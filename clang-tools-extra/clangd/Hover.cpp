//===--- Hover.cpp - Information about code at the cursor location --------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "Hover.h"

#include "AST.h"
#include "CodeCompletionStrings.h"
#include "Config.h"
#include "FindTarget.h"
#include "Headers.h"
#include "IncludeCleaner.h"
#include "ParsedAST.h"
#include "Selection.h"
#include "SourceCode.h"
#include "clang-include-cleaner/Analysis.h"
#include "clang-include-cleaner/IncludeSpeller.h"
#include "clang-include-cleaner/Types.h"
#include "index/SymbolCollector.h"
#include "support/Markup.h"
#include "support/Trace.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTDiagnostic.h"
#include "clang/AST/ASTTypeTraits.h"
#include "clang/AST/Attr.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclBase.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclObjC.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/OperationKinds.h"
#include "clang/AST/PrettyPrinter.h"
#include "clang/AST/RecordLayout.h"
#include "clang/AST/Type.h"
#include "clang/AST/TypeOrdering.h"
#include "clang/Basic/CharInfo.h"
#include "clang/Basic/LLVM.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/Specifiers.h"
#include "clang/Basic/TokenKinds.h"
#include "clang/Index/IndexSymbol.h"
#include "clang/Tooling/Syntax/Tokens.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/ScopedPrinter.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <optional>
#include <string>
#include <vector>

namespace clang {
namespace clangd {
namespace {

class TypeSimplifier {
  ParsedAST &AST;
  struct LocalAlias {
    QualType Pretty;

    QualType getPretty() const { return Pretty; }
    QualType getUgly() const { return Pretty.getCanonicalType(); }
  };
  llvm::SmallVector<LocalAlias, 1> LocalAliases;

public:
  explicit TypeSimplifier(ParsedAST &AST) : AST(AST) {}

  QualType simplify(QualType T) const {
    auto Pretty = simplifyImpl(T);
    if (!Pretty)
      return T;
    return *Pretty;
  }

  bool pushLocalTypeAlias(QualType Pretty) {
    if (Pretty->isTypedefNameType()) {
      LocalAliases.emplace_back(LocalAlias{Pretty});
      return true;
    }
    return false;
  }
  void popLocalTypeAlias(size_t Num = 1) {
    if (Num)
      LocalAliases.pop_back_n(std::min(Num, LocalAliases.size()));
  }

  std::optional<QualType> simplifyPartially(QualType Current) const {
    const Type *Ty = Current.getTypePtr();
    ASTContext &Ctx = AST.getASTContext();
    QualType Next;
    switch (Ty->getTypeClass()) {
    case Type::TypeClass::Pointer:
      if (auto Pointee =
              simplifyImpl(cast<PointerType>(Ty)->getPointeeType(), true))
        return Ctx.getPointerType(*Pointee);
      return std::nullopt;
    case Type::TypeClass::RValueReference:
      if (auto Pointee = simplifyImpl(
              cast<RValueReferenceType>(Ty)->getPointeeType(), true))
        return Ctx.getRValueReferenceType(*Pointee);
      return std::nullopt;
    case Type::TypeClass::LValueReference:
      if (auto Pointee = simplifyImpl(
              cast<LValueReferenceType>(Ty)->getPointeeType(), true))
        return Ctx.getLValueReferenceType(*Pointee);
      return std::nullopt;
    case Type::TypeClass::Elaborated: {
      const auto *ET = cast<ElaboratedType>(Ty);
      auto *Spec = ET->getQualifier();
      if (Spec && Spec->getAsType()) {
        if (auto PrettySpec =
                simplifyImpl(QualType{Spec->getAsType(), 0}, true)) {
          Spec = NestedNameSpecifier::Create(Ctx, Spec->getPrefix(),
                                             PrettySpec->getTypePtr());
        }
      }
      if (auto Pretty = simplifyImpl(ET->getNamedType(), true))
        return Ctx.getElaboratedType(ET->getKeyword(), Spec, *Pretty);
      return std::nullopt;
    }
    case Type::TypeClass::TemplateSpecialization: {
      const auto *TST = cast<TemplateSpecializationType>(Ty);
      TemplateName Template = TST->getTemplateName();
      ArrayRef<TemplateArgument> Args = TST->template_arguments();
      bool Changed = false;
      llvm::SmallVector<TemplateArgument, 4> NewArgs;
      NewArgs.reserve(Args.size());
      for (const TemplateArgument &Arg : Args) {
        if (Arg.getKind() == TemplateArgument::Type) {
          if (auto Pretty = simplifyImpl(Arg.getAsType(), true)) {
            Changed = true;
            NewArgs.push_back(TemplateArgument(
                *Pretty, Arg.getKind() == TemplateArgument::Null,
                Arg.getIsDefaulted()));
            continue;
          }
        }
        NewArgs.push_back(Arg);
      }
      if (Changed)
        return Ctx.getTemplateSpecializationType(Template, NewArgs, {});
      return std::nullopt;
    }
    default:
      return std::nullopt;
    }
  }

private:
  std::optional<QualType>
  simplifyImpl(QualType T, bool UseLocalAliasAsFallback = false) const {
    if (!isUgly(T)) {
      if (UseLocalAliasAsFallback)
        return findPrettyAliasFromMap(T, true);
      return std::nullopt;
    }
    std::optional<QualType> Pretty = findPrettyDesugared(T);
    if (Pretty)
      return Pretty;
    Pretty = findPrettyAliasFromMap(T);
    if (Pretty)
      return Pretty;
    Pretty = simplifyPartially(T);
    return Pretty;
  }

  bool isUgly(QualType T) const { return isUglyImpl(T); }

  bool isUglyImpl(QualType T, bool IgnoreDeclContext = false) const {
    const Type *Ty = T.getTypePtr();
    NamedDecl *D = nullptr;
    switch (Ty->getTypeClass()) {
    case Type::TypeClass::Builtin:
    case Type::TypeClass::MemberPointer:
    default:
      return false;
    case Type::TypeClass::Pointer:
    case Type::TypeClass::RValueReference:
    case Type::TypeClass::LValueReference:
      return isUglyImpl(Ty->getPointeeType());
    case Type::TypeClass::InjectedClassName:
    case Type::TypeClass::TemplateSpecialization:
    case Type::TypeClass::DeducedTemplateSpecialization:
    case Type::TypeClass::DependentTemplateSpecialization:
      return true;
    case Type::TypeClass::SubstTemplateTypeParm: {
      const auto *STTP = cast<SubstTemplateTypeParmType>(Ty);
      return isUglyImpl(STTP->getReplacementType());
    }
    case Type::TypeClass::UnaryTransform:
      return cast<UnaryTransformType>(Ty)->isSugared();
    case Type::TypeClass::Decltype:
      return cast<DecltypeType>(Ty)->isSugared();
    case Type::TypeClass::TypeOfExpr:
    case Type::TypeClass::TypeOf:
      return true;
    case Type::TypeClass::Record: {
      const auto *RT = cast<RecordType>(Ty);
      D = RT->getDecl();
      if (isa<ClassTemplateSpecializationDecl>(D))
        return true;
      break;
    }
    case Type::TypeClass::Elaborated: {
      const auto *ET = cast<ElaboratedType>(Ty);
      if (NestedNameSpecifier *NameSpecifier = ET->getQualifier()) {
        if (const Type *SpecifierType = NameSpecifier->getAsType()) {
          return isUglyImpl({SpecifierType, 0}) ||
                 isUglyImpl(ET->getNamedType(), true);
        }
      }
      return isUglyImpl(ET->getNamedType());
    }
    case Type::TypeClass::Typedef: {
      const auto *TDT = cast<TypedefType>(Ty);
      D = TDT->getDecl();
      break;
    }
    }
    if (isPreserveIdentifierOrNull(D))
      return true;

    if (IgnoreDeclContext)
      return false;

    DeclContext *DeclCtx = D->getDeclContext();
    if (!DeclCtx)
      return false;
    if (auto *RD = dyn_cast<RecordDecl>(DeclCtx))
      return isUglyImpl({RD->getTypeForDecl(), 0});
    if (auto *RD = dyn_cast<NamespaceDecl>(DeclCtx)) {
      while (RD) {
        if (isPreserveIdentifierOrNull(RD))
          return true;
        RD = dyn_cast<NamespaceDecl>(RD->getParent());
      }
    }
    return false;
  }

  static bool isPreserveIdentifierOrNull(NamedDecl *Decl) {
    IdentifierInfo *Id = Decl->getIdentifier();
    if (!Id)
      return true;
    StringRef Name = Id->getName();
    return Name.starts_with("__") ||
           (Name.size() > 1 && Name.starts_with('_') && llvm::isUpper(Name[1]));
  }

  std::optional<QualType> findPrettyDesugared(QualType Current,
                                              int Depth = 0) const {
    const int MaxDepth = 15;
    if (Depth > MaxDepth)
      return std::nullopt;
    const Type *Ty = Current.getTypePtr();
    ASTContext &Ctx = AST.getASTContext();
    QualType Next;
    switch (Ty->getTypeClass()) {
    case Type::TypeClass::Pointer:
    case Type::TypeClass::RValueReference:
    case Type::TypeClass::LValueReference:
      return simplifyPartially(Current);
    case Type::TypeClass::TemplateSpecialization: {
      const auto *TST = cast<TemplateSpecializationType>(Ty);
      if (!TST->isTypeAlias())
        return std::nullopt;
      Next = TST->getAliasedType();
      if (Next == Current)
        return std::nullopt;
      break;
    }
    case Type::TypeClass::UnaryTransform:
      Next = cast<UnaryTransformType>(Ty)->getUnderlyingType();
      break;
    case Type::TypeClass::Decltype:
      Next = cast<DecltypeType>(Ty)->getUnderlyingType();
      break;
    case Type::TypeClass::TypeOfExpr:
      Next = cast<TypeOfExprType>(Ty)->getUnderlyingExpr()->getType();
      break;
    case Type::TypeClass::TypeOf:
      Next = cast<TypeOfType>(Ty)->desugar();
      break;
    case Type::TypeClass::SubstTemplateTypeParm:
      Next = cast<SubstTemplateTypeParmType>(Ty)->getReplacementType();
      break;
    case Type::TypeClass::Elaborated:
      Next = cast<ElaboratedType>(Ty)->getNamedType();
      break;
    case Type::TypeClass::Typedef:
      Next = cast<TypedefType>(Ty)->desugar();
      break;
    default:
      Next = Current.getSingleStepDesugaredType(Ctx);
      if (Next == Current)
        return std::nullopt;
      break;
    }
    if (auto LocalPrettified = findPrettyAliasFromMap(Next, true))
      return LocalPrettified;
    if (!isUgly(Next))
      return Next;

    return findPrettyDesugared(Next);
  }

  std::optional<QualType> findLocalAlias(QualType T) const {
    auto Found = llvm::find_if(LocalAliases, [T](const LocalAlias &Alias) {
      return Alias.getUgly() == T;
    });
    if (Found != LocalAliases.end()) {
      return Found->getPretty();
    }
    return std::nullopt;
  }

  std::optional<QualType>
  findPrettyAliasFromMap(QualType T, bool UseLocalAlias = false) const {
    if (UseLocalAlias) {
      if (auto Pretty = findLocalAlias(T)) {
        return Pretty;
      }
    } else {
      // 暂时只找一阶别名
      T = T.getCanonicalType();
      auto Found = AST.getTypeAliasMap().Map.find(T);
      if (Found != AST.getTypeAliasMap().Map.end()) {
        auto &AliasList = Found->second;
        for (int i = AliasList.size() - 1; i >= 0; i--) {
          QualType QT = AST.getASTContext().getTypedefType(AliasList[i]);
          if (!isUgly(QT))
            return QT;
        }
      }
    }

    const Type *Ty = T.getTypePtr();
    ASTContext &Ctx = AST.getASTContext();
    switch (Ty->getTypeClass()) {
    case Type::TypeClass::Pointer:
      if (auto Pointee = findPrettyAliasFromMap(
              cast<PointerType>(Ty)->getPointeeType(), UseLocalAlias))
        return Ctx.getPointerType(*Pointee);
      break;
    case Type::TypeClass::RValueReference:
      if (auto Pointee = findPrettyAliasFromMap(
              cast<RValueReferenceType>(Ty)->getPointeeType(), UseLocalAlias))
        return Ctx.getRValueReferenceType(*Pointee);
      break;
    case Type::TypeClass::LValueReference:
      if (auto Pointee = findPrettyAliasFromMap(
              cast<LValueReferenceType>(Ty)->getPointeeType(), UseLocalAlias))
        return Ctx.getLValueReferenceType(*Pointee);
      break;
    case Type::TypeClass::SubstTemplateTypeParm: {
      auto STTPT = cast<SubstTemplateTypeParmType>(Ty);
      if (auto Subst = findPrettyAliasFromMap(STTPT->getReplacementType(),
                                              UseLocalAlias))
        return Ctx.getSubstTemplateTypeParmType(
            *Subst, STTPT->getAssociatedDecl(), STTPT->getIndex(),
            STTPT->getPackIndex(), STTPT->getFinal());
      break;
    }
    default:
      break;
    }
    auto Quals = T.getLocalFastQualifiers();
    if (Quals == 0)
      return std::nullopt;
    if (auto NonQualType = findPrettyAliasFromMap(QualType{T.getTypePtr(), 0},
                                                  UseLocalAlias)) {
      return QualType{NonQualType->getTypePtr(), Quals};
    }
    return std::nullopt;
  }
};

void fillFunctionTypeAndParams(HoverInfo &HI, const Decl *D,
                               const FunctionDecl *FD, const PrintingPolicy &PP,
                               TypeSimplifier &Simplifier);

// print as "(lambda [](Params...) -> ReturnType/auto)"
void printPrettyLambdaType(
    llvm::raw_ostream &OS,
    const std::optional<std::vector<HoverInfo::Param>> &Parameters,
    const std::optional<clang::clangd::HoverInfo::PrintedType> &ReturnType) {
  OS << "(lambda [](";
  if (Parameters) {
    llvm::ListSeparator LS;
    for (const auto &P : *Parameters)
      OS << LS << P;
  }
  OS << ") -> ";
  if (ReturnType)
    OS << ReturnType->Type << ")";
  else
    OS << "auto)";
}

void printSingleTemplateArgument(const TemplateArgument &P,
                                 llvm::raw_ostream &OS,
                                 const PrintingPolicy &Policy, bool IncludeType,
                                 TypeSimplifier &Simplifier) {
  if (P.getKind() == TemplateArgument::Type) {
    PrintingPolicy SubPolicy(Policy);
    SubPolicy.SuppressStrongLifetime = true;
    Simplifier.simplify(P.getAsType()).print(OS, SubPolicy);
  } else
    P.print(Policy, OS, IncludeType);
}

void printPrettyTemplateArgumentList(llvm::raw_ostream &OS,
                                     llvm::ArrayRef<TemplateArgument> Args,
                                     const PrintingPolicy &Policy,
                                     const TemplateParameterList *TPL,
                                     TypeSimplifier &Simplifier) {
  // Don't print <> for an empty list.
  if (Args.empty())
    return;
  OS << "<";
  llvm::ListSeparator LS;
  for (size_t I = 0; I < Args.size(); ++I) {
    const TemplateArgument &Arg = Args[I];
    if (Arg.getKind() == TemplateArgument::Pack) {
      for (const auto &P : Arg.getPackAsArray()) {
        OS << LS;
        printSingleTemplateArgument(P, OS, Policy, false, Simplifier);
      }
      continue;
    }
    OS << LS;
    if (Arg.getKind() == TemplateArgument::Type) {
      if (const auto *RD = Arg.getAsType()->getAsCXXRecordDecl();
          RD && RD->isLambda()) {
        HoverInfo LambdaHI;
        fillFunctionTypeAndParams(LambdaHI, RD, RD->getLambdaCallOperator(),
                                  Policy, Simplifier);
        printPrettyLambdaType(OS, LambdaHI.Parameters, LambdaHI.ReturnType);
        continue;
      }
    }
    bool inlcudeType =
        TPL ? TemplateParameterList::shouldIncludeTypeForArgument(Policy, TPL,
                                                                  I)
            : false;
    printSingleTemplateArgument(Arg, OS, Policy, inlcudeType, Simplifier);
  }
  OS << ">";
}

std::string printExpr(const Expr *E, const PrintingPolicy &PP) {
  std::string S;
  llvm::raw_string_ostream OS(S);
  E->printPretty(OS, nullptr, PP);
  return S;
}

PrintingPolicy getPrintingPolicy(PrintingPolicy Base) {
  Base.SuppressScope = false;
  Base.PolishForDeclaration = true;
  Base.PrintAsCanonical = false;
  Base.SuppressUnwrittenScope = false;
  Base.FullyQualifiedName = true;
  Base.TerseOutput = true;
  Base.SuppressInlineNamespace = PrintingPolicy::None;
  Base.SuppressElaboration = false;
  Base.AnonymousTagLocations = false;
  return Base;
}

/// Given a declaration \p D, return a human-readable string representing the
/// local scope in which it is declared, i.e. class(es) and method name. Returns
/// an empty string if it is not local.
std::string getLocalScope(const Decl *D, const PrintingPolicy &PP) {
  std::vector<std::string> Scopes;
  const DeclContext *DC = D->getDeclContext();

  // ObjC scopes won't have multiple components for us to join, instead:
  // - Methods: "-[Class methodParam1:methodParam2]"
  // - Classes, categories, and protocols: "MyClass(Category)"
  if (const ObjCMethodDecl *MD = dyn_cast<ObjCMethodDecl>(DC))
    return printObjCMethod(*MD);
  if (const ObjCContainerDecl *CD = dyn_cast<ObjCContainerDecl>(DC))
    return printObjCContainer(*CD);

  auto GetName = [](const TypeDecl *D, const PrintingPolicy &PP) {
    if (!D->getDeclName().isEmpty())
      return declaredType(D).getAsString(PP);
    if (auto *RD = dyn_cast<RecordDecl>(D))
      return ("(anonymous " + RD->getKindName() + ")").str();
    return std::string("");
  };
  PrintingPolicy Policy = PP;
  Policy.SuppressScope = true;
  while (DC) {
    if (const TypeDecl *TD = dyn_cast<TypeDecl>(DC))
      Scopes.push_back(GetName(TD, Policy));
    else if (const FunctionDecl *FD = dyn_cast<FunctionDecl>(DC))
      Scopes.push_back(FD->getNameAsString());
    DC = DC->getParent();
  }

  return llvm::join(llvm::reverse(Scopes), "::");
}

// Forward declarations for the recursive pretty-printer.
void printAPValueRecursive(llvm::raw_ostream &OS, const APValue &Val,
                           QualType T, const ASTContext &Ctx, bool Pretty,
                           unsigned Indent);
std::optional<std::string> formatAPValue(const APValue &Val, QualType T,
                                         const ASTContext &Ctx,
                                         unsigned Indent);

std::optional<std::string> printLValue(const APValue &Val,
                                       const ASTContext &Ctx) {
  const Expr *BaseExpr = Val.getLValueBase().dyn_cast<const Expr *>();
  const StringLiteral *SL = nullptr;
  if (const auto *PE = dyn_cast_or_null<PredefinedExpr>(BaseExpr))
    SL = PE->getFunctionName();
  else
    SL = dyn_cast_or_null<StringLiteral>(BaseExpr);

  if (SL) {
    CharUnits Offset = Val.getLValueOffset();
    if (Offset.getQuantity() >= SL->getByteLength())
      return "\"out-of-bounds\"";
    std::string Result;
    llvm::raw_string_ostream OS(Result);
    OS << '"';
    OS.write_escaped(SL->getString().substr(Offset.getQuantity()),
                     /*UseHexEscapes*/ true);
    OS << '"';
    return Result;
  }
  return std::nullopt;
}

void printStructRecursive(llvm::raw_ostream &OS, const APValue &Val, QualType T,
                          const ASTContext &Ctx, bool Pretty, unsigned Indent) {
  const RecordDecl *RD = T->getAsRecordDecl();
  if (!RD || (!RD->isClass() && !RD->isStruct())) {
    OS << Val.getAsString(Ctx, T);
    return;
  }

  OS << "{";
  if (Pretty) {
    OS << "\n";
    Indent += 4;
  }

  bool First = true;
  for (const FieldDecl *FD : RD->fields()) {
    if (FD->isUnnamedBitField())
      continue;
    if (!First)
      OS << (Pretty ? ",\n" : ", ");
    First = false;

    if (Pretty)
      OS.indent(Indent);

    OS << "." << FD->getNameAsString() << " = ";
    const APValue &MemberVal = Val.getStructField(FD->getFieldIndex());
    if (Pretty)
      OS << formatAPValue(MemberVal, FD->getType(), Ctx, Indent).value_or("?");
    else
      printAPValueRecursive(OS, MemberVal, FD->getType(), Ctx,
                            /*Pretty=*/false, Indent);
  }

  if (Pretty) {
    if (!First)
      OS << "\n";
    OS.indent(Indent - 4);
  }
  OS << "}";
}

// Heuristic: is the element simple enough to be part of a wrapped line?
bool isSimpleForLineWrapping(const APValue &Val) {
  return !Val.isStruct() && !Val.isArray();
}

bool printString(llvm::raw_ostream &OS, const APValue &Val,
                 bool printableASCIIOnly = false) {
  // Try to print char arrays as string literals.
  if (Val.getArrayInitializedElts() > 128)
    return false;
  std::string Str;
  for (unsigned I = 0; I < Val.getArrayInitializedElts(); ++I) {
    const APValue &Elt = Val.getArrayInitializedElt(I);
    if (!Elt.isInt())
      return false;

    llvm::APSInt CharVal = Elt.getInt();
    auto V = CharVal.getExtValue();
    if (printableASCIIOnly && !isprint(V) && V != '\n' && V != '\r' &&
        V != '\t' && V != '\v' && V != '\f')
      return false;
    Str += static_cast<char>(V);
  }
  if (Str.back() == '\0')
    Str.pop_back();
  if (Val.getArrayInitializedElts() > 0) {
    OS << '"';
    OS.write_escaped(Str, /*UseHexEscapes*/ true);
    OS << '"';
    return true;
  }
  return false;
}

static void printArrayRecursive(llvm::raw_ostream &OS, const APValue &Val,
                                QualType T, const ASTContext &Ctx, bool Pretty,
                                unsigned Indent) {
  if (!Val.getArrayInitializedElts() && !Val.hasArrayFiller()) {
    OS << "{}";
    return;
  }

  QualType ElemT = T->getAsArrayTypeUnsafe()->getElementType();

  if (ElemT->isCharType() || ElemT->isChar8Type()) {
    if (printString(OS, Val))
      return;
  }

  OS << "{";

  if (Pretty) {
    bool AllSimple = true;
    if (Val.getArrayInitializedElts() > 0)
      AllSimple = isSimpleForLineWrapping(Val.getArrayInitializedElt(0));

    OS << "\n";
    unsigned CurrentIndent = Indent + 4;

    if (AllSimple) { // Line-wrapping mode for simple elements.
      OS.indent(CurrentIndent);
      unsigned LinePos = CurrentIndent;
      const unsigned LineLimit = 80;

      for (unsigned i = 0; i < Val.getArrayInitializedElts(); ++i) {
        if (i > 0) {
          OS << ", ";
          LinePos += 4;
        }
        std::string EltStr = formatAPValue(Val.getArrayInitializedElt(i), ElemT,
                                           Ctx, CurrentIndent)
                                 .value_or("?");
        if (LinePos + EltStr.length() > LineLimit && i > 0) {
          OS << "\n";
          OS.indent(CurrentIndent);
          LinePos = CurrentIndent;
        }
        OS << EltStr;
        LinePos += EltStr.length();
      }

      if (Val.hasArrayFiller()) {
        const char *FillerStr = "...";
        if (Val.getArrayInitializedElts() > 0) {
          if (LinePos + strlen(FillerStr) + 2 > LineLimit) {
            OS << ",\n";
            OS.indent(CurrentIndent);
          } else {
            OS << ", ";
          }
        }
        OS << FillerStr;
      }
    } else { // One-element-per-line mode for complex elements.
      bool First = true;
      for (unsigned i = 0; i < Val.getArrayInitializedElts(); ++i) {
        if (!First)
          OS << ",\n";
        First = false;
        OS.indent(CurrentIndent);
        OS << formatAPValue(Val.getArrayInitializedElt(i), ElemT, Ctx,
                            CurrentIndent)
                  .value_or("?");
      }
      if (Val.hasArrayFiller()) {
        if (!First)
          OS << ",\n";
        OS.indent(CurrentIndent);
        OS << "...";
      }
    }

    OS << "\n";
    OS.indent(Indent);
  } else {
    bool First = true;
    for (unsigned i = 0; i < Val.getArrayInitializedElts(); ++i) {
      if (!First)
        OS << ", ";
      First = false;
      printAPValueRecursive(OS, Val.getArrayInitializedElt(i), ElemT, Ctx,
                            /*Pretty=*/false, Indent);
    }
    if (Val.hasArrayFiller()) {
      if (!First)
        OS << ", ";
      OS << "...";
    }
  }

  OS << "}";
}

void printAPValueRecursive(llvm::raw_ostream &OS, const APValue &Val,
                           QualType T, const ASTContext &Ctx, bool Pretty,
                           unsigned Indent) {
  if (Val.isLValue())
    if (auto S = printLValue(Val, Ctx)) {
      OS << *S;
      return;
    }
  if (Val.isStruct())
    return printStructRecursive(OS, Val, T, Ctx, Pretty, Indent);
  if (Val.isArray())
    return printArrayRecursive(OS, Val, T, Ctx, Pretty, Indent);
  OS << Val.getAsString(Ctx, T);
}

std::optional<std::string> formatAPValue(const APValue &Val, QualType T,
                                         const ASTContext &Ctx,
                                         unsigned Indent = 0) {
  if (Val.isLValue())
    return printLValue(Val, Ctx);

  std::string Compact;
  llvm::raw_string_ostream CompactOS(Compact);
  printAPValueRecursive(CompactOS, Val, T, Ctx, /*Pretty=*/false, Indent);
  CompactOS.flush();

  if (Compact.length() <= 80 && Compact.find('\n') == std::string::npos)
    return Compact;

  std::string Pretty;
  llvm::raw_string_ostream PrettyOS(Pretty);
  printAPValueRecursive(PrettyOS, Val, T, Ctx, /*Pretty=*/true, Indent);
  PrettyOS.flush();
  return Pretty;
}

/// A map from doxygen command to its presentation name.
const llvm::StringMap<const char *> DoxygenCommandToText = {
    {"sa", "See also"},
    {"see", "See also"},
    {"since", "Since"},
    {"author", "Author"},
    {"authors", "Authors"},
    {"bug", "Bug"},
    {"warning", "Warning"},
    {"todo", "Todo"},
    {"deprecated", "Deprecated"},
    {"pre", "Pre-condition"},
    {"post", "Post-condition"},
    {"return", "Returns"},
    {"returns", "Returns"},
    {"param", "Parameter"},
    {"tparam", "Template parameter"},
    {"brief", "Brief"},
};

// Commands that should be grouped together in the hover.
const llvm::StringMap<const char *> DoxygenGroupedCommands = {
    {"param", "Parameters"},
    {"tparam", "Template Parameters"},
};

/// Returns the human-readable representation for namespace containing the
/// declaration \p D. Returns empty if it is contained global namespace.
std::string getNamespaceScope(const Decl *D, const PrintingPolicy &PP) {
  const DeclContext *DC = D->getDeclContext();

  // ObjC does not have the concept of namespaces, so instead we support
  // local scopes.
  if (isa<ObjCMethodDecl, ObjCContainerDecl>(DC))
    return "";

  if (const TagDecl *TD = dyn_cast<TagDecl>(DC))
    return getNamespaceScope(TD, PP);
  if (const FunctionDecl *FD = dyn_cast<FunctionDecl>(DC))
    return getNamespaceScope(FD, PP);
  if (const NamespaceDecl *NSD = dyn_cast<NamespaceDecl>(DC)) {
    // Skip inline/anon namespaces.
    // We want to show inline namespaces, so only skip anonymous ones.
    if (NSD->isAnonymousNamespace())
      return getNamespaceScope(NSD, PP);
  }
  if (const NamedDecl *ND = dyn_cast<NamedDecl>(DC)) {
    std::string QName;
    llvm::raw_string_ostream OS(QName);
    ND->printQualifiedName(OS, PP);
    return QName;
  }

  return "";
}

std::string printDefinition(const Decl *D, PrintingPolicy PP,
                            const syntax::TokenBuffer &TB) {
  if (auto *VD = llvm::dyn_cast<VarDecl>(D)) {
    if (auto *IE = VD->getInit()) {
      // Initializers might be huge and result in lots of memory allocations in
      // some catostrophic cases. Such long lists are not useful in hover cards
      // anyway.
      if (200 < TB.expandedTokens(IE->getSourceRange()).size())
        PP.SuppressInitializers = true;
    }
  }
  std::string Definition;
  llvm::raw_string_ostream OS(Definition);
  if (const auto *FD = llvm::dyn_cast<FunctionDecl>(D)) {
    FD->print(OS, PP, 0, true);
  } else {
    D->print(OS, PP);
  }
  return Definition;
}

const char *getMarkdownLanguage(const ASTContext &Ctx) {
  const auto &LangOpts = Ctx.getLangOpts();
  if (LangOpts.ObjC && LangOpts.CPlusPlus)
    return "objective-cpp";
  return LangOpts.ObjC ? "objective-c" : "cpp";
}

HoverInfo::PrintedType printType(QualType QT, ASTContext &ASTCtx,
                                 const PrintingPolicy &PP,
                                 llvm::StringRef Placeholder = "") {
  // TypePrinter doesn't resolve decltypes, so resolve them here.
  // FIXME: This doesn't handle composite types that contain a decltype in them.
  // We should rather have a printing policy for that.
  while (!QT.isNull() && QT->isDecltypeType())
    QT = QT->castAs<DecltypeType>()->getUnderlyingType();
  HoverInfo::PrintedType Result;
  llvm::raw_string_ostream OS(Result.Type);
  // Special case: if the outer type is a tag type without qualifiers, then
  // include the tag for extra clarity.
  // This isn't very idiomatic, so don't attempt it for complex cases, including
  // pointers/references, template specializations, etc.
  if (!QT.isNull() && !QT.hasQualifiers() && PP.SuppressTagKeyword) {
    if (auto *TT = llvm::dyn_cast<TagType>(QT.getTypePtr()))
      OS << TT->getDecl()->getKindName() << " ";
  }
  QT.print(OS, PP, Placeholder);

  const Config &Cfg = Config::current();
  if (!QT.isNull() && Cfg.Hover.ShowAKA) {
    bool ShouldAKA = false;
    QualType DesugaredTy = clang::desugarForDiagnostic(ASTCtx, QT, ShouldAKA);
    if (ShouldAKA)
      Result.AKA = DesugaredTy.getAsString(PP);
  }
  return Result;
}

HoverInfo::PrintedType printType(const TemplateTypeParmDecl *TTP) {
  HoverInfo::PrintedType Result;
  Result.Type = TTP->wasDeclaredWithTypename() ? "typename" : "class";
  if (TTP->isParameterPack())
    Result.Type += "...";
  return Result;
}

HoverInfo::PrintedType printType(const NonTypeTemplateParmDecl *NTTP,
                                 const PrintingPolicy &PP,
                                 TypeSimplifier &Simplifier) {
  auto PrintedType = printType(Simplifier.simplify(NTTP->getType()),
                               NTTP->getASTContext(), PP);
  if (NTTP->isParameterPack()) {
    PrintedType.Type.append("...");
    if (PrintedType.AKA)
      PrintedType.AKA->append("...");
  }
  if (const IdentifierInfo *II = NTTP->getIdentifier())
    PrintedType.Type.append(" ").append(II->getName());
  return PrintedType;
}

HoverInfo::PrintedType printType(const TemplateTemplateParmDecl *TTP,
                                 const PrintingPolicy &PP,
                                 TypeSimplifier &Simplifier) {
  HoverInfo::PrintedType Result;
  llvm::raw_string_ostream OS(Result.Type);
  OS << "template <";
  llvm::StringRef Sep = "";
  for (const Decl *Param : *TTP->getTemplateParameters()) {
    OS << Sep;
    Sep = ", ";
    if (const auto *TTP = dyn_cast<TemplateTypeParmDecl>(Param))
      OS << printType(TTP).Type;
    else if (const auto *NTTP = dyn_cast<NonTypeTemplateParmDecl>(Param))
      OS << printType(NTTP, PP, Simplifier).Type;
    else if (const auto *TTPD = dyn_cast<TemplateTemplateParmDecl>(Param))
      OS << printType(TTPD, PP, Simplifier).Type;
  }
  // FIXME: TemplateTemplateParameter doesn't store the info on whether this
  // param was a "typename" or "class".
  OS << "> class";
  return Result;
}

std::vector<HoverInfo::Param>
fetchTemplateParameters(const TemplateParameterList *Params,
                        const PrintingPolicy &PP, TypeSimplifier &Simplifier) {
  assert(Params);
  std::vector<HoverInfo::Param> TempParameters;

  for (const Decl *Param : *Params) {
    HoverInfo::Param P;
    if (const auto *TTPD = dyn_cast<TemplateTypeParmDecl>(Param)) {
      P.Type = printType(TTPD);
      if (IdentifierInfo *II = TTPD->getIdentifier())
        P.Type->Type += " " + II->getName().str();
      if (TTPD->hasDefaultArgument()) {
        P.Default.emplace();
        llvm::raw_string_ostream Out(*P.Default);
        TTPD->getDefaultArgument().getArgument().print(PP, Out,
                                                       /*IncludeType=*/false);
      }
    } else if (const auto *NTTP = dyn_cast<NonTypeTemplateParmDecl>(Param)) {
      P.Type = printType(NTTP, PP, Simplifier);
      if (NTTP->hasDefaultArgument()) {
        P.Default.emplace();
        llvm::raw_string_ostream Out(*P.Default);
        NTTP->getDefaultArgument().getArgument().print(PP, Out,
                                                       /*IncludeType=*/false);
      }
    } else if (const auto *TTPD = dyn_cast<TemplateTemplateParmDecl>(Param)) {
      P.Type = printType(TTPD, PP, Simplifier);
      if (IdentifierInfo *II = TTPD->getIdentifier())
        P.Type->Type += " " + II->getName().str();
      if (TTPD->hasDefaultArgument()) {
        P.Default.emplace();
        llvm::raw_string_ostream Out(*P.Default);
        TTPD->getDefaultArgument().getArgument().print(PP, Out,
                                                       /*IncludeType*/ false);
      }
    }
    TempParameters.push_back(std::move(P));
  }

  return TempParameters;
}

const FunctionDecl *getUnderlyingFunction(const Decl *D) {
  // Extract lambda from variables.
  if (const VarDecl *VD = llvm::dyn_cast<VarDecl>(D)) {
    auto QT = VD->getType();
    if (!QT.isNull()) {
      while (!QT->getPointeeType().isNull())
        QT = QT->getPointeeType();

      if (const auto *CD = QT->getAsCXXRecordDecl())
        return CD->getLambdaCallOperator();
    }
  }

  // Non-lambda functions.
  return D->getAsFunction();
}

// Returns the decl that should be used for querying comments, either from index
// or AST.
const NamedDecl *getDeclForComment(const NamedDecl *D) {
  const NamedDecl *DeclForComment = D;
  if (const auto *TSD = llvm::dyn_cast<ClassTemplateSpecializationDecl>(D)) {
    // Template may not be instantiated e.g. if the type didn't need to be
    // complete; fallback to primary template.
    if (TSD->getTemplateSpecializationKind() == TSK_Undeclared)
      DeclForComment = TSD->getSpecializedTemplate();
    else if (const auto *TIP = TSD->getTemplateInstantiationPattern())
      DeclForComment = TIP;
  } else if (const auto *TSD =
                 llvm::dyn_cast<VarTemplateSpecializationDecl>(D)) {
    if (TSD->getTemplateSpecializationKind() == TSK_Undeclared)
      DeclForComment = TSD->getSpecializedTemplate();
    else if (const auto *TIP = TSD->getTemplateInstantiationPattern())
      DeclForComment = TIP;
  } else if (const auto *FD = D->getAsFunction())
    if (const auto *TIP = FD->getTemplateInstantiationPattern())
      DeclForComment = TIP;
  // Ensure that getDeclForComment(getDeclForComment(X)) = getDeclForComment(X).
  // This is usually not needed, but in strange cases of comparision operators
  // being instantiated from spasceship operater, which itself is a template
  // instantiation the recursrive call is necessary.
  if (D != DeclForComment)
    DeclForComment = getDeclForComment(DeclForComment);
  return DeclForComment;
}

// Look up information about D from the index, and add it to Hover.
void enhanceFromIndex(HoverInfo &Hover, const NamedDecl &ND,
                      const SymbolIndex *Index) {
  assert(&ND == getDeclForComment(&ND));
  // We only add documentation, so don't bother if we already have some.
  if (!Hover.Documentation.empty() || !Index)
    return;

  // Skip querying for non-indexable symbols, there's no point.
  // We're searching for symbols that might be indexed outside this main file.
  if (!SymbolCollector::shouldCollectSymbol(ND, ND.getASTContext(),
                                            SymbolCollector::Options(),
                                            /*IsMainFileOnly=*/false))
    return;
  auto ID = getSymbolID(&ND);
  if (!ID)
    return;
  LookupRequest Req;
  Req.IDs.insert(ID);
  Index->lookup(Req, [&](const Symbol &S) {
    Hover.Documentation = std::string(S.Documentation);
  });
}

// Default argument might exist but be unavailable, in the case of unparsed
// arguments for example. This function returns the default argument if it is
// available.
const Expr *getDefaultArg(const ParmVarDecl *PVD) {
  // Default argument can be unparsed or uninstantiated. For the former we
  // can't do much, as token information is only stored in Sema and not
  // attached to the AST node. For the latter though, it is safe to proceed as
  // the expression is still valid.
  if (!PVD->hasDefaultArg() || PVD->hasUnparsedDefaultArg())
    return nullptr;
  return PVD->hasUninstantiatedDefaultArg() ? PVD->getUninstantiatedDefaultArg()
                                            : PVD->getDefaultArg();
}

HoverInfo::Param toHoverInfoParam(const ParmVarDecl *PVD,
                                  const PrintingPolicy &PP,
                                  TypeSimplifier &Simplifier) {
  HoverInfo::Param Out;
  if (PVD->isParameterPack()) {
    QualType Pattern = PVD->getType();
    if (const auto *PET = Pattern->getAs<PackExpansionType>())
      Pattern = PET->getPattern();

    std::string Placeholder = "...";
    if (PVD->getIdentifier())
      Placeholder.append(PVD->getNameAsString());
    Out.Type = printType(Pattern, PVD->getASTContext(), PP, Placeholder);
  } else {
    Out.Type = printType(Simplifier.simplify(PVD->getType()),
                         PVD->getASTContext(), PP, PVD->getName());
  }
  if (const Expr *DefArg = getDefaultArg(PVD)) {
    Out.Default.emplace();
    llvm::raw_string_ostream OS(*Out.Default);
    DefArg->printPretty(OS, nullptr, PP);
  }
  return Out;
}

// Populates Type, ReturnType, and Parameters for function-like decls.
void fillFunctionTypeAndParams(HoverInfo &HI, const Decl *D,
                               const FunctionDecl *FD, const PrintingPolicy &PP,
                               TypeSimplifier &Simplifier) {
  HI.Parameters.emplace();
  FD->getDeclContext();
  for (const ParmVarDecl *PVD : FD->parameters())
    HI.Parameters->emplace_back(toHoverInfoParam(PVD, PP, Simplifier));
  if (FD->isVariadic()) {
    HoverInfo::Param P;
    P.Type.emplace("...");
    HI.Parameters->push_back(std::move(P));
  }

  // We don't want any type info, if name already contains it. This is true for
  // constructors/destructors and conversion operators.
  const auto NK = FD->getDeclName().getNameKind();
  if (NK == DeclarationName::CXXConstructorName ||
      NK == DeclarationName::CXXDestructorName ||
      NK == DeclarationName::CXXConversionFunctionName)
    return;
  QualType ReturnType = Simplifier.simplify(FD->getReturnType());
  HI.ReturnType = printType(ReturnType, FD->getASTContext(), PP);
}

// Non-negative numbers are printed using min digits
// 0     => 0x0
// 100   => 0x64
// Negative numbers are sign-extended to 32/64 bits
// -2    => 0xfffffffe
// -2^32 => 0xffffffff00000000
static llvm::FormattedNumber printHex(const llvm::APSInt &V) {
  assert(V.getSignificantBits() <= 64 && "Can't print more than 64 bits.");
  uint64_t Bits =
      V.getBitWidth() > 64 ? V.trunc(64).getZExtValue() : V.getZExtValue();
  if (V.isNegative() && V.getSignificantBits() <= 32)
    return llvm::format_hex(uint32_t(Bits), 0);
  return llvm::format_hex(Bits, 0);
}

std::optional<std::string> printExprValue(const Expr *E,
                                          const ASTContext &Ctx) {
  // InitListExpr has two forms, syntactic and semantic. They are the same thing
  // (refer to a same AST node) in most cases.
  // When they are different, RAV returns the syntactic form, and we should feed
  // the semantic form to EvaluateAsRValue.
  if (const auto *ILE = llvm::dyn_cast<InitListExpr>(E)) {
    if (!ILE->isSemanticForm())
      E = ILE->getSemanticForm();
  }

  // Evaluating [[foo]]() as "&foo" isn't useful, and prevents us walking up
  // to the enclosing call. Evaluating an expression of void type doesn't
  // produce a meaningful result.
  QualType T = E->getType();
  if (T.isNull() || T->isFunctionType() || T->isFunctionPointerType() ||
      T->isFunctionReferenceType() || T->isVoidType())
    return std::nullopt;

  Expr::EvalResult Constant;
  // Attempt to evaluate. If expr is dependent, evaluation crashes!
  if (E->isValueDependent() || !E->EvaluateAsRValue(Constant, Ctx) ||
      Constant.Val.isUnion())
    return std::nullopt;

  if (auto Result = formatAPValue(Constant.Val, T, Ctx))
    return Result;

  // Show enums symbolically, not numerically like APValue::printPretty().
  if (T->isEnumeralType() && Constant.Val.isInt() &&
      Constant.Val.getInt().getSignificantBits() <= 64) {
    // Compare to int64_t to avoid bit-width match requirements.
    int64_t Val = Constant.Val.getInt().getExtValue();
    for (const EnumConstantDecl *ECD :
         T->castAs<EnumType>()->getDecl()->enumerators())
      if (ECD->getInitVal() == Val)
        return llvm::formatv("{0} ({1})", ECD->getNameAsString(),
                             printHex(Constant.Val.getInt()))
            .str();
  }
  // Show hex value of integers if they're at least 10 (or negative!)
  if (T->isIntegralOrEnumerationType() && Constant.Val.isInt() &&
      Constant.Val.getInt().getSignificantBits() <= 64) {
    if (T->isCharType()) {
      return llvm::formatv("({0}){1}", T.getAsString(Ctx.getPrintingPolicy()),
                           Constant.Val.getAsString(Ctx, T))
          .str();
    }
    if (Constant.Val.getInt().uge(10))
      return llvm::formatv("{0} ({1})", Constant.Val.getAsString(Ctx, T),
                           printHex(Constant.Val.getInt()))
          .str();
  }
  return Constant.Val.getAsString(Ctx, T);
}

struct PrintExprResult {
  /// The evaluation result on expression `Expr`.
  std::optional<std::string> PrintedValue;
  /// The Expr object that represents the closest evaluable
  /// expression.
  const clang::Expr *TheExpr;
  /// The node of selection tree where the traversal stops.
  const SelectionTree::Node *TheNode;
};

// Seek the closest evaluable expression along the ancestors of node N
// in a selection tree. If a node in the path can be converted to an evaluable
// Expr, a possible evaluation would happen and the associated context
// is returned.
// If evaluation couldn't be done, return the node where the traversal ends.
PrintExprResult printExprValue(const SelectionTree::Node *N,
                               const ASTContext &Ctx) {
  for (; N; N = N->Parent) {
    // Try to evaluate the first evaluatable enclosing expression.
    if (const Expr *E = N->ASTNode.get<Expr>()) {
      // Once we cross an expression of type 'cv void', the evaluated result
      // has nothing to do with our original cursor position.
      if (!E->getType().isNull() && E->getType()->isVoidType())
        break;
      if (auto Val = printExprValue(E, Ctx))
        return PrintExprResult{/*PrintedValue=*/std::move(Val), /*Expr=*/E,
                               /*Node=*/N};
    } else if (N->ASTNode.get<Decl>() || N->ASTNode.get<Stmt>()) {
      // Refuse to cross certain non-exprs. (TypeLoc are OK as part of Exprs).
      // This tries to ensure we're showing a value related to the cursor.
      break;
    }
  }
  return PrintExprResult{/*PrintedValue=*/std::nullopt, /*Expr=*/nullptr,
                         /*Node=*/N};
}

std::optional<StringRef> fieldName(const Expr *E) {
  const auto *ME = llvm::dyn_cast<MemberExpr>(E->IgnoreCasts());
  if (!ME || !llvm::isa<CXXThisExpr>(ME->getBase()->IgnoreCasts()))
    return std::nullopt;
  const auto *Field = llvm::dyn_cast<FieldDecl>(ME->getMemberDecl());
  if (!Field || !Field->getDeclName().isIdentifier())
    return std::nullopt;
  return Field->getDeclName().getAsIdentifierInfo()->getName();
}

// If CMD is of the form T foo() { return FieldName; } then returns "FieldName".
std::optional<StringRef> getterVariableName(const CXXMethodDecl *CMD) {
  assert(CMD->hasBody());
  if (CMD->getNumParams() != 0 || CMD->isVariadic())
    return std::nullopt;
  const auto *Body = llvm::dyn_cast<CompoundStmt>(CMD->getBody());
  const auto *OnlyReturn = (Body && Body->size() == 1)
                               ? llvm::dyn_cast<ReturnStmt>(Body->body_front())
                               : nullptr;
  if (!OnlyReturn || !OnlyReturn->getRetValue())
    return std::nullopt;
  return fieldName(OnlyReturn->getRetValue());
}

// If CMD is one of the forms:
//   void foo(T arg) { FieldName = arg; }
//   R foo(T arg) { FieldName = arg; return *this; }
//   void foo(T arg) { FieldName = std::move(arg); }
//   R foo(T arg) { FieldName = std::move(arg); return *this; }
// then returns "FieldName"
std::optional<StringRef> setterVariableName(const CXXMethodDecl *CMD) {
  assert(CMD->hasBody());
  if (CMD->isConst() || CMD->getNumParams() != 1 || CMD->isVariadic())
    return std::nullopt;
  const ParmVarDecl *Arg = CMD->getParamDecl(0);
  if (Arg->isParameterPack())
    return std::nullopt;

  const auto *Body = llvm::dyn_cast<CompoundStmt>(CMD->getBody());
  if (!Body || Body->size() == 0 || Body->size() > 2)
    return std::nullopt;
  // If the second statement exists, it must be `return this` or `return *this`.
  if (Body->size() == 2) {
    auto *Ret = llvm::dyn_cast<ReturnStmt>(Body->body_back());
    if (!Ret || !Ret->getRetValue())
      return std::nullopt;
    const Expr *RetVal = Ret->getRetValue()->IgnoreCasts();
    if (const auto *UO = llvm::dyn_cast<UnaryOperator>(RetVal)) {
      if (UO->getOpcode() != UO_Deref)
        return std::nullopt;
      RetVal = UO->getSubExpr()->IgnoreCasts();
    }
    if (!llvm::isa<CXXThisExpr>(RetVal))
      return std::nullopt;
  }
  // The first statement must be an assignment of the arg to a field.
  const Expr *LHS, *RHS;
  if (const auto *BO = llvm::dyn_cast<BinaryOperator>(Body->body_front())) {
    if (BO->getOpcode() != BO_Assign)
      return std::nullopt;
    LHS = BO->getLHS();
    RHS = BO->getRHS();
  } else if (const auto *COCE =
                 llvm::dyn_cast<CXXOperatorCallExpr>(Body->body_front())) {
    if (COCE->getOperator() != OO_Equal || COCE->getNumArgs() != 2)
      return std::nullopt;
    LHS = COCE->getArg(0);
    RHS = COCE->getArg(1);
  } else {
    return std::nullopt;
  }

  // Detect the case when the item is moved into the field.
  if (auto *CE = llvm::dyn_cast<CallExpr>(RHS->IgnoreCasts())) {
    if (CE->getNumArgs() != 1)
      return std::nullopt;
    auto *ND = llvm::dyn_cast_or_null<NamedDecl>(CE->getCalleeDecl());
    if (!ND || !ND->getIdentifier() || ND->getName() != "move" ||
        !ND->isInStdNamespace())
      return std::nullopt;
    RHS = CE->getArg(0);
  }

  auto *DRE = llvm::dyn_cast<DeclRefExpr>(RHS->IgnoreCasts());
  if (!DRE || DRE->getDecl() != Arg)
    return std::nullopt;
  return fieldName(LHS);
}

std::string synthesizeDocumentation(const NamedDecl *ND) {
  if (const auto *CMD = llvm::dyn_cast<CXXMethodDecl>(ND)) {
    // Is this an ordinary, non-static method whose definition is visible?
    if (CMD->getDeclName().isIdentifier() && !CMD->isStatic() &&
        (CMD = llvm::dyn_cast_or_null<CXXMethodDecl>(CMD->getDefinition())) &&
        CMD->hasBody()) {
      if (const auto GetterField = getterVariableName(CMD))
        return llvm::formatv("Trivial accessor for `{0}`.", *GetterField);
      if (const auto SetterField = setterVariableName(CMD))
        return llvm::formatv("Trivial setter for `{0}`.", *SetterField);
    }
  }
  return "";
}

/// Generate a \p Hover object given the declaration \p D.
HoverInfo getHoverContents(const NamedDecl *D, const PrintingPolicy &PP,
                           const SymbolIndex *Index,
                           const syntax::TokenBuffer &TB,
                           std::optional<QualType> &PrettyType,
                           TypeSimplifier &Simplifier) {
  HoverInfo HI;
  auto &Ctx = D->getASTContext();

  HI.AccessSpecifier = getAccessSpelling(D->getAccess()).str();
  HI.NamespaceScope = getNamespaceScope(D, PP);
  if (!HI.NamespaceScope->empty())
    HI.NamespaceScope->append("::");

  HI.Kind = index::getSymbolInfo(D).Kind;

  HI.LocalScope = getLocalScope(D, PP);
  if (!HI.LocalScope.empty())
    HI.LocalScope.append("::");

  HI.Name = D->getNameAsString();

  const auto *CommentD = getDeclForComment(D);
  HI.Documentation = getDeclComment(Ctx, *CommentD);
  enhanceFromIndex(HI, *CommentD, Index);
  if (HI.Documentation.empty())
    HI.Documentation = synthesizeDocumentation(D);

  // Fill in template params.
  if (const TemplateDecl *TD = D->getDescribedTemplate()) {
    HI.TemplateParameters =
        fetchTemplateParameters(TD->getTemplateParameters(), PP, Simplifier);
  } else if (const FunctionDecl *FD = D->getAsFunction()) {
    if (const auto *FTD = FD->getDescribedTemplate()) {
      HI.TemplateParameters =
          fetchTemplateParameters(FTD->getTemplateParameters(), PP, Simplifier);
    }
  }
  // For members of class templates, show class template params
  if (!HI.TemplateParameters) {
    if (const auto *RD = llvm::dyn_cast<CXXRecordDecl>(D->getDeclContext())) {
      if (const auto *CTD = RD->getDescribedClassTemplate()) {
        if (!isa<ClassTemplateSpecializationDecl>(D->getDeclContext()))
          HI.TemplateParameters = fetchTemplateParameters(
              CTD->getTemplateParameters(), PP, Simplifier);
      }
    }
  }

  // If we are on an instantiation, get the specialized arguments from D.
  if (const auto *FD = D->getAsFunction()) {
    if (FD->isTemplateInstantiation()) {
      if (const auto *Args = FD->getTemplateSpecializationArgs()) {
        std::string ArgString;
        llvm::raw_string_ostream OS(ArgString);
        printPrettyTemplateArgumentList(
            OS, Args->asArray(), PP,
            FD->getPrimaryTemplate()
                ? FD->getPrimaryTemplate()->getTemplateParameters()
                : nullptr,
            Simplifier);
        HI.SpecializedTemplateArgs = OS.str();
      }
    }
  } else if (const auto *CTSD =
                 llvm::dyn_cast<ClassTemplateSpecializationDecl>(D)) {
    llvm::ArrayRef<clang::TemplateArgument> Args;
    if (PrettyType) {
      if (const auto *TST = PrettyType->getTypePtr()
                                ->getAsNonAliasTemplateSpecializationType()) {
        Args = TST->template_arguments();
      }
    }
    if (Args.empty())
      Args = CTSD->getTemplateInstantiationArgs().asArray();
    std::string ArgString;
    llvm::raw_string_ostream OS(ArgString);
    printPrettyTemplateArgumentList(
        OS, Args, PP, CTSD->getSpecializedTemplate()->getTemplateParameters(),
        Simplifier);
    HI.SpecializedTemplateArgs = OS.str();
  } else if (const auto *VSD =
                 llvm::dyn_cast<VarTemplateSpecializationDecl>(D)) {
    const auto &Args = VSD->getTemplateArgs();
    std::string ArgString;
    llvm::raw_string_ostream OS(ArgString);
    printPrettyTemplateArgumentList(
        OS, Args.asArray(), PP,
        VSD->getSpecializedTemplate()->getTemplateParameters(), Simplifier);
    HI.SpecializedTemplateArgs = OS.str();
  }

  // Function attribute/qualifier
  if (const auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
    HI.IsDefaulted = Func->isDefaulted();
    HI.IsInline = Func->isInlined();
    HI.IsConstexpr = Func->isConstexpr();
    HI.IsConsteval = Func->isConsteval();
    if (const auto *Method = llvm::dyn_cast<CXXMethodDecl>(D)) {
      HI.IsVirtual = Method->isVirtual();
      HI.IsConst = Method->isConst();
      HI.IsOverride = Method->size_overridden_methods() > 0;
      HI.IsFinal = Method->hasAttr<FinalAttr>();
      if (PrettyType) {
        QualType PrettyTypeNonConst = *PrettyType;
        PrettyTypeNonConst.removeLocalConst();
        HI.LocalScope.clear();
        HI.NamespaceScope.reset();
        llvm::raw_string_ostream OS{HI.LocalScope};
        PrettyTypeNonConst.print(OS, PP);
        OS << "::";
      }
    }
    HI.IsStatic = Func->isStatic();
    if (const auto *FT = Func->getType()->getAs<FunctionProtoType>()) {
      HI.RefQualifier = FT->getRefQualifier();
      HI.HasTrailingReturn = FT->hasTrailingReturn();
      if (FT->isNothrow()) {
        if (const Expr *NoexceptExpr = FT->getNoexceptExpr()) {
          HI.Noexcept = "noexcept(" + printExpr(NoexceptExpr, PP) + ")";
        } else {
          HI.Noexcept = "noexcept";
        }
      }
    }
  }

  // Fill in types and params.
  if (const FunctionDecl *FD = getUnderlyingFunction(D)) {
    if (PrettyType) {
      QualType &ScopeType = *PrettyType;
      if (const auto *TST =
              ScopeType->getAsNonAliasTemplateSpecializationType()) {
        auto TemplateArgs = TST->template_arguments();
        size_t Count = 0;
        llvm::for_each(TemplateArgs, [&](const TemplateArgument &Arg) {
          if (Arg.getKind() == TemplateArgument::Type)
            Count += Simplifier.pushLocalTypeAlias(Arg.getAsType());
        });
        fillFunctionTypeAndParams(HI, D, FD, PP, Simplifier);
        Simplifier.popLocalTypeAlias(Count);
      }
    } else
      fillFunctionTypeAndParams(HI, D, FD, PP, Simplifier);
  } else if (const auto *VD = dyn_cast<ValueDecl>(D)) {
    // For variables, print the name in the middle of the type.
    // QualType::print is smart enough to put it in the right place.
    // local variable doesn't need scope name
    QualType Simplified = Simplifier.simplify(VD->getType());
    if ((HI.Kind == index::SymbolKind::Variable && !HI.LocalScope.empty()) ||
        HI.Kind == index::SymbolKind::Parameter)
      HI.Type = printType(Simplified, Ctx, PP, HI.Name);
    else if (HI.NamespaceScope)
      HI.Type = printType(Simplified, Ctx, PP,
                          *HI.NamespaceScope + HI.LocalScope + HI.Name);
    else
      HI.Type = printType(Simplified, Ctx, PP, HI.LocalScope + HI.Name);
    // The name is now part of the type string, so clear it to avoid
    // duplication.
    HI.Name.clear();
  } else if (const auto *TTP = dyn_cast<TemplateTypeParmDecl>(D))
    HI.Type = TTP->wasDeclaredWithTypename() ? "typename" : "class";
  else if (const auto *TTP = dyn_cast<TemplateTemplateParmDecl>(D))
    HI.Type = printType(TTP, PP, Simplifier);
  else if (const auto *VT = dyn_cast<VarTemplateDecl>(D)) {
    auto *TemplatedDecl = VT->getTemplatedDecl();
    auto PrintPolicy = PP;
    PrintPolicy.TerseOutput = false; // print initializer
    HI.Type = printType(TemplatedDecl->getType(), Ctx, PrintPolicy);
  } else if (const auto *TN = dyn_cast<TypedefNameDecl>(D))
    HI.Type = printType(TN->getUnderlyingType().getDesugaredType(Ctx), Ctx, PP);
  else if (const auto *TAT = dyn_cast<TypeAliasTemplateDecl>(D))
    HI.Type = printType(TAT->getTemplatedDecl()->getUnderlyingType(), Ctx, PP);
  else if (const auto *ED = dyn_cast<EnumDecl>(D)) {
    QualType UnderlyingType = ED->getIntegerType();
    if (!UnderlyingType.isNull())
      HI.Type = printType(UnderlyingType, Ctx, PP);
    HI.IsEnumClass = ED->isScopedUsingClassTag();
  }

  // Fill in value with evaluated initializer if possible.
  if (const auto *Var = dyn_cast<VarDecl>(D); Var && !Var->isInvalidDecl()) {
    HI.IsConstexpr = Var->isConstexpr();
    HI.IsInline = Var->isInline();
    HI.IsStatic = Var->isStaticLocal() || Var->isStaticDataMember();
    if (const Expr *Init = Var->getInit()) {
      HI.Value = printExprValue(Init, Ctx);
      if (!HI.Value)
        HI.Initializer = printExpr(Init, PP);
    }
  } else if (const auto *ECD = dyn_cast<EnumConstantDecl>(D)) {
    // Dependent enums (e.g. nested in template classes) don't have values yet.
    HI.Name = ECD->getName();
    if (!ECD->getType()->isDependentType())
      HI.Value = toString(ECD->getInitVal(), 10);
  }

  auto printFullName = [&](const NamedDecl &ND) {
    std::string Name;
    llvm::raw_string_ostream OS(Name);
    ND.printQualifiedName(OS, PP);
    return Name;
  };

  if (D->isFunctionOrFunctionTemplate() || isa<EnumConstantDecl>(D) ||
      isa<EnumDecl>(D) || isa<VarDecl>(D)) {
    // Do nothing, will be handled in present().
  } else if (isa<NamespaceDecl>(D)) {
    HI.Definition = "namespace " + printFullName(*D);
  } else if (const auto *TD = dyn_cast<TagDecl>(D)) {
    if (const auto *RD = llvm::dyn_cast<CXXRecordDecl>(TD))
      if (RD->hasAttr<FinalAttr>())
        HI.IsFinal = true;
    std::string QName = printFullName(*D);
    // Anonymous tags already have their kind in the name, e.g., "(anonymous
    // struct)".
    if (TD->getDeclName().isEmpty() || !TD->getIdentifier())
      HI.Definition = QName;
    else
      HI.Definition = std::string(TD->getKindName()) + " " + QName;
  } else if (const auto *TND = dyn_cast<TypedefNameDecl>(D)) {
    std::string Definition;
    llvm::raw_string_ostream OS(Definition);
    if (const auto *TAD = dyn_cast<TypeAliasDecl>(TND)) {
      OS << "using " << HI.NamespaceScope << HI.LocalScope << HI.Name << " = ";
      TAD->getUnderlyingType().print(OS, PP);
    } else if (const auto *TD = dyn_cast<TypedefDecl>(TND)) {
      OS << "typedef ";
      TD->getUnderlyingType().print(OS, PP);
      OS << " " << HI.NamespaceScope << HI.LocalScope << HI.Name;
    }
    HI.Definition = OS.str();
  } else {
    HI.Definition = printDefinition(D, PP, TB);
  }

  return HI;
}

/// The standard defines __func__ as a "predefined variable".
std::optional<HoverInfo>
getPredefinedExprHoverContents(const PredefinedExpr &PE, ASTContext &Ctx,
                               const PrintingPolicy &PP) {
  HoverInfo HI;
  HI.Name = PE.getIdentKindName();
  HI.Kind = index::SymbolKind::Variable;
  HI.Documentation = "Name of the current function (predefined variable)";
  if (const StringLiteral *Name = PE.getFunctionName()) {
    HI.Value.emplace();
    llvm::raw_string_ostream OS(*HI.Value);
    Name->outputString(OS);
    HI.Type = printType(Name->getType(), Ctx, PP);
  } else {
    // Inside templates, the approximate type `const char[]` is still useful.
    QualType StringType = Ctx.getIncompleteArrayType(Ctx.CharTy.withConst(),
                                                     ArraySizeModifier::Normal,
                                                     /*IndexTypeQuals=*/0);
    HI.Type = printType(StringType, Ctx, PP);
  }
  return HI;
}

HoverInfo evaluateMacroExpansion(unsigned int SpellingBeginOffset,
                                 unsigned int SpellingEndOffset,
                                 llvm::ArrayRef<syntax::Token> Expanded,
                                 ParsedAST &AST) {
  auto &Context = AST.getASTContext();
  auto &Tokens = AST.getTokens();
  auto PP = getPrintingPolicy(Context.getPrintingPolicy());
  auto Tree = SelectionTree::createRight(Context, Tokens, SpellingBeginOffset,
                                         SpellingEndOffset);

  // If macro expands to one single token, rule out punctuator or digraph.
  // E.g., for the case `array L_BRACKET 42 R_BRACKET;` where L_BRACKET and
  // R_BRACKET expand to
  // '[' and ']' respectively, we don't want the type of
  // 'array[42]' when user hovers on L_BRACKET.
  if (Expanded.size() == 1)
    if (tok::getPunctuatorSpelling(Expanded[0].kind()))
      return {};

  auto *StartNode = Tree.commonAncestor();
  if (!StartNode)
    return {};
  // If the common ancestor is partially selected, do evaluate if it has no
  // children, thus we can disallow evaluation on incomplete expression.
  // For example,
  // #define PLUS_2 +2
  // 40 PL^US_2
  // In this case we don't want to present 'value: 2' as PLUS_2 actually expands
  // to a non-value rather than a binary operand.
  if (StartNode->Selected == SelectionTree::Selection::Partial)
    if (!StartNode->Children.empty())
      return {};

  HoverInfo HI;
  // Attempt to evaluate it from Expr first.
  auto ExprResult = printExprValue(StartNode, Context);
  HI.Value = std::move(ExprResult.PrintedValue);
  if (auto *E = ExprResult.TheExpr)
    HI.Type = printType(E->getType(), Context, PP);

  // If failed, extract the type from Decl if possible.
  if (!HI.Value && !HI.Type && ExprResult.TheNode)
    if (auto *VD = ExprResult.TheNode->ASTNode.get<VarDecl>())
      HI.Type = printType(VD->getType(), Context, PP);

  return HI;
}

/// Generate a \p Hover object given the macro \p MacroDecl.
HoverInfo getHoverContents(const DefinedMacro &Macro, const syntax::Token &Tok,
                           ParsedAST &AST) {
  HoverInfo HI;
  SourceManager &SM = AST.getSourceManager();
  HI.Name = std::string(Macro.Name);
  HI.Kind = index::SymbolKind::Macro;
  // FIXME: Populate documentation
  // FIXME: Populate parameters

  // Try to get the full definition, not just the name
  SourceLocation StartLoc = Macro.Info->getDefinitionLoc();
  SourceLocation EndLoc = Macro.Info->getDefinitionEndLoc();
  // Ensure that EndLoc is a valid offset. For example it might come from
  // preamble, and source file might've changed, in such a scenario EndLoc still
  // stays valid, but getLocForEndOfToken will fail as it is no longer a valid
  // offset.
  // Note that this check is just to ensure there's text data inside the range.
  // It will still succeed even when the data inside the range is irrelevant to
  // macro definition.
  if (SM.getPresumedLoc(EndLoc, /*UseLineDirectives=*/false).isValid()) {
    EndLoc = Lexer::getLocForEndOfToken(EndLoc, 0, SM, AST.getLangOpts());
    bool Invalid;
    StringRef Buffer = SM.getBufferData(SM.getFileID(StartLoc), &Invalid);
    if (!Invalid) {
      unsigned StartOffset = SM.getFileOffset(StartLoc);
      unsigned EndOffset = SM.getFileOffset(EndLoc);
      if (EndOffset <= Buffer.size() && StartOffset < EndOffset)
        HI.Definition =
            ("#define " + Buffer.substr(StartOffset, EndOffset - StartOffset))
                .str();
    }
  }

  if (auto Expansion = AST.getTokens().expansionStartingAt(&Tok)) {
    // We drop expansion that's longer than the threshold.
    // For extremely long expansion text, it's not readable from hover card
    // anyway.
    std::string ExpansionText;
    for (const auto &ExpandedTok : Expansion->Expanded) {
      ExpansionText += ExpandedTok.text(SM);
      ExpansionText += " ";
      if (ExpansionText.size() > 2048) {
        ExpansionText.clear();
        break;
      }
    }

    if (!ExpansionText.empty()) {
      if (!HI.Definition.empty()) {
        HI.Definition += "\n\n";
      }
      HI.Definition += "// Expands to\n";
      HI.Definition += ExpansionText;
    }

    auto Evaluated = evaluateMacroExpansion(
        /*SpellingBeginOffset=*/SM.getFileOffset(Tok.location()),
        /*SpellingEndOffset=*/SM.getFileOffset(Tok.endLocation()),
        /*Expanded=*/Expansion->Expanded, AST);
    HI.Value = std::move(Evaluated.Value);
    HI.Type = std::move(Evaluated.Type);
  }
  return HI;
}

std::string typeAsDefinition(const HoverInfo::PrintedType &PType) {
  std::string Result;
  llvm::raw_string_ostream OS(Result);
  OS << PType.Type;
  if (PType.AKA)
    OS << " // aka: " << *PType.AKA;
  return Result;
}

std::optional<HoverInfo> getThisExprHoverContents(const CXXThisExpr *CTE,
                                                  ASTContext &ASTCtx,
                                                  const PrintingPolicy &PP) {
  QualType OriginThisType = CTE->getType()->getPointeeType();
  QualType ClassType = declaredType(OriginThisType->getAsTagDecl());
  // For partial specialization class, origin `this` pointee type will be
  // parsed as `InjectedClassNameType`, which will ouput template arguments
  // like "type-parameter-0-0". So we retrieve user written class type in this
  // case.
  QualType PrettyThisType = ASTCtx.getPointerType(
      QualType(ClassType.getTypePtr(), OriginThisType.getCVRQualifiers()));

  HoverInfo HI;
  HI.Name = "this";
  HI.Definition = typeAsDefinition(printType(PrettyThisType, ASTCtx, PP));
  return HI;
}

/// Generate a HoverInfo object given the deduced type \p QT
HoverInfo getDeducedTypeHoverContents(QualType QT, const syntax::Token &Tok,
                                      ParsedAST &AST, const PrintingPolicy &PP,
                                      const SymbolIndex *Index) {
  HoverInfo HI;
  ASTContext &ASTCtx = AST.getASTContext();
  // FIXME: distinguish decltype(auto) vs decltype(expr)
  HI.Name = tok::getTokenName(Tok.kind());
  HI.Kind = index::SymbolKind::TypeAlias;

  if (QT->isUndeducedAutoType()) {
    HI.Definition = "/* not deduced */";
  } else {
    // Create a new policy that prints scopes.
    if (const auto *D = QT->getAsCXXRecordDecl(); D && D->isLambda()) {
      const FunctionDecl *FD = D->getLambdaCallOperator();
      // This is a bit of a hack, we don't have a TypeSimplifier available here.
      // But lambda's return type is usually inferred and doesn't need
      // simplification.
      TypeSimplifier Simplifier(AST);
      fillFunctionTypeAndParams(HI, FD, FD, PP, Simplifier);
      HI.Kind = index::SymbolKind::Variable;
      HI.Name = "";
      HI.Type = std::nullopt;

      const auto *CommentD = getDeclForComment(D);
      HI.Documentation = getDeclComment(ASTCtx, *CommentD);
      enhanceFromIndex(HI, *CommentD, Index);
    } else {
      HI.Definition = typeAsDefinition(printType(QT, ASTCtx, PP));
      if (const auto *D = QT->getAsTagDecl()) {
        const auto *CommentD = getDeclForComment(D);
        HI.Documentation = getDeclComment(ASTCtx, *CommentD);
        enhanceFromIndex(HI, *CommentD, Index);
      }
    }
  }

  return HI;
}

HoverInfo getStringLiteralContents(const StringLiteral *SL,
                                   const PrintingPolicy &PP) {
  HoverInfo HI;
  HI.Size = (SL->getLength() + 1) * SL->getCharByteWidth() * 8;
  std::string Def;
  llvm::raw_string_ostream OS(Def);
  OS << "(" << SL->getType().getAsString(PP) << ")";
  SL->outputString(OS);
  HI.Definition = std::move(Def);
  return HI;
}

bool isLiteral(const Expr *E) {
  // Unfortunately there's no common base Literal classes inherits from
  // (apart from Expr), therefore these exclusions.
  return llvm::isa<CompoundLiteralExpr>(E) ||
         llvm::isa<CXXBoolLiteralExpr>(E) ||
         llvm::isa<CXXNullPtrLiteralExpr>(E) ||
         llvm::isa<FixedPointLiteral>(E) || llvm::isa<FloatingLiteral>(E) ||
         llvm::isa<ImaginaryLiteral>(E) || llvm::isa<IntegerLiteral>(E) ||
         llvm::isa<CharacterLiteral>(E) || llvm::isa<StringLiteral>(E) ||
         llvm::isa<UserDefinedLiteral>(E);
}

llvm::StringLiteral getNameForExpr(const Expr *E) {
  // FIXME: Come up with names for `special` expressions.
  //
  // It's an known issue for GCC5, https://godbolt.org/z/Z_tbgi. Work around
  // that by using explicit conversion constructor.
  //
  // TODO: Once GCC5 is fully retired and not the minimal requirement as stated
  // in `GettingStarted`, please remove the explicit conversion constructor.
  return llvm::StringLiteral("expression");
}

void maybeAddCalleeArgInfo(const SelectionTree::Node *N, HoverInfo &HI,
                           const PrintingPolicy &PP,
                           TypeSimplifier &Simplifier);

// Generates hover info for `this` and evaluatable expressions.
// FIXME: Support hover for literals (esp user-defined)
std::optional<HoverInfo> getHoverContents(const SelectionTree::Node *N,
                                          const Expr *E, ParsedAST &AST,
                                          const PrintingPolicy &PP,
                                          const SymbolIndex *Index,
                                          TypeSimplifier &Simplifier) {
  std::optional<HoverInfo> HI;

  // Check for aggregate initialization.
  const InitListExpr *ILE = nullptr;
  unsigned InitIdx = 0;
  for (const auto *P = N; P && P->Parent; P = P->Parent) {
    if (auto *Candidate = P->Parent->ASTNode.get<InitListExpr>()) {
      const Expr *CurrentE = P->ASTNode.get<Expr>();
      for (unsigned I = 0; I < Candidate->getNumInits(); ++I) {
        if (Candidate->getInit(I) == CurrentE) {
          ILE = Candidate;
          InitIdx = I;
          break;
        }
      }
    }
    if (ILE)
      break;
  }

  if (ILE) {
    QualType AggType = ILE->getType();
    if (AggType->isAggregateType()) {
      if (const RecordDecl *RD = AggType->getAsRecordDecl()) {
        unsigned FieldNo = 0;
        for (const FieldDecl *FD : RD->fields()) {
          if (FD->isUnnamedBitField())
            continue;
          if (FieldNo == InitIdx) {
            if (auto Val = printExprValue(E, AST.getASTContext())) {
              HI.emplace();
              HI->Name = ("." + FD->getName()).str();
              HI->Value = *Val;
              HI->Kind = index::SymbolKind::Field;
              return HI;
            }
            break;
          }
          ++FieldNo;
        }
      }
    }
  }

  if (const StringLiteral *SL = dyn_cast<StringLiteral>(E)) {
    // Print the type and the size for string literals
    HI = getStringLiteralContents(SL, PP);
  } else if (isLiteral(E)) {
    HI.emplace();
    HI->Kind = index::SymbolKind::Unknown;
    std::string Def;
    llvm::raw_string_ostream OS(Def);
    OS << "(" << E->getType().getAsString(PP) << ")";
    if (auto Val = printExprValue(E, AST.getASTContext()))
      OS << *Val;
    HI->Definition = std::move(Def);
    return HI;
  }

  // For `this` expr we currently generate hover with pointee type.
  if (const CXXThisExpr *CTE = dyn_cast<CXXThisExpr>(E))
    HI = getThisExprHoverContents(CTE, AST.getASTContext(), PP);
  if (const PredefinedExpr *PE = dyn_cast<PredefinedExpr>(E))
    HI = getPredefinedExprHoverContents(*PE, AST.getASTContext(), PP);
  if (!HI) {
    if (auto Val = printExprValue(E, AST.getASTContext())) {
      HI.emplace();
      HI->Type = printType(E->getType(), AST.getASTContext(), PP);
      HI->Value = *Val;
      HI->Name = std::string(getNameForExpr(E));
    }
  }

  if (HI)
    maybeAddCalleeArgInfo(N, *HI, PP, Simplifier);

  return HI;
}

// Generates hover info for attributes.
std::optional<HoverInfo> getHoverContents(const Attr *A, ParsedAST &AST) {
  HoverInfo HI;
  HI.Name = A->getSpelling();
  if (A->hasScope())
    HI.LocalScope = A->getScopeName()->getName().str();
  {
    llvm::raw_string_ostream OS(HI.Definition);
    A->printPretty(OS, AST.getASTContext().getPrintingPolicy());
  }
  HI.Documentation = Attr::getDocumentation(A->getKind()).str();
  return HI;
}

bool isParagraphBreak(llvm::StringRef Rest) {
  return Rest.ltrim(" \t").starts_with("\n");
}

bool punctuationIndicatesLineBreak(llvm::StringRef Line) {
  constexpr llvm::StringLiteral Punctuation = R"txt(.:,;!?)txt";

  Line = Line.rtrim();
  return !Line.empty() && Punctuation.contains(Line.back());
}

bool isHardLineBreakIndicator(llvm::StringRef Rest) {
  // '-'/'*' md list, '@'/'\' documentation command, '>' md blockquote,
  // '#' headings, '`' code blocks
  constexpr llvm::StringLiteral LinebreakIndicators = R"txt(-*@\>#`)txt";

  Rest = Rest.ltrim(" \t");
  if (Rest.empty())
    return false;

  if (LinebreakIndicators.contains(Rest.front()))
    return true;

  if (llvm::isDigit(Rest.front())) {
    llvm::StringRef AfterDigit = Rest.drop_while(llvm::isDigit);
    if (AfterDigit.starts_with(".") || AfterDigit.starts_with(")"))
      return true;
  }
  return false;
}

bool isHardLineBreakAfter(llvm::StringRef Line, llvm::StringRef Rest) {
  // Should we also consider whether Line is short?
  return punctuationIndicatesLineBreak(Line) || isHardLineBreakIndicator(Rest);
}

void addLayoutInfo(const NamedDecl &ND, HoverInfo &HI) {
  if (ND.isInvalidDecl())
    return;

  const auto &Ctx = ND.getASTContext();
  if (auto *RD = llvm::dyn_cast<RecordDecl>(&ND)) {
    if (auto Size = Ctx.getTypeSizeInCharsIfKnown(RD->getTypeForDecl()))
      HI.Size = Size->getQuantity() * 8;
    if (!RD->isDependentType() && RD->isCompleteDefinition())
      HI.Align = Ctx.getTypeAlign(RD->getTypeForDecl());
    return;
  }

  if (const auto *FD = llvm::dyn_cast<FieldDecl>(&ND)) {
    const auto *Record = FD->getParent();
    HI.IsBitfield = FD->isBitField();
    if (Record)
      Record = Record->getDefinition();
    if (Record && !Record->isInvalidDecl() && !Record->isDependentType()) {
      HI.Align = Ctx.getTypeAlign(FD->getType());
      const ASTRecordLayout &Layout = Ctx.getASTRecordLayout(Record);
      HI.Offset = Layout.getFieldOffset(FD->getFieldIndex());
      if (FD->isBitField())
        HI.Size = FD->getBitWidthValue();
      else if (auto Size = Ctx.getTypeSizeInCharsIfKnown(FD->getType()))
        HI.Size = FD->isZeroSize(Ctx) ? 0 : Size->getQuantity() * 8;
      if (HI.Size) {
        unsigned EndOfField = *HI.Offset + *HI.Size;

        // Calculate padding following the field.
        if (!Record->isUnion() &&
            FD->getFieldIndex() + 1 < Layout.getFieldCount()) {
          // Measure padding up to the next class field.
          unsigned NextOffset = Layout.getFieldOffset(FD->getFieldIndex() + 1);
          if (NextOffset >= EndOfField) // next field could be a bitfield!
            HI.Padding = NextOffset - EndOfField;
        } else {
          // Measure padding up to the end of the object.
          HI.Padding = Layout.getSize().getQuantity() * 8 - EndOfField;
        }
      }
      // Offset in a union is always zero, so not really useful to report.
      if (Record->isUnion())
        HI.Offset.reset();
    }
    return;
  }
}

HoverInfo::PassType::PassMode getPassMode(QualType ParmType) {
  if (ParmType->isReferenceType()) {
    if (ParmType->getPointeeType().isConstQualified())
      return HoverInfo::PassType::ConstRef;
    return HoverInfo::PassType::Ref;
  }
  return HoverInfo::PassType::Value;
}

// If N is passed as argument to a function, fill HI.CalleeArgInfo with
// information about that argument.
void maybeAddCalleeArgInfo(const SelectionTree::Node *N, HoverInfo &HI,
                           const PrintingPolicy &PP,
                           TypeSimplifier &Simplifier) {
  const auto &OuterNode = N->outerImplicit();
  if (!OuterNode.Parent)
    return;

  const FunctionDecl *FD = nullptr;
  llvm::ArrayRef<const Expr *> Args;

  if (const auto *CE = OuterNode.Parent->ASTNode.get<CallExpr>()) {
    FD = CE->getDirectCallee();
    Args = {CE->getArgs(), CE->getNumArgs()};
  } else if (const auto *CE =
                 OuterNode.Parent->ASTNode.get<CXXConstructExpr>()) {
    FD = CE->getConstructor();
    Args = {CE->getArgs(), CE->getNumArgs()};
  }
  if (!FD)
    return;

  // For non-function-call-like operators (e.g. operator+, operator<<) it's
  // not immediately obvious what the "passed as" would refer to and, given
  // fixed function signature, the value would be very low anyway, so we choose
  // to not support that.
  // Both variadic functions and operator() (especially relevant for lambdas)
  // should be supported in the future.
  if (!FD || FD->isOverloadedOperator() || FD->isVariadic())
    return;

  HoverInfo::PassType PassType;

  auto Parameters = resolveForwardingParameters(FD);

  // Find argument index for N.
  for (unsigned I = 0; I < Args.size() && I < Parameters.size(); ++I) {
    if (Args[I] != OuterNode.ASTNode.get<Expr>())
      continue;

    // Extract matching argument from function declaration.
    if (const ParmVarDecl *PVD = Parameters[I]) {
      HI.CalleeArgInfo.emplace(toHoverInfoParam(PVD, PP, Simplifier));
      if (N == &OuterNode)
        PassType.PassBy = getPassMode(PVD->getType());
    }
    break;
  }
  if (!HI.CalleeArgInfo)
    return;

  // If we found a matching argument, also figure out if it's a
  // [const-]reference. For this we need to walk up the AST from the arg itself
  // to CallExpr and check all implicit casts, constructor calls, etc.
  if (const auto *E = N->ASTNode.get<Expr>()) {
    if (E->getType().isConstQualified())
      PassType.PassBy = HoverInfo::PassType::ConstRef;
  }

  for (auto *CastNode = N->Parent;
       CastNode != OuterNode.Parent && !PassType.Converted;
       CastNode = CastNode->Parent) {
    if (const auto *ImplicitCast = CastNode->ASTNode.get<ImplicitCastExpr>()) {
      switch (ImplicitCast->getCastKind()) {
      case CK_NoOp:
      case CK_DerivedToBase:
      case CK_UncheckedDerivedToBase:
        // If it was a reference before, it's still a reference.
        if (PassType.PassBy != HoverInfo::PassType::Value)
          PassType.PassBy = ImplicitCast->getType().isConstQualified()
                                ? HoverInfo::PassType::ConstRef
                                : HoverInfo::PassType::Ref;
        break;
      case CK_LValueToRValue:
      case CK_ArrayToPointerDecay:
      case CK_FunctionToPointerDecay:
      case CK_NullToPointer:
      case CK_NullToMemberPointer:
        // No longer a reference, but we do not show this as type conversion.
        PassType.PassBy = HoverInfo::PassType::Value;
        break;
      default:
        PassType.PassBy = HoverInfo::PassType::Value;
        PassType.Converted = true;
        break;
      }
    } else if (const auto *CtorCall =
                   CastNode->ASTNode.get<CXXConstructExpr>()) {
      // We want to be smart about copy constructors. They should not show up as
      // type conversion, but instead as passing by value.
      if (CtorCall->getConstructor()->isCopyConstructor())
        PassType.PassBy = HoverInfo::PassType::Value;
      else
        PassType.Converted = true;
    } else if (CastNode->ASTNode.get<MaterializeTemporaryExpr>()) {
      // Can't bind a non-const-ref to a temporary, so has to be const-ref
      PassType.PassBy = HoverInfo::PassType::ConstRef;
    } else { // Unknown implicit node, assume type conversion.
      PassType.PassBy = HoverInfo::PassType::Value;
      PassType.Converted = true;
    }
  }

  HI.CallPassType.emplace(PassType);
}

const NamedDecl *pickDeclToUse(llvm::ArrayRef<const NamedDecl *> Candidates) {
  if (Candidates.empty())
    return nullptr;

  // This is e.g the case for
  //     namespace ns { void foo(); }
  //     void bar() { using ns::foo; f^oo(); }
  // One declaration in Candidates will refer to the using declaration,
  // which isn't really useful for Hover. So use the other one,
  // which in this example would be the actual declaration of foo.
  if (Candidates.size() <= 2) {
    if (llvm::isa<UsingDecl>(Candidates.front()))
      return Candidates.back();
    return Candidates.front();
  }

  // For something like
  //     namespace ns { void foo(int); void foo(char); }
  //     using ns::foo;
  //     template <typename T> void bar() { fo^o(T{}); }
  // we actually want to show the using declaration,
  // it's not clear which declaration to pick otherwise.
  auto BaseDecls = llvm::make_filter_range(
      Candidates, [](const NamedDecl *D) { return llvm::isa<UsingDecl>(D); });
  if (std::distance(BaseDecls.begin(), BaseDecls.end()) == 1)
    return *BaseDecls.begin();

  return Candidates.front();
}

void maybeAddSymbolProviders(ParsedAST &AST, HoverInfo &HI,
                             include_cleaner::Symbol Sym) {
  trace::Span Tracer("Hover::maybeAddSymbolProviders");

  llvm::SmallVector<include_cleaner::Header> RankedProviders =
      include_cleaner::headersForSymbol(Sym, AST.getPreprocessor(),
                                        &AST.getPragmaIncludes());
  if (RankedProviders.empty())
    return;

  const SourceManager &SM = AST.getSourceManager();
  std::string Result;
  include_cleaner::Includes ConvertedIncludes = convertIncludes(AST);
  for (const auto &P : RankedProviders) {
    if (P.kind() == include_cleaner::Header::Physical &&
        P.physical() == SM.getFileEntryForID(SM.getMainFileID()))
      // Main file ranked higher than any #include'd file
      break;

    // Pick the best-ranked #include'd provider
    auto Matches = ConvertedIncludes.match(P);
    if (!Matches.empty()) {
      Result = Matches[0]->quote();
      break;
    }
  }

  if (!Result.empty()) {
    HI.Provider = std::move(Result);
    return;
  }

  // Pick the best-ranked non-#include'd provider
  const auto &H = RankedProviders.front();
  if (H.kind() == include_cleaner::Header::Physical &&
      H.physical() == SM.getFileEntryForID(SM.getMainFileID()))
    // Do not show main file as provider, otherwise we'll show provider info
    // on local variables, etc.
    return;

  HI.Provider = include_cleaner::spellHeader(
      {H, AST.getPreprocessor().getHeaderSearchInfo(),
       SM.getFileEntryForID(SM.getMainFileID())});
}

// FIXME: similar functions are present in FindHeaders.cpp (symbolName)
// and IncludeCleaner.cpp (getSymbolName). Introduce a name() method into
// include_cleaner::Symbol instead.
std::string getSymbolName(include_cleaner::Symbol Sym) {
  std::string Name;
  switch (Sym.kind()) {
  case include_cleaner::Symbol::Declaration:
    if (const auto *ND = llvm::dyn_cast<NamedDecl>(&Sym.declaration()))
      Name = ND->getDeclName().getAsString();
    break;
  case include_cleaner::Symbol::Macro:
    Name = Sym.macro().Name->getName();
    break;
  }
  return Name;
}

void maybeAddUsedSymbols(ParsedAST &AST, HoverInfo &HI, const Inclusion &Inc) {
  auto Converted = convertIncludes(AST);
  llvm::DenseSet<include_cleaner::Symbol> UsedSymbols;
  include_cleaner::walkUsed(
      AST.getLocalTopLevelDecls(), collectMacroReferences(AST),
      &AST.getPragmaIncludes(), AST.getPreprocessor(),
      [&](const include_cleaner::SymbolReference &Ref,
          llvm::ArrayRef<include_cleaner::Header> Providers) {
        if (Ref.RT != include_cleaner::RefType::Explicit ||
            UsedSymbols.contains(Ref.Target))
          return;

        if (isPreferredProvider(Inc, Converted, Providers))
          UsedSymbols.insert(Ref.Target);
      });

  for (const auto &UsedSymbolDecl : UsedSymbols)
    HI.UsedSymbolNames.push_back(getSymbolName(UsedSymbolDecl));
  llvm::sort(HI.UsedSymbolNames);
  HI.UsedSymbolNames.erase(llvm::unique(HI.UsedSymbolNames),
                           HI.UsedSymbolNames.end());
}

} // namespace

std::optional<HoverInfo> getHover(ParsedAST &AST, Position Pos,
                                  const format::FormatStyle &Style,
                                  const SymbolIndex *Index) {
  static constexpr trace::Metric HoverCountMetric(
      "hover", trace::Metric::Counter, "case");
  PrintingPolicy PP =
      getPrintingPolicy(AST.getASTContext().getPrintingPolicy());
  const SourceManager &SM = AST.getSourceManager();
  auto CurLoc = sourceLocationInMainFile(SM, Pos);
  if (!CurLoc) {
    llvm::consumeError(CurLoc.takeError());
    return std::nullopt;
  }
  const auto &TB = AST.getTokens();
  auto TokensTouchingCursor = syntax::spelledTokensTouching(*CurLoc, TB);
  // Early exit if there were no tokens around the cursor.
  if (TokensTouchingCursor.empty())
    return std::nullopt;

  // Show full header file path if cursor is on include directive.
  for (const auto &Inc : AST.getIncludeStructure().MainFileIncludes) {
    if (Inc.Resolved.empty() || Inc.HashLine != Pos.line)
      continue;
    HoverCountMetric.record(1, "include");
    HoverInfo HI;
    HI.Name = std::string(llvm::sys::path::filename(Inc.Resolved));
    // FIXME: We don't have a fitting value for Kind.
    HI.Definition =
        URIForFile::canonicalize(Inc.Resolved, AST.tuPath()).file().str();
    HI.DefinitionLanguage = "";
    maybeAddUsedSymbols(AST, HI, Inc);
    return HI;
  }

  // To be used as a backup for highlighting the selected token, we use back as
  // it aligns better with biases elsewhere (editors tend to send the position
  // for the left of the hovered token).
  CharSourceRange HighlightRange =
      TokensTouchingCursor.back().range(SM).toCharRange(SM);
  std::optional<HoverInfo> HI;
  // Macros and deducedtype only works on identifiers and auto/decltype keywords
  // respectively. Therefore they are only trggered on whichever works for them,
  // similar to SelectionTree::create().
  for (const auto &Tok : TokensTouchingCursor) {
    if (Tok.kind() == tok::identifier) {
      // Prefer the identifier token as a fallback highlighting range.
      HighlightRange = Tok.range(SM).toCharRange(SM);
      if (auto M = locateMacroAt(Tok, AST.getPreprocessor())) {
        HoverCountMetric.record(1, "macro");
        HI = getHoverContents(*M, Tok, AST);
        if (auto DefLoc = M->Info->getDefinitionLoc(); DefLoc.isValid()) {
          include_cleaner::Macro IncludeCleanerMacro{
              AST.getPreprocessor().getIdentifierInfo(Tok.text(SM)), DefLoc};
          maybeAddSymbolProviders(AST, *HI,
                                  include_cleaner::Symbol{IncludeCleanerMacro});
        }
        break;
      }
    } else if (Tok.kind() == tok::kw_auto || Tok.kind() == tok::kw_decltype) {
      HoverCountMetric.record(1, "keyword");
      if (auto Deduced = getDeducedType(AST.getASTContext(), Tok.location())) {
        HI = getDeducedTypeHoverContents(*Deduced, Tok, AST, PP, Index);
        HighlightRange = Tok.range(SM).toCharRange(SM);
        break;
      }

      // If we can't find interesting hover information for this
      // auto/decltype keyword, return nothing to avoid showing
      // irrelevant or incorrect informations.
      return std::nullopt;
    }
  }

  // If it wasn't auto/decltype or macro, look for decls and expressions.
  if (!HI) {
    auto Offset = SM.getFileOffset(*CurLoc);
    // Editors send the position on the left of the hovered character.
    // So our selection tree should be biased right. (Tested with VSCode).
    SelectionTree ST =
        SelectionTree::createRight(AST.getASTContext(), TB, Offset, Offset);
    if (const SelectionTree::Node *N = ST.commonAncestor()) {
      // FIXME: Fill in HighlightRange with range coming from N->ASTNode.
      auto Decls = explicitReferenceTargets(N->ASTNode, DeclRelation::Alias,
                                            AST.getHeuristicResolver());
      // If we didn't find a target and the cursor is on a TypeLoc, it may be
      // part of a declaration with a complex ("infix") declarator.
      // e.g. hovering `a` in `int (&a)[2]`. `SelectionTree` may select the
      // `ReferenceTypeLoc`, and `explicitReferenceTargets` on it yields no
      // decls. If the cursor is on an identifier, we walk up the
      // `SelectionTree` to find the enclosing `DeclaratorDecl`.
      if (Decls.empty() && N->ASTNode.get<TypeLoc>()) {
        bool IsOnIdentifier = false;
        for (const auto &Tok : TokensTouchingCursor) {
          if (Tok.kind() == tok::identifier) {
            IsOnIdentifier = true;
            break;
          }
        }
        if (IsOnIdentifier) {
          const SelectionTree::Node *DeclNode = N;
          for (const SelectionTree::Node *P = N->Parent; P; P = P->Parent) {
            if (const auto *D = P->ASTNode.get<Decl>()) {
              if (isa<DeclaratorDecl>(D)) {
                DeclNode = P;
                break;
              }
            }
          }
          // If we found an enclosing decl, re-run target finding on it.
          if (DeclNode != N)
            Decls =
                explicitReferenceTargets(DeclNode->ASTNode, DeclRelation::Alias,
                                         AST.getHeuristicResolver());
        }
      }
      if (const auto *DeclToUse = pickDeclToUse(Decls)) {
        std::optional<QualType> PrettyType;
        if (const TypeLoc *TL = N->ASTNode.get<TypeLoc>())
          PrettyType = TL->getType();
        else if (const DeclRefExpr *DRE = N->ASTNode.get<DeclRefExpr>()) {
          if (NestedNameSpecifier *NNS = DRE->getQualifier()) {
            if (const Type *TP = NNS->getAsType()) {
              if (const clang::TypedefType *TDefT = TP->getAs<TypedefType>())
                PrettyType = TDefT->desugar();
              else
                PrettyType = {TP, 0};
            }
          }
        } else {
          for (const SelectionTree::Node *CurrentNode = N; CurrentNode;
               CurrentNode = CurrentNode->Parent) {
            const MemberExpr *ME = CurrentNode->ASTNode.get<MemberExpr>();
            if (!ME || ME->getMemberDecl() != DeclToUse)
              continue;
            if (const Expr *BaseExpr = ME->getBase()) {
              if (const auto *CE = dyn_cast<CastExpr>(BaseExpr)) {
                CastKind Kind = CE->getCastKind();
                if (Kind == CK_DerivedToBase || Kind == CK_BaseToDerived ||
                    Kind == CK_UncheckedDerivedToBase) {
                  auto end = CE->path().end();
                  --end;
                  PrettyType = (*end)->getTypeSourceInfo()->getType();
                  break;
                } else if (const auto *SubExpr = CE->getSubExprAsWritten()) {
                  PrettyType = SubExpr->getType();
                  break;
                }
              }
              PrettyType = BaseExpr->getType();
              break;
            }
          }
        }
        HoverCountMetric.record(1, "decl");
        TypeSimplifier Simplifier(AST);
        HI = getHoverContents(DeclToUse, PP, Index, TB, PrettyType, Simplifier);
        addLayoutInfo(*DeclToUse, *HI);
        // Look for a close enclosing expression to show the value of.
        auto ExprEval = printExprValue(N, AST.getASTContext());
        if (ExprEval.PrintedValue) {
          bool IsSelf = false;
          if (const auto *DRE = llvm::dyn_cast_if_present<DeclRefExpr>(
                  ExprEval.TheExpr->IgnoreParenCasts()))
            IsSelf = (DRE->getDecl() == DeclToUse);
          if (!IsSelf)
            HI->ExpressionValue = ExprEval.PrintedValue;
        }
        maybeAddCalleeArgInfo(N, *HI, PP, Simplifier);

        if (!isa<NamespaceDecl>(DeclToUse))
          maybeAddSymbolProviders(AST, *HI,
                                  include_cleaner::Symbol{*DeclToUse});
      } else if (const Expr *E = N->ASTNode.get<Expr>()) {
        HoverCountMetric.record(1, "expr");
        TypeSimplifier Simplifier(AST);
        HI = getHoverContents(N, E, AST, PP, Index, Simplifier);
      } else if (const Attr *A = N->ASTNode.get<Attr>()) {
        HoverCountMetric.record(1, "attribute");
        HI = getHoverContents(A, AST);
      }
      // FIXME: support hovers for other nodes?
      //  - built-in types
    }
  }

  if (!HI)
    return std::nullopt;

  // Reformat Definition
  if (!HI->Definition.empty()) {
    auto Replacements = format::reformat(
        Style, HI->Definition, tooling::Range(0, HI->Definition.size()));
    if (auto Formatted =
            tooling::applyAllReplacements(HI->Definition, Replacements))
      HI->Definition = *Formatted;
  }

  HI->DefinitionLanguage = getMarkdownLanguage(AST.getASTContext());
  HI->SymRange = halfOpenToRange(SM, HighlightRange);

  return HI;
}

static bool paramListNeedBreakLine(const std::vector<HoverInfo::Param> &Params,
                                   size_t MaxSizePerLine = 90,
                                   size_t PreSize = 0) {
  size_t ParamLength = 0;
  for (auto &&P : Params) {
    if (P.Type)
      ParamLength += P.Type->Type.size();
    if (P.Name)
      ParamLength += P.Name->size();
    if (P.Default)
      ParamLength += P.Default->size();
    ParamLength += 2;
    if (ParamLength + PreSize > 90)
      return true;
  }
  return false;
}

markup::Document HoverInfo::present() const {
  markup::Document Output;
  std::string Signature;
  llvm::raw_string_ostream OS(Signature);

  // Helper to print specialized template arguments.
  auto PrintSpecializedTemplateArgs = [](llvm::raw_string_ostream &OS,
                                         std::optional<std::string> Args,
                                         size_t limit) {
    if (Args) {
      if (Args->size() > limit)
        OS << "<...>";
      else
        OS << *Args;
    }
  };

  const bool IsParam = (Kind == index::SymbolKind::Parameter ||
                        Kind == index::SymbolKind::TemplateTypeParm ||
                        Kind == index::SymbolKind::TemplateTemplateParm ||
                        Kind == index::SymbolKind::NonTypeTemplateParm);

  const bool IsFunction =
      (Kind == index::SymbolKind::Function ||
       Kind == index::SymbolKind::InstanceMethod ||
       Kind == index::SymbolKind::StaticMethod ||
       Kind == index::SymbolKind::Constructor ||
       Kind == index::SymbolKind::Destructor ||
       // Also handle function templates and other function-likes
       (Kind == index::SymbolKind::Unknown && (Parameters || ReturnType)));

  if (!AccessSpecifier.empty() && !IsParam)
    OS << AccessSpecifier << ":\n";
  if (TemplateParameters && !SpecializedTemplateArgs && !IsParam) {
    OS << "template <";
    if (paramListNeedBreakLine(*TemplateParameters, 90,
                               sizeof("template <") - 1)) {
      OS << "\n    ";
      llvm::ListSeparator LS(",\n    ");
      for (const auto &P : *TemplateParameters)
        OS << LS << P;
      OS << "\n";
    } else {
      llvm::ListSeparator LS(", ");
      for (const auto &P : *TemplateParameters)
        OS << LS << P;
    }
    OS << ">\n";
  }

  if (IsFunction) {
    const auto line1Length = OS.str().length();

    if (IsStatic)
      OS << "static ";
    else if (IsVirtual)
      OS << "virtual ";

    if (IsConsteval)
      OS << "consteval ";
    else if (IsConstexpr)
      OS << "constexpr ";
    else if (IsInline)
      OS << "inline ";

    if (HasTrailingReturn) {
      OS << "auto ";
    } else if (ReturnType) {
      llvm::StringRef TypeStr = ReturnType->Type;
      TypeStr = TypeStr.trim();
      OS << TypeStr;
      if (!TypeStr.empty() && TypeStr.back() != '*' && TypeStr.back() != '&')
        OS << " ";
      if (TypeStr.size() > 64)
        OS << "\n";
    }

    if (NamespaceScope)
      OS << *NamespaceScope;
    if (!LocalScope.empty())
      OS << LocalScope;
    OS << Name;

    PrintSpecializedTemplateArgs(OS, SpecializedTemplateArgs, 64);

    OS << "(";
    if (Parameters) {
      if (paramListNeedBreakLine(*Parameters, 90,
                                 OS.str().length() - line1Length)) {
        OS << "\n    ";
        llvm::ListSeparator LS(",\n    ");
        for (const auto &P : *Parameters)
          OS << LS << P;
        OS << "\n";
      } else {
        llvm::ListSeparator LS(", ");
        for (const auto &P : *Parameters)
          OS << LS << P;
      }
    }
    OS << ")";

    if (IsConst)
      OS << " const";
    switch (RefQualifier) {
    case RQ_LValue:
      OS << " &";
      break;
    case RQ_RValue:
      OS << " &&";
      break;
    case RQ_None:
      break;
    }
    if (IsOverride)
      OS << " override";
    if (IsFinal)
      OS << " final";
    if (Noexcept)
      OS << " " << *Noexcept;
    if (HasTrailingReturn && ReturnType)
      OS << " -> " << ReturnType->Type;
    if (IsDefaulted)
      OS << " = default";
  } else if (Kind == index::SymbolKind::Variable ||
             Kind == index::SymbolKind::Field ||
             Kind == index::SymbolKind::StaticProperty ||
             Kind == index::SymbolKind::Parameter) {
    if (IsStatic)
      OS << "static ";
    if (IsConstexpr)
      OS << "constexpr ";
    else if (IsInline)
      OS << "inline ";

    if (Parameters || ReturnType) // Lambda
      printPrettyLambdaType(OS, Parameters, ReturnType);
    else if (Type)
      OS << llvm::StringRef(Type->Type).ltrim();

    // HI.Name might be cleared if it was embedded in the type.
    if (!Name.empty())
      OS << " " << Name;
  } else if (Kind == index::SymbolKind::Class ||
             Kind == index::SymbolKind::Struct) {
    OS << index::getSymbolKindString(Kind) << " ";
    if (NamespaceScope)
      OS << *NamespaceScope;
    if (!LocalScope.empty())
      OS << LocalScope;
    OS << Name;
    PrintSpecializedTemplateArgs(OS, SpecializedTemplateArgs, 64);
    if (IsFinal)
      OS << " final";
  } else if (Kind == index::SymbolKind::EnumConstant) {
    OS << Name;
  } else if (Kind == index::SymbolKind::Enum) {
    OS << (IsEnumClass ? "enum class " : "enum ") << Name;
    if (Type && !Type->Type.empty())
      OS << " : " << Type->Type;
  } else if (!Definition.empty()) {
    OS << Definition;
  }

  if (Kind != index::SymbolKind::Class && Kind != index::SymbolKind::Struct &&
      !IsFunction) {
    PrintSpecializedTemplateArgs(OS, SpecializedTemplateArgs, 48);
  }

  if (Kind != index::SymbolKind::Unknown) {
    if (Value && !Value->empty()) {
      OS << " = " << *Value;
    } else if (Initializer && !Initializer->empty()) {
      OS << " = " << *Initializer;
    }
  }

  Output.addCodeBlock(OS.str(), DefinitionLanguage);

  if (ExpressionValue) {
    if (ExpressionValue->size() > 48)
      Output.addParagraph().appendCode("= {...}");
    else
      Output.addParagraph().appendCode("= " + *ExpressionValue);
  } else if (Value && Kind == index::SymbolKind::Unknown) {
    Output.addParagraph().appendCode("= " + *Value);
  }

  if (CalleeArgInfo) {
    auto &P = Output.addParagraph();
    P.appendText("Arg: ");
    if (CalleeArgInfo->Type)
      P.appendCode(CalleeArgInfo->Type->Type);
    else
      P.appendCode("(unknown)");
  }

  if (!IsStatic && (Size || Align || Offset || Padding)) {
    Output.addRuler();
    auto &Parag = Output.addParagraph();
    auto formatSizeE = [](size_t SizeInBit) {
      const auto Value = SizeInBit % 8 == 0 ? SizeInBit / 8 : SizeInBit;
      return llvm::formatv("{0} {1}", Value, Value == SizeInBit ? "b" : "B")
          .str();
    };

    if (Size)
      Parag.appendCode(formatSizeE(*Size));
    if (Align)
      Parag.appendText(", align: ").appendCode(formatSizeE(*Align));
    if (Offset) {
      const auto Bytes = *Offset / 8;
      const auto Bits = *Offset % 8;
      if (IsBitfield)
        Parag.appendText(", this+").appendCode(
            llvm::formatv("{0}[{1}]", Bytes, Bits).str());
      else
        Parag.appendText(", this+").appendCode(
            llvm::formatv("{0}", Bytes).str());
    }
    if (Padding && *Padding > 0)
      Parag.appendText(", padding: ").appendCode(formatSizeE(*Padding));
  }

  if (!Documentation.empty()) {
    Output.addRuler();
    parseDocumentation(Documentation, Output);
  }

  return Output;
}

// If the backtick at `Offset` starts a probable quoted range, return the range
// (including the quotes).
std::optional<llvm::StringRef> getBacktickQuoteRange(llvm::StringRef Line,
                                                     unsigned Offset) {
  assert(Line[Offset] == '`');

  // The open-quote is usually preceded by whitespace.
  llvm::StringRef Prefix = Line.substr(0, Offset);
  constexpr llvm::StringLiteral BeforeStartChars = " \t(=";
  if (!Prefix.empty() && !BeforeStartChars.contains(Prefix.back()))
    return std::nullopt;

  // The quoted string must be nonempty and usually has no leading/trailing ws.
  auto Next = Line.find('`', Offset + 1);
  if (Next == llvm::StringRef::npos)
    return std::nullopt;
  llvm::StringRef Contents = Line.slice(Offset + 1, Next);
  if (Contents.empty() || isWhitespace(Contents.front()) ||
      isWhitespace(Contents.back()))
    return std::nullopt;

  // The close-quote is usually followed by whitespace or punctuation.
  llvm::StringRef Suffix = Line.substr(Next + 1);
  constexpr llvm::StringLiteral AfterEndChars = " \t)=.,;:";
  if (!Suffix.empty() && !AfterEndChars.contains(Suffix.front()))
    return std::nullopt;

  return Line.slice(Offset, Next + 1);
}

void parseDocumentationLine(llvm::StringRef Line, markup::Paragraph &Out,
                            bool AppendSpace = true) {
  // Probably this is appendText(Line), but scan for something interesting.
  for (unsigned I = 0; I < Line.size();) {
    auto NextInteresting = Line.find_first_of("`@\\", I);
    if (NextInteresting == llvm::StringRef::npos) {
      Out.appendText(Line.substr(I));
      break;
    }

    Out.appendText(Line.slice(I, NextInteresting));
    I = NextInteresting;
    switch (Line[I]) {
    case '`':
      if (auto Range = getBacktickQuoteRange(Line, I)) {
        Out.appendCode(Range->trim("`"), /*Preserve=*/true);
        I += Range->size();
        continue;
      }
      break;
    case '@':
    case '\\':
      if (I + 2 < Line.size() && isalpha(Line[I + 1]) &&
          (isspace(Line[I + 2]) || ispunct(Line[I + 2]))) {
        char Cmd = Line[I + 1];
        llvm::StringRef Rest = Line.substr(I + 2).ltrim();
        auto ArgEndPos =
            Rest.find_if_not([](char C) { return isalnum(C) || C == '_'; });
        llvm::StringRef ArgText = Rest.substr(0, ArgEndPos);

        if (!ArgText.empty()) {
          if (Cmd == 'a') {
            Out.appendText("*").appendText(ArgText).appendText("*");
          } else if (Cmd == 'b') {
            Out.appendText("**").appendText(ArgText).appendText("**");
          } else if (Cmd == 'c' || Cmd == 'p') {
            Out.appendCode(ArgText);
          } else if (Cmd == 'c' || Cmd == 'p')
            Out.appendCode(ArgText);
          else
            break; // Unhandled command, treat as literal text.
          I += (Rest.data() - Line.data() - I) + ArgText.size();
          continue;
        }
      }
      break;
    }
    // If we didn't handle it, just append the character and move on.
    Out.appendText(Line.substr(I, 1));
    ++I;
  }
  if (AppendSpace)
    Out.appendSpace();
}

namespace {
struct ParsedDoxygen {
  std::string Brief;
  // For grouped commands like @param, we store a list of (arg, description).
  // Key is the display name, e.g. "Parameters".
  llvm::StringMap<std::vector<std::pair<std::string, std::string>>>
      GroupedCommands;
  // For other commands, we store them by their display name.
  llvm::StringMap<std::vector<std::string>> OtherCommands;
  // For free-form paragraphs after the brief and commands.
  std::vector<std::string> Paragraphs;
};
} // namespace
static ParsedDoxygen parseDoxygen(llvm::StringRef Comment) {
  ParsedDoxygen Docs;

  llvm::SmallVector<llvm::StringRef, 16> Lines;
  Comment.trim().split(Lines, '\n');

  size_t LineIdx = 0;

  // Phase 1: Brief description.
  // Everything up to the first blank line or the first command.
  std::string Brief;
  for (; LineIdx < Lines.size(); ++LineIdx) {
    llvm::StringRef Line = Lines[LineIdx].ltrim(" \t*");
    if (Line.empty() || Line.starts_with('@') || Line.starts_with('\\'))
      break;
    if (!Brief.empty())
      Brief += ' ';
    Brief += Line;
  }
  Docs.Brief = std::move(Brief);

  // Phase 2: Commands and paragraphs.
  while (LineIdx < Lines.size()) {
    llvm::StringRef Line = Lines[LineIdx].ltrim(" \t*");

    // Skip blank lines between blocks.
    if (Line.empty()) {
      LineIdx++;
      continue;
    }

    if (Line.consume_front("@") || Line.consume_front("\\")) {
      // This is a command block.
      auto [Cmd, Arg] = Line.split(' ');
      Arg = Arg.ltrim();

      std::string CommandText = Arg.str();
      size_t CommandEndLine = LineIdx;
      for (size_t i = LineIdx + 1; i < Lines.size(); ++i) {
        llvm::StringRef NextLine = Lines[i].ltrim(" \t*");
        if (NextLine.empty() || NextLine.starts_with('@') ||
            NextLine.starts_with('\\'))
          break;
        CommandText += " " + NextLine.str();
        CommandEndLine = i;
      }
      LineIdx = CommandEndLine + 1;

      // Process the command.
      auto GroupIt = DoxygenGroupedCommands.find(Cmd);
      if (GroupIt != DoxygenGroupedCommands.end()) {
        llvm::StringRef ArgRef(CommandText);
        auto [ParamName, Desc] = ArgRef.split(' ');
        Docs.GroupedCommands[GroupIt->second].emplace_back(
            ParamName.str(), std::string(Desc.ltrim()));
      } else {
        auto It = DoxygenCommandToText.find(Cmd);
        if (It != DoxygenCommandToText.end()) {
          if (Cmd == "brief") {
            if (!Docs.Brief.empty())
              Docs.Brief += "\n\n";
            Docs.Brief += CommandText;
          } else {
            Docs.OtherCommands[It->second].push_back(std::move(CommandText));
          }
        }
      }
    } else {
      // This is a paragraph block.
      std::string Paragraph;
      size_t ParagraphEndLine = LineIdx - 1;
      for (size_t i = LineIdx; i < Lines.size(); ++i) {
        llvm::StringRef NextLine = Lines[i].ltrim(" \t*");
        if (NextLine.empty() || NextLine.starts_with('@') ||
            NextLine.starts_with('\\'))
          break;
        if (!Paragraph.empty())
          Paragraph += ' ';
        Paragraph += NextLine;
        ParagraphEndLine = i;
      }
      LineIdx = ParagraphEndLine + 1;
      if (!Paragraph.empty())
        Docs.Paragraphs.push_back(std::move(Paragraph));
    }
  }

  return Docs;
}

static void renderDoxygen(const ParsedDoxygen &Docs, markup::Document &Output) {
  if (!Docs.Brief.empty()) {
    auto &P = Output.addParagraph();
    parseDocumentationLine(Docs.Brief, P, /*AppendSpace=*/false);
  }

  const char *GroupedCommandsOrder[] = {"Template Parameters", "Parameters"};
  for (const char *GroupName : GroupedCommandsOrder) {
    auto It = Docs.GroupedCommands.find(GroupName);
    if (It == Docs.GroupedCommands.end())
      continue;

    Output.addHeading(3).appendText(It->getKey());
    auto &List = Output.addBulletList();
    for (const auto &Param : It->getValue()) {
      auto &ItemP = List.addItem().addParagraph();
      ItemP.appendCode(Param.first);
      if (!Param.second.empty()) {
        ItemP.appendText(" \xE2\x80\x93 "); // en-dash
        parseDocumentationLine(Param.second, ItemP, /*AppendSpace=*/false);
      }
    }
  }

  const char *OtherCommandsOrder[] = {
      "Returns", "Since", "See also",   "Author",        "Authors",       "Bug",
      "Warning", "Todo",  "Deprecated", "Pre-condition", "Post-condition"};

  for (const char *CommandName : OtherCommandsOrder) {
    auto It = Docs.OtherCommands.find(CommandName);
    if (It == Docs.OtherCommands.end())
      continue;

    Output.addHeading(3).appendText(It->getKey());
    for (const auto &Text : It->getValue()) {
      auto &P = Output.addParagraph();
      parseDocumentationLine(Text, P, /*AppendSpace=*/false);
    }
  }

  for (const auto &ParaText : Docs.Paragraphs) {
    auto &P = Output.addParagraph();
    parseDocumentationLine(ParaText, P, /*AppendSpace=*/false);
  }
}

void parseDocumentation(llvm::StringRef Input, markup::Document &Output) {
  // If the comment doesn't seem to be Doxygen, use a simple markdown-like
  // parser. This is a heuristic.
  if (!Input.contains('@') && !Input.contains('\\')) {
    std::vector<llvm::StringRef> ParagraphLines;
    auto FlushParagraph = [&] {
      if (ParagraphLines.empty())
        return;
      auto &P = Output.addParagraph();
      for (llvm::StringRef Line : ParagraphLines)
        parseDocumentationLine(Line, P);
      ParagraphLines.clear();
    };

    llvm::StringRef Line, Rest = Input;
    for (std::tie(Line, Rest) = Rest.split('\n');
         !(Line.empty() && Rest.empty());
         std::tie(Line, Rest) = Rest.split('\n')) {
      Line = Line.ltrim();
      if (!Line.empty())
        ParagraphLines.push_back(Line);
      if (isParagraphBreak(Rest) || isHardLineBreakAfter(Line, Rest))
        FlushParagraph();
    }
    FlushParagraph();
    return;
  }

  ParsedDoxygen Docs = parseDoxygen(Input);
  renderDoxygen(Docs, Output);
}

llvm::raw_ostream &operator<<(llvm::raw_ostream &OS,
                              const HoverInfo::PrintedType &T) {
  OS << T.Type;
  if (T.AKA)
    OS << " (aka " << *T.AKA << ")";
  return OS;
}

llvm::raw_ostream &operator<<(llvm::raw_ostream &OS,
                              const HoverInfo::Param &P) {
  if (P.Type)
    OS << P.Type->Type;
  else if (P.Name)
    OS << *P.Name;
  if (P.Default)
    OS << " = " << *P.Default;
  return OS;
}

} // namespace clangd
} // namespace clang
