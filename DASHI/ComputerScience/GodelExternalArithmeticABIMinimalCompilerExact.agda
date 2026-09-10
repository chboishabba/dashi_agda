module DASHI.ComputerScience.GodelExternalArithmeticABIMinimalCompilerExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelDiagonalProvabilityContractExact as Godel
import DASHI.ComputerScience.GodelArithmetisedFormalSystemShapeAuthorityExact as Shape

------------------------------------------------------------------------
-- MINIMAL EXTERNAL-ARITHMETIC -> DASHI ABI COMPILER
--
-- This is deliberately source-agnostic.  Coquand T4, a Lean arithmetic
-- development, or another machine-checked arithmetic may instantiate this
-- record, but theorem names do not cross the ABI by themselves.
--
-- Unary formulas, binary formulas and sentences are RESTRICTED FIBRES of one
-- source formula carrier.  The source's actual free-variable relation is also
-- retained, so those fibres are not merely nominal wrappers.
------------------------------------------------------------------------

record ExternalArithmeticSource : Set₁ where
  field
    Term : Set
    RawFormula : Set
    Variable : Set

    FreeIn : Variable → RawFormula → Set
    distinguishedUnary : Variable
    distinguishedBinaryLeft : Variable
    distinguishedBinaryRight : Variable

    UnaryAdmissible : RawFormula → Set
    BinaryAdmissible : RawFormula → Set
    Closed : RawFormula → Set

    unaryFreeOnly :
      (φ : RawFormula) → UnaryAdmissible φ →
      (v : Variable) → FreeIn v φ → v ≡ distinguishedUnary

    binaryFreeOnly :
      (φ : RawFormula) → BinaryAdmissible φ →
      (v : Variable) → FreeIn v φ →
      (v ≡ distinguishedBinaryLeft) ⊎
      (v ≡ distinguishedBinaryRight)

    binaryVariablesDistinct :
      distinguishedBinaryLeft ≡ distinguishedBinaryRight → ⊥

    RawDeriv : RawFormula → Set

    codeTerm : Term → Nat
    codeFormula : RawFormula → Nat
    numeral : Nat → Term

    instantiateUnaryRaw : RawFormula → Term → RawFormula
    instantiateBinaryRaw : RawFormula → Term → Term → RawFormula

    unaryInstantiationClosed :
      (φ : RawFormula) → UnaryAdmissible φ → (t : Term) →
      Closed (instantiateUnaryRaw φ t)

    binaryInstantiationClosed :
      (φ : RawFormula) → BinaryAdmissible φ → (s t : Term) →
      Closed (instantiateBinaryRaw φ s t)

    NegationRaw : RawFormula → RawFormula
    ImplicationRaw : RawFormula → RawFormula → RawFormula
    BiconditionalRaw : RawFormula → RawFormula → RawFormula

    negationClosed :
      (φ : RawFormula) → Closed φ → Closed (NegationRaw φ)
    implicationClosed :
      (φ ψ : RawFormula) → Closed φ → Closed ψ →
      Closed (ImplicationRaw φ ψ)
    biconditionalClosed :
      (φ ψ : RawFormula) → Closed φ → Closed ψ →
      Closed (BiconditionalRaw φ ψ)

    consistencyRaw : RawFormula
    consistencyClosed : Closed consistencyRaw

open ExternalArithmeticSource public

record RestrictedUnary
    (S : ExternalArithmeticSource) : Set where
  constructor restrictedUnary
  field
    rawUnary : RawFormula S
    unaryOK : UnaryAdmissible S rawUnary

open RestrictedUnary public

record RestrictedBinary
    (S : ExternalArithmeticSource) : Set where
  constructor restrictedBinary
  field
    rawBinary : RawFormula S
    binaryOK : BinaryAdmissible S rawBinary

open RestrictedBinary public

record RestrictedSentence
    (S : ExternalArithmeticSource) : Set where
  constructor restrictedSentence
  field
    rawSentence : RawFormula S
    closedOK : Closed S rawSentence

open RestrictedSentence public

record RestrictedProof
    (S : ExternalArithmeticSource) : Set where
  constructor restrictedProof
  field
    provedRaw : RawFormula S
    sourceDerivation : RawDeriv S provedRaw

open RestrictedProof public

------------------------------------------------------------------------
-- Compiler to the existing DASHI abstract formal-system ABI.
------------------------------------------------------------------------

compileExternalArithmeticSystem :
  ExternalArithmeticSource → Godel.ArithmetisedFormalSystem
compileExternalArithmeticSystem S =
  record
    { Term = Term S
    ; Formula = RestrictedUnary S
    ; BinaryFormula = RestrictedBinary S
    ; Sentence = RestrictedSentence S
    ; Proof = RestrictedProof S

    ; codeTerm = codeTerm S
    ; codeFormula = λ φ → codeFormula S (rawUnary φ)
    ; codeBinaryFormula = λ φ → codeFormula S (rawBinary φ)
    ; codeSentence = λ φ → codeFormula S (rawSentence φ)
    ; codeProof = λ p → codeFormula S (provedRaw p)

    ; numeral = numeral S
    ; instantiate = λ φ t →
        restrictedSentence
          (instantiateUnaryRaw S (rawUnary φ) t)
          (unaryInstantiationClosed S (rawUnary φ) (unaryOK φ) t)
    ; instantiate2 = λ φ s t →
        restrictedSentence
          (instantiateBinaryRaw S (rawBinary φ) s t)
          (binaryInstantiationClosed S (rawBinary φ) (binaryOK φ) s t)

    ; Provable = λ φ → RawDeriv S (rawSentence φ)
    ; proves = λ p φ → provedRaw p ≡ rawSentence φ

    ; Negation = λ φ →
        restrictedSentence
          (NegationRaw S (rawSentence φ))
          (negationClosed S (rawSentence φ) (closedOK φ))
    ; Implication = λ φ ψ →
        restrictedSentence
          (ImplicationRaw S (rawSentence φ) (rawSentence ψ))
          (implicationClosed S
            (rawSentence φ) (rawSentence ψ)
            (closedOK φ) (closedOK ψ))
    ; Biconditional = λ φ ψ →
        restrictedSentence
          (BiconditionalRaw S (rawSentence φ) (rawSentence ψ))
          (biconditionalClosed S
            (rawSentence φ) (rawSentence ψ)
            (closedOK φ) (closedOK ψ))
    ; ConsistencySentence =
        restrictedSentence (consistencyRaw S) (consistencyClosed S)
    }

compileExternalShapeAuthority :
  (S : ExternalArithmeticSource) →
  Shape.FormulaSentenceShapeAuthority (compileExternalArithmeticSystem S)
compileExternalShapeAuthority S =
  record
    { Variable = Variable S
    ; distinguishedUnary = distinguishedUnary S
    ; distinguishedBinaryLeft = distinguishedBinaryLeft S
    ; distinguishedBinaryRight = distinguishedBinaryRight S
    ; FreeInUnary = λ v φ → FreeIn S v (rawUnary φ)
    ; FreeInBinary = λ v φ → FreeIn S v (rawBinary φ)
    ; unaryHasNoOtherFreeVariable = λ v φ evidence →
        unaryFreeOnly S (rawUnary φ) (unaryOK φ) v evidence
    ; binaryHasNoOtherFreeVariable = λ v φ evidence →
        binaryFreeOnly S (rawBinary φ) (binaryOK φ) v evidence
    ; binaryDistinguishedVariablesDistinct = binaryVariablesDistinct S
    }

------------------------------------------------------------------------
-- Source substitution is deliberately a SECOND coordinate.  Merely compiling
-- the syntax/provability ABI does not create an arithmetised substitution law.
------------------------------------------------------------------------

record ExternalArithmetisedSubstitution
    (S : ExternalArithmeticSource) : Set₁ where
  field
    substituteCodeRaw : Nat → Nat → Nat
    substituteCodeExact :
      (φ : RestrictedUnary S) → (n : Nat) →
      substituteCodeRaw (codeFormula S (rawUnary φ)) n
      ≡ codeFormula S
          (instantiateUnaryRaw S (rawUnary φ) (numeral S n))

open ExternalArithmetisedSubstitution public

compileExternalArithmetisedSubstitution :
  (S : ExternalArithmeticSource) →
  ExternalArithmetisedSubstitution S →
  Godel.ArithmetisedSubstitution (compileExternalArithmeticSystem S)
compileExternalArithmetisedSubstitution S A =
  record
    { substituteCode = substituteCodeRaw A
    ; substitutionExact = substituteCodeExact A
    }

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RawFormulaAliasSuppliesUnaryShape : Set where
data IndexedDerivationSuppliesClosedSentenceShape : Set where
data SyntaxCompilerSuppliesSubstitutionExactness : Set where
data ExternalTheoremNameSuppliesLocalTheorem : Set where

rawAliasDoesNotSupplyShape : RawFormulaAliasSuppliesUnaryShape → ⊥
rawAliasDoesNotSupplyShape ()

derivationDoesNotSupplySentenceShape :
  IndexedDerivationSuppliesClosedSentenceShape → ⊥
derivationDoesNotSupplySentenceShape ()

syntaxCompilerDoesNotSupplySubstitution :
  SyntaxCompilerSuppliesSubstitutionExactness → ⊥
syntaxCompilerDoesNotSupplySubstitution ()

externalNameDoesNotSupplyTheorem : ExternalTheoremNameSuppliesLocalTheorem → ⊥
externalNameDoesNotSupplyTheorem ()

record ExternalArithmeticABICompilerBoundary : Set where
  constructor externalArithmeticABICompilerBoundary
  field
    restrictedUnaryCarrierCompilerOwned : Bool
    restrictedBinaryCarrierCompilerOwned : Bool
    restrictedSentenceCarrierCompilerOwned : Bool
    sourceFreeVariableRelationRetained : Bool
    shapeAuthorityCompiledFromSourceProofs : Bool
    indexedDerivationProjectionOwned : Bool
    substitutionCompiledOnlyFromExactSourceLaw : Bool
    rawFormulaAliasesAcceptedAsShapeEvidence : Bool
    externalTheoremsImportedByName : Bool

canonicalExternalArithmeticABICompilerBoundary :
  ExternalArithmeticABICompilerBoundary
canonicalExternalArithmeticABICompilerBoundary =
  externalArithmeticABICompilerBoundary
    true true true true true true true false false
