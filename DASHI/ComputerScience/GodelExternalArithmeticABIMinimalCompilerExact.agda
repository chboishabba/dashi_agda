module DASHI.ComputerScience.GodelExternalArithmeticABIMinimalCompilerExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelDiagonalProvabilityContractExact as Godel

------------------------------------------------------------------------
-- MINIMAL EXTERNAL-ARITHMETIC -> DASHI ABI COMPILER
--
-- This is deliberately source-agnostic.  Coquand T4, a Lean arithmetic
-- development, or another machine-checked arithmetic may instantiate this
-- record, but theorem names do not cross the ABI by themselves.
--
-- The important correction is that unary formulas, binary formulas and
-- sentences are RESTRICTED FIBRES of one source formula carrier.  They are not
-- three aliases for the raw source syntax.
------------------------------------------------------------------------

record ExternalArithmeticSource : Set₁ where
  field
    Term : Set
    RawFormula : Set
    Variable : Set

    UnaryAdmissible : RawFormula → Set
    BinaryAdmissible : RawFormula → Set
    Closed : RawFormula → Set

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

-- The proof carrier retains the exact source formula proved by the indexed
-- derivation.  `proves` below then asks that this source formula is exactly the
-- raw formula of the requested closed-sentence fibre.
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
    { Godel.Term = Term S
    ; Godel.Formula = RestrictedUnary S
    ; Godel.BinaryFormula = RestrictedBinary S
    ; Godel.Sentence = RestrictedSentence S
    ; Godel.Proof = RestrictedProof S

    ; Godel.codeTerm = codeTerm S
    ; Godel.codeFormula = λ φ → codeFormula S (rawUnary φ)
    ; Godel.codeBinaryFormula = λ φ → codeFormula S (rawBinary φ)
    ; Godel.codeSentence = λ φ → codeFormula S (rawSentence φ)
    ; Godel.codeProof = λ p → codeFormula S (provedRaw p)

    ; Godel.numeral = numeral S
    ; Godel.instantiate = λ φ t →
        restrictedSentence
          (instantiateUnaryRaw S (rawUnary φ) t)
          (unaryInstantiationClosed S (rawUnary φ) (unaryOK φ) t)
    ; Godel.instantiate2 = λ φ s t →
        restrictedSentence
          (instantiateBinaryRaw S (rawBinary φ) s t)
          (binaryInstantiationClosed S (rawBinary φ) (binaryOK φ) s t)

    ; Godel.Provable = λ φ → RawDeriv S (rawSentence φ)
    ; Godel.proves = λ p φ → provedRaw p ≡ rawSentence φ

    ; Godel.Negation = λ φ →
        restrictedSentence
          (NegationRaw S (rawSentence φ))
          (negationClosed S (rawSentence φ) (closedOK φ))
    ; Godel.Implication = λ φ ψ →
        restrictedSentence
          (ImplicationRaw S (rawSentence φ) (rawSentence ψ))
          (implicationClosed S
            (rawSentence φ) (rawSentence ψ)
            (closedOK φ) (closedOK ψ))
    ; Godel.Biconditional = λ φ ψ →
        restrictedSentence
          (BiconditionalRaw S (rawSentence φ) (rawSentence ψ))
          (biconditionalClosed S
            (rawSentence φ) (rawSentence ψ)
            (closedOK φ) (closedOK ψ))
    ; Godel.ConsistencySentence =
        restrictedSentence (consistencyRaw S) (consistencyClosed S)
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
    { Godel.substituteCode = substituteCodeRaw A
    ; Godel.substitutionExact = substituteCodeExact A
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
    indexedDerivationProjectionOwned : Bool
    substitutionCompiledOnlyFromExactSourceLaw : Bool
    rawFormulaAliasesAcceptedAsShapeEvidence : Bool
    externalTheoremsImportedByName : Bool

canonicalExternalArithmeticABICompilerBoundary :
  ExternalArithmeticABICompilerBoundary
canonicalExternalArithmeticABICompilerBoundary =
  externalArithmeticABICompilerBoundary
    true true true true true false false
