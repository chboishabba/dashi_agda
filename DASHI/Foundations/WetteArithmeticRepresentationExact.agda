{-# OPTIONS --safe #-}
module DASHI.Foundations.WetteArithmeticRepresentationExact where

------------------------------------------------------------------------
-- EDUARD WETTE SOURCE CONTEXT
--
-- Eduard Wette,
-- "Definition eines (relativ vollstaendigen) formalen Systems konstruktiver
-- Arithmetik", in Foundations of Mathematics: Symposium Papers
-- Commemorating the Sixtieth Birthday of Kurt Goedel, pp. 130--195.
--
-- Eduard Wette,
-- "Vom Unendlichen zum Endlichen", Dialectica 24 (1970), 303--324.
--
-- No DOI is asserted here until a stable bibliographic record has been
-- independently verified.  These references identify the historical source
-- family whose representation architecture is being reconstructed.
--
-- DASHI CONTRIBUTION
--
-- This file does not claim that the repository's existing prime-exponent
-- lattice is Wette's literal historical coding.  It packages that existing
-- machinery as a reconstruction target: a finite structured state has a
-- canonical prime-exponent coordinate and an executable scalar Goedel number.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.GodelLattice using (FactorVec)
open import Ontology.GodelScalarization using (G)

------------------------------------------------------------------------
-- Reconstructed arithmetic state.
------------------------------------------------------------------------

record WetteArithmeticState : Set where
  constructor wetteArithmeticState
  field
    factors : FactorVec

open WetteArithmeticState public

wetteNumeral : WetteArithmeticState → Nat
wetteNumeral state = G (factors state)

------------------------------------------------------------------------
-- The representation law is intentionally modest: the scalar numeral is
-- exactly the repository's already-defined prime-power scalarization of the
-- structured exponent state.
------------------------------------------------------------------------

record WetteArithmeticRepresentation : Set₁ where
  field
    State : Set
    structured : State → FactorVec
    numeral : State → Nat
    numeralLaw : (state : State) → numeral state ≡ G (structured state)

open WetteArithmeticRepresentation public

canonicalWetteArithmeticRepresentation : WetteArithmeticRepresentation
canonicalWetteArithmeticRepresentation =
  record
    { State = WetteArithmeticState
    ; structured = factors
    ; numeral = wetteNumeral
    ; numeralLaw = λ _ → refl
    }

canonicalNumeralLaw :
  (state : WetteArithmeticState) →
  wetteNumeral state ≡ G (factors state)
canonicalNumeralLaw _ = refl

------------------------------------------------------------------------
-- Claim boundary.
--
-- Prime-exponent scalarization by itself is an encoding theorem only.  It is
-- not yet a theorem that Wette's deduction relation has been reconstructed,
-- that the scalar numeral is lossless for arbitrary syntax, or that any
-- consistency statement follows from the representation.
------------------------------------------------------------------------

record WetteRepresentationClaimScope : Set where
  constructor wetteRepresentationClaimScope
  field
    primeExponentStateConstructed : Bool
    primeExponentStateConstructedIsTrue :
      primeExponentStateConstructed ≡ true

    executableScalarNumeralConstructed : Bool
    executableScalarNumeralConstructedIsTrue :
      executableScalarNumeralConstructed ≡ true

    historicalWetteCodecRecovered : Bool
    historicalWetteCodecRecoveredIsFalse :
      historicalWetteCodecRecovered ≡ false

    deductionSemanticsRecovered : Bool
    deductionSemanticsRecoveredIsFalse :
      deductionSemanticsRecovered ≡ false

    consistencyConsequenceEstablished : Bool
    consistencyConsequenceEstablishedIsFalse :
      consistencyConsequenceEstablished ≡ false

open import Agda.Builtin.Bool using (Bool; true; false)

canonicalWetteRepresentationClaimScope : WetteRepresentationClaimScope
canonicalWetteRepresentationClaimScope =
  wetteRepresentationClaimScope
    true refl
    true refl
    false refl
    false refl
    false refl
