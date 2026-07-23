module DASHI.Physics.Closure.NSPeriodicCanonicalStrictMarginInterpretation where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicStrictDissipationMargin as Margin
import DASHI.Physics.Closure.NSPeriodicCanonicalStrictMarginCertificate as Canonical
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Interpretation of the exact denominator-eight certificate in the official
-- scalar carrier.
--
-- Once the actual near/far quantities fit the interpreted 1/4, 1/8, 1/8
-- payments, this module constructs the strict-margin ledger automatically.
-- The viscosity split and the positive 1/2 remainder are not restated as free
-- scalar equalities.
------------------------------------------------------------------------

record CanonicalDyadicMarginInterpretation
    (A : AbsorptionArithmetic) : Set₁ where
  field
    interpretDyadic : Nat → Scalar A

    interpretAddition : ∀ m n →
      interpretDyadic (m + n) ≡
      _+_ A (interpretDyadic m) (interpretDyadic n)

    nearTerm farLowTerm farHighTerm : Scalar A

    nearFitsCanonicalQuarter :
      _≤_ A nearTerm
        (interpretDyadic Canonical.canonicalNearPayment)

    farLowFitsCanonicalEighth :
      _≤_ A farLowTerm
        (interpretDyadic Canonical.canonicalFarLowPayment)

    farHighFitsCanonicalEighth :
      _≤_ A farHighTerm
        (interpretDyadic Canonical.canonicalFarHighPayment)

    interpretedMarginNonnegative :
      _≤_ A (zero A)
        (interpretDyadic Canonical.canonicalStrictMargin)

    InterpretedMarginPositive : Set
    interpretedMarginPositive : InterpretedMarginPositive

open CanonicalDyadicMarginInterpretation public

interpretCanonicalTotalPayment :
  ∀ {A : AbsorptionArithmetic} →
  (I : CanonicalDyadicMarginInterpretation A) →
  interpretDyadic I Canonical.canonicalTotalNonlinearPayment
  ≡
  _+_ A
    (_+_ A
      (interpretDyadic I Canonical.canonicalNearPayment)
      (interpretDyadic I Canonical.canonicalFarLowPayment))
    (interpretDyadic I Canonical.canonicalFarHighPayment)
interpretCanonicalTotalPayment {A = A} I =
  trans
    (interpretAddition I
      (Canonical.canonicalNearPayment + Canonical.canonicalFarLowPayment)
      Canonical.canonicalFarHighPayment)
    (cong
      (λ prefix →
        _+_ A prefix
          (interpretDyadic I Canonical.canonicalFarHighPayment))
      (interpretAddition I
        Canonical.canonicalNearPayment
        Canonical.canonicalFarLowPayment))

interpretCanonicalPaymentPlusMargin :
  ∀ {A : AbsorptionArithmetic} →
  (I : CanonicalDyadicMarginInterpretation A) →
  interpretDyadic I
    (Canonical.canonicalTotalNonlinearPayment
      + Canonical.canonicalStrictMargin)
  ≡
  _+_ A
    (_+_ A
      (_+_ A
        (interpretDyadic I Canonical.canonicalNearPayment)
        (interpretDyadic I Canonical.canonicalFarLowPayment))
      (interpretDyadic I Canonical.canonicalFarHighPayment))
    (interpretDyadic I Canonical.canonicalStrictMargin)
interpretCanonicalPaymentPlusMargin {A = A} I =
  trans
    (interpretAddition I
      Canonical.canonicalTotalNonlinearPayment
      Canonical.canonicalStrictMargin)
    (cong
      (λ total →
        _+_ A total
          (interpretDyadic I Canonical.canonicalStrictMargin))
      (interpretCanonicalTotalPayment I))

interpretedViscositySplitsCanonicalPaymentsAndMargin :
  ∀ {A : AbsorptionArithmetic} →
  (I : CanonicalDyadicMarginInterpretation A) →
  interpretDyadic I Canonical.canonicalViscosityBudget
  ≡
  _+_ A
    (_+_ A
      (_+_ A
        (interpretDyadic I Canonical.canonicalNearPayment)
        (interpretDyadic I Canonical.canonicalFarLowPayment))
      (interpretDyadic I Canonical.canonicalFarHighPayment))
    (interpretDyadic I Canonical.canonicalStrictMargin)
interpretedViscositySplitsCanonicalPaymentsAndMargin I =
  trans
    (cong (interpretDyadic I)
      (sym Canonical.canonicalPaymentPlusMarginIsViscosity))
    (interpretCanonicalPaymentPlusMargin I)

canonicalInterpretationToStrictMarginInputs :
  ∀ {A : AbsorptionArithmetic} →
  CanonicalDyadicMarginInterpretation A →
  Margin.PeriodicStrictDissipationMarginInputs A
canonicalInterpretationToStrictMarginInputs {A = A} I = record
  { nearTerm = nearTerm I
  ; farLowTerm = farLowTerm I
  ; farHighTerm = farHighTerm I
  ; nearPayment = interpretDyadic I Canonical.canonicalNearPayment
  ; farLowPayment = interpretDyadic I Canonical.canonicalFarLowPayment
  ; farHighPayment = interpretDyadic I Canonical.canonicalFarHighPayment
  ; strictMargin = interpretDyadic I Canonical.canonicalStrictMargin
  ; viscosityBudget = interpretDyadic I Canonical.canonicalViscosityBudget
  ; nearTermBound = nearFitsCanonicalQuarter I
  ; farLowTermBound = farLowFitsCanonicalEighth I
  ; farHighTermBound = farHighFitsCanonicalEighth I
  ; viscositySplitsPaymentsAndMargin =
      interpretedViscositySplitsCanonicalPaymentsAndMargin I
  ; strictMarginNonnegative = interpretedMarginNonnegative I
  ; StrictMarginPositive = InterpretedMarginPositive I
  ; strictMarginPositive = interpretedMarginPositive I
  }

canonicalInterpretedNonlinearBelowViscosity :
  ∀ {A : AbsorptionArithmetic} →
  (I : CanonicalDyadicMarginInterpretation A) →
  _≤_ A
    (_+_ A
      (_+_ A (nearTerm I) (farLowTerm I))
      (farHighTerm I))
    (interpretDyadic I Canonical.canonicalViscosityBudget)
canonicalInterpretedNonlinearBelowViscosity I =
  Margin.periodicNonlinearBelowViscosity
    (canonicalInterpretationToStrictMarginInputs I)

canonicalInterpretedStrictMarginWitness :
  ∀ {A : AbsorptionArithmetic} →
  (I : CanonicalDyadicMarginInterpretation A) →
  InterpretedMarginPositive I
canonicalInterpretedStrictMarginWitness = interpretedMarginPositive

------------------------------------------------------------------------
-- Status: the exact half-margin certificate is transported into any official
-- additive scalar carrier.  The remaining harmonic leaf is only the three
-- cutoff-uniform fit estimates at 1/4, 1/8, and 1/8.
------------------------------------------------------------------------

canonicalStrictMarginInterpretationLevel : ProofLevel
canonicalStrictMarginInterpretationLevel = machineChecked
