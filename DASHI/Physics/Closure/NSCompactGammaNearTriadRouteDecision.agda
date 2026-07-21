module DASHI.Physics.Closure.NSCompactGammaNearTriadRouteDecision where

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption

------------------------------------------------------------------------
-- The near-triad term is cubic in the Fourier amplitudes.  A global positive
-- lower bound is therefore unavailable on any admissible cone which is closed
-- under the sign reversal carrying the cubic form to its negative while leaving
-- the five-halves rate positive.  This file records that obstruction as an
-- actual theorem and exposes the mathematically viable replacement:
--
--   |Qnear| <= delta D + Cdelta E.
--
-- The periodic Fourier estimate supplying that inequality remains the only PDE
-- leaf; no signed coercivity is silently assumed by the downstream producer.
------------------------------------------------------------------------

record ReversalClosedSignedGainObstruction (i : Level) : Set (lsuc i) where
  field
    State : Set i
    reverse : State → State

    Admissible : State → Set i
    WeightedRatePositive : State → Set i
    NearGainPositive : State → Set i
    NearGainNonpositive : State → Set i

    witness : State
    witnessAdmissible : Admissible witness
    witnessRatePositive : WeightedRatePositive witness

    reversePreservesAdmissibility : ∀ z → Admissible z → Admissible (reverse z)
    reversePreservesRatePositivity :
      ∀ z → WeightedRatePositive z → WeightedRatePositive (reverse z)

    -- Exact oddness consequence for the cubic near-triad form.
    reversalMakesGainNonpositive :
      ∀ z → Admissible z → WeightedRatePositive z →
      NearGainNonpositive (reverse z)

    positiveAndNonpositiveContradict :
      ∀ z → NearGainPositive z → NearGainNonpositive z → ⊥

open ReversalClosedSignedGainObstruction public

UniversalSignedNearCoercivity :
  ∀ {i} → ReversalClosedSignedGainObstruction i → Set i
UniversalSignedNearCoercivity O =
  ∀ z → Admissible O z → WeightedRatePositive O z → NearGainPositive O z

signedNearCoercivityImpossibleOnReversalClosedCone :
  ∀ {i} (O : ReversalClosedSignedGainObstruction i) →
  UniversalSignedNearCoercivity O → ⊥
signedNearCoercivityImpossibleOnReversalClosedCone O coercive =
  positiveAndNonpositiveContradict O (reverse O (witness O))
    (coercive
      (reverse O (witness O))
      (reversePreservesAdmissibility O
        (witness O)
        (witnessAdmissible O))
      (reversePreservesRatePositivity O
        (witness O)
        (witnessRatePositive O)))
    (reversalMakesGainNonpositive O
      (witness O)
      (witnessAdmissible O)
      (witnessRatePositive O))

------------------------------------------------------------------------
-- Absorption route.
------------------------------------------------------------------------

record NearTriadDissipativeAbsorption
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    Time : Set i

    gammaPotentialDerivative gammaDissipation gammaForcing :
      Index → Time → Scalar A
    weightedFiveHalvesRate nearTriadMagnitude : Index → Time → Scalar A
    deltaDissipation residualEnvelope farTailPayment :
      Index → Time → Scalar A

    -- The actual local Fourier target replacing the false signed lower bound.
    nearTriadAbsorptionEstimate : ∀ q τ →
      _≤_ A
        (nearTriadMagnitude q τ)
        (_+_ A (deltaDissipation q τ) (residualEnvelope q τ))

    -- Route-B differential inequality before cancelling the identical tail.
    rawAbsorbedNearTailInequality : ∀ q τ →
      _≤_ A
        (_+_ A
          (_+_ A
            (gammaPotentialDerivative q τ)
            (weightedFiveHalvesRate q τ))
          (farTailPayment q τ))
        (_+_ A
          (_+_ A
            (_+_ A
              (gammaDissipation q τ)
              (gammaForcing q τ))
            (residualEnvelope q τ))
          (farTailPayment q τ))

open NearTriadDissipativeAbsorption public

absorbedNearTailDifferentialInequality :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (D : NearTriadDissipativeAbsorption A Index) → ∀ q τ →
  _≤_ A
    (_+_ A
      (gammaPotentialDerivative D q τ)
      (weightedFiveHalvesRate D q τ))
    (_+_ A
      (_+_ A
        (gammaDissipation D q τ)
        (gammaForcing D q τ))
      (residualEnvelope D q τ))
absorbedNearTailDifferentialInequality {A = A} D q τ =
  additionCancelRight A (rawAbsorbedNearTailInequality D q τ)

------------------------------------------------------------------------
-- The official replacement owner.  Besides the absorption inequality, it
-- names the positive non-cubic term which produces the weighted rate.  This
-- prevents the old `cNear` name from being reused after signed cubic coercivity
-- has been refuted.
------------------------------------------------------------------------

record AbsorbedGammaRoute
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    absorption : NearTriadDissipativeAbsorption A Index

    _·_ : Scalar A → Scalar A → Scalar A
    baseWeightedCoefficient : Scalar A
    Positive : Scalar A → Set i
    positiveDissipativeTerm :
      Index → Time absorption → Scalar A

    baseWeightedCoefficientPositive :
      Positive baseWeightedCoefficient

    baseWeightedCoefficientProducesRate : ∀ q τ →
      _≤_ A
        (_·_ baseWeightedCoefficient
          (weightedFiveHalvesRate absorption q τ))
        (positiveDissipativeTerm q τ)

open AbsorbedGammaRoute public

absorbedGammaRouteDifferentialInequality :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (R : AbsorbedGammaRoute A Index) → ∀ q τ →
  _≤_ A
    (_+_ A
      (gammaPotentialDerivative (absorption R) q τ)
      (weightedFiveHalvesRate (absorption R) q τ))
    (_+_ A
      (_+_ A
        (gammaDissipation (absorption R) q τ)
        (gammaForcing (absorption R) q τ))
      (residualEnvelope (absorption R) q τ))
absorbedGammaRouteDifferentialInequality R =
  absorbedNearTailDifferentialInequality (absorption R)

baseWeightedCoefficientProducesRateExact :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (R : AbsorbedGammaRoute A Index) → ∀ q τ →
  _≤_ A
    (_·_ R (baseWeightedCoefficient R)
      (weightedFiveHalvesRate (absorption R) q τ))
    (positiveDissipativeTerm R q τ)
baseWeightedCoefficientProducesRateExact =
  baseWeightedCoefficientProducesRate

-- Audit aliases matching the mathematical review.
nearTriadFormCannotBeGloballyCoerciveUnderSignReversal :
  ∀ {i} (O : ReversalClosedSignedGainObstruction i) →
  UniversalSignedNearCoercivity O → ⊥
nearTriadFormCannotBeGloballyCoerciveUnderSignReversal =
  signedNearCoercivityImpossibleOnReversalClosedCone

nearTriadsAbsorbIntoDissipationAndEnvelope :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (D : NearTriadDissipativeAbsorption A Index) → ∀ q τ →
  _≤_ A
    (nearTriadMagnitude D q τ)
    (_+_ A (deltaDissipation D q τ) (residualEnvelope D q τ))
nearTriadsAbsorbIntoDissipationAndEnvelope = nearTriadAbsorptionEstimate
