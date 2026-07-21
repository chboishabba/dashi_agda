module DASHI.Physics.Closure.NSCompactGammaNearTriadAbsorptionReduction where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaNearTriadRouteDecision as Route
import DASHI.Physics.Closure.NSCompactGammaConcreteDyadicScalarCertificate as Dyadic

------------------------------------------------------------------------
-- Exact reduction of the viable near-triad target
--
--   |Qnear| <= delta D + Cdelta E
--
-- to a literal Fourier expansion, a three-way paraproduct split, three local
-- product/Young bounds, and one finite scalar regrouping inequality.  The only
-- non-algebraic leaves are the displayed Fourier estimates themselves.
------------------------------------------------------------------------

additionMonotoneBothA :
  (A : AbsorptionArithmetic) →
  ∀ {a a′ b b′} →
  _≤_ A a a′ → _≤_ A b b′ →
  _≤_ A (_+_ A a b) (_+_ A a′ b′)
additionMonotoneBothA A p q =
  ≤-trans A
    (additionMonotoneRight A p)
    (additionMonotoneLeft A q)

record NearTriadParaproductReduction
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    Time : Set i

    literalFourierMagnitude nearTriadMagnitude : Index → Time → Scalar A
    nearLowHigh nearHighLow nearHighHigh : Index → Time → Scalar A

    deltaLowHigh deltaHighLow deltaHighHigh : Index → Time → Scalar A
    residualLowHigh residualHighLow residualHighHigh :
      Index → Time → Scalar A

    deltaDissipation residualEnvelope : Index → Time → Scalar A

    nearTriadLiteralFourierExpansion : ∀ q τ →
      nearTriadMagnitude q τ ≡ literalFourierMagnitude q τ

    nearTriadParaproductSplit : ∀ q τ →
      _≤_ A
        (nearTriadMagnitude q τ)
        (_+_ A
          (nearLowHigh q τ)
          (_+_ A (nearHighLow q τ) (nearHighHigh q τ)))

    nearLowHighProductBound : ∀ q τ →
      _≤_ A
        (nearLowHigh q τ)
        (_+_ A (deltaLowHigh q τ) (residualLowHigh q τ))

    nearHighLowProductBound : ∀ q τ →
      _≤_ A
        (nearHighLow q τ)
        (_+_ A (deltaHighLow q τ) (residualHighLow q τ))

    nearHighHighProductBound : ∀ q τ →
      _≤_ A
        (nearHighHigh q τ)
        (_+_ A (deltaHighHigh q τ) (residualHighHigh q τ))

    -- Finite scalar bookkeeping after the three Young inequalities.  This is
    -- where the selected delta shares and Cdelta residuals are checked against
    -- the common dissipative and envelope budgets.
    componentYoungPaymentsFitBudget : ∀ q τ →
      _≤_ A
        (_+_ A
          (_+_ A (deltaLowHigh q τ) (residualLowHigh q τ))
          (_+_ A
            (_+_ A (deltaHighLow q τ) (residualHighLow q τ))
            (_+_ A (deltaHighHigh q τ) (residualHighHigh q τ))))
        (_+_ A (deltaDissipation q τ) (residualEnvelope q τ))

open NearTriadParaproductReduction public

threeParaproductBoundsAssemble :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (P : NearTriadParaproductReduction A Index) → ∀ q τ →
  _≤_ A
    (_+_ A
      (nearLowHigh P q τ)
      (_+_ A (nearHighLow P q τ) (nearHighHigh P q τ)))
    (_+_ A
      (_+_ A (deltaLowHigh P q τ) (residualLowHigh P q τ))
      (_+_ A
        (_+_ A (deltaHighLow P q τ) (residualHighLow P q τ))
        (_+_ A (deltaHighHigh P q τ) (residualHighHigh P q τ))))
threeParaproductBoundsAssemble {A = A} P q τ =
  additionMonotoneBothA A
    (nearLowHighProductBound P q τ)
    (additionMonotoneBothA A
      (nearHighLowProductBound P q τ)
      (nearHighHighProductBound P q τ))

youngAbsorbsNearTriad :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (P : NearTriadParaproductReduction A Index) → ∀ q τ →
  _≤_ A
    (nearTriadMagnitude P q τ)
    (_+_ A (deltaDissipation P q τ) (residualEnvelope P q τ))
youngAbsorbsNearTriad {A = A} P q τ =
  ≤-trans A
    (nearTriadParaproductSplit P q τ)
    (≤-trans A
      (threeParaproductBoundsAssemble P q τ)
      (componentYoungPaymentsFitBudget P q τ))

------------------------------------------------------------------------
-- Route constructor.  The exact raw Route-B inequality remains tied to the
-- same magnitude, delta and residual objects used by the paraproduct reduction.
------------------------------------------------------------------------

record NearTriadRouteSkeleton
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (P : NearTriadParaproductReduction A Index) : Set (lsuc i) where
  field
    gammaPotentialDerivative gammaDissipation gammaForcing :
      Index → Time P → Scalar A
    weightedFiveHalvesRate farTailPayment : Index → Time P → Scalar A

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
            (residualEnvelope P q τ))
          (farTailPayment q τ))

open NearTriadRouteSkeleton public

paraproductReductionToDissipativeAbsorption :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (P : NearTriadParaproductReduction A Index) →
  NearTriadRouteSkeleton A Index P →
  Route.NearTriadDissipativeAbsorption A Index
paraproductReductionToDissipativeAbsorption P S = record
  { Time = Time P
  ; gammaPotentialDerivative = gammaPotentialDerivative S
  ; gammaDissipation = gammaDissipation S
  ; gammaForcing = gammaForcing S
  ; weightedFiveHalvesRate = weightedFiveHalvesRate S
  ; nearTriadMagnitude = nearTriadMagnitude P
  ; deltaDissipation = deltaDissipation P
  ; residualEnvelope = residualEnvelope P
  ; farTailPayment = farTailPayment S
  ; nearTriadAbsorptionEstimate = youngAbsorbsNearTriad P
  ; rawAbsorbedNearTailInequality = rawAbsorbedNearTailInequality S
  }

------------------------------------------------------------------------
-- Coherent official owner: paraproduct leaves, Route-B skeleton, positive base
-- coefficient and exact dyadic interpretation are selected together.
------------------------------------------------------------------------

record ConcreteAbsorbedGammaRoute
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    paraproduct : NearTriadParaproductReduction A Index
    skeleton : NearTriadRouteSkeleton A Index paraproduct

    _·_ : Scalar A → Scalar A → Scalar A
    interpretDyadic : Nat → Scalar A
    baseWeightedCoefficient : Scalar A
    Positive : Scalar A → Set i
    positiveDissipativeTerm :
      Index → Time paraproduct → Scalar A

    baseWeightedCoefficientMeaning :
      baseWeightedCoefficient ≡
      interpretDyadic Dyadic.baseWeightedCoefficient

    baseWeightedCoefficientPositive :
      Positive baseWeightedCoefficient

    baseWeightedCoefficientProducesRate : ∀ q τ →
      _≤_ A
        (_·_ baseWeightedCoefficient
          (weightedFiveHalvesRate skeleton q τ))
        (positiveDissipativeTerm q τ)

open ConcreteAbsorbedGammaRoute public

concreteAbsorbedGammaRoute :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  ConcreteAbsorbedGammaRoute A Index →
  Route.AbsorbedGammaRoute A Index
concreteAbsorbedGammaRoute C = record
  { absorption =
      paraproductReductionToDissipativeAbsorption
        (paraproduct C) (skeleton C)
  ; _·_ = _·_ C
  ; interpretDyadic = interpretDyadic C
  ; baseWeightedCoefficient = baseWeightedCoefficient C
  ; Positive = Positive C
  ; positiveDissipativeTerm = positiveDissipativeTerm C
  ; baseWeightedCoefficientMeaning = baseWeightedCoefficientMeaning C
  ; baseWeightedCoefficientPositive = baseWeightedCoefficientPositive C
  ; baseWeightedCoefficientProducesRate =
      baseWeightedCoefficientProducesRate C
  }
