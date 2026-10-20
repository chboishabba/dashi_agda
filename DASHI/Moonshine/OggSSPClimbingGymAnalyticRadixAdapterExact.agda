module DASHI.Moonshine.OggSSPClimbingGymAnalyticRadixAdapterExact where

------------------------------------------------------------------------
-- SAME-OBJECT ANALYTIC -> RADIX ADAPTER
--
-- Reuse the repository's constructive-real exponential/logarithm carrier and
-- constructed complex exponential (which owns pi).  The current real spine
-- deliberately does not own a floor/fractional-part-to-Fin implementation, so
-- that final quantisation is explicit additional authority rather than a fake
-- theorem.
--
-- Given that authority, this module wires the exact JMD formulas
--
--   x_p(t) = frac(t log p / (2 pi))
--   h_m    = 2 pi m / (p^a log p)
--   v_m    = frac(m / p^a)
--
-- into the existing p-radix wall address and supplies the already-defined
-- WallHeightHoleObserver on the SAME constructive-real carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Foundations.RadixValuationStageBridge as Radix
import DASHI.Moonshine.OggSSPClimbingGymFigureObservationExact as Figure
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- 1. Additional authority not present in the minimal constructive-real spine.
------------------------------------------------------------------------

record AnalyticRadixQuantisationAuthority
  (R : Real.ConstructedOrderedCompleteReal)
  (E : Real.ConstructedRealExponential R)
  (L : Real.ConstructedRealLogarithm R E)
  (CE : Complex.ConstructedComplexExponential R E) : Set₁ where
  field
    natToReal : Nat → Real.Real R
    divide : Real.Real R → Real.Real R → Real.Real R
    fractionalPart : Real.Real R → Real.Real R

    primePositive :
      (prime : Lane.MonsterPrimeLane) →
      Real.Positive E
        (natToReal (Lane.monsterPrimeLaneToNat prime))

    quantizeAddress :
      (form : Gym.WallForm) →
      Real.Real R →
      Radix.RadialTreeAddress
        (Gym.oggPrimeRadixChart (Gym.formLane form))
        (Gym.formExponent form)

    -- Algebraic payment that the analytic hole height lands on the declared
    -- p^a vertex coordinate.  Division cancellation is not silently inferred
    -- from the minimal real record, whose division operation is intentionally
    -- absent.
    holePhaseIdentity :
      (form : Gym.WallForm) →
      (m : Nat) →
      fractionalPart
        (divide
          (Real._*_
            R
            (divide
              (Real._*_
                R
                (Real._*_
                  R
                  (natToReal 2)
                  (Complex.pi CE))
                (natToReal m))
              (Real._*_
                R
                (Real.power E
                  (natToReal
                    (Lane.monsterPrimeLaneToNat (Gym.formLane form)))
                  (Gym.formExponent form))
                (Real.log L
                  (natToReal
                    (Lane.monsterPrimeLaneToNat (Gym.formLane form)))
                  (primePositive (Gym.formLane form)))))
            (Real.log L
              (natToReal
                (Lane.monsterPrimeLaneToNat (Gym.formLane form)))
              (primePositive (Gym.formLane form))))
          (Real._*_
            R
            (natToReal 2)
            (Complex.pi CE))))
      ≡
      fractionalPart
        (divide
          (natToReal m)
          (natToReal (Gym.wallFormN form)))

open AnalyticRadixQuantisationAuthority public

------------------------------------------------------------------------
-- 2. Exact formula compiler on the supplied constructive-real carrier.
------------------------------------------------------------------------

primeReal :
  ∀ {R E L CE} →
  AnalyticRadixQuantisationAuthority R E L CE →
  Gym.WallForm →
  Real.Real R
primeReal authority form =
  natToReal authority
    (Lane.monsterPrimeLaneToNat (Gym.formLane form))

logPrime :
  ∀ {R E L CE} →
  (authority : AnalyticRadixQuantisationAuthority R E L CE) →
  (form : Gym.WallForm) →
  Real.Real R
logPrime {L = L} authority form =
  Real.log L
    (primeReal authority form)
    (primePositive authority (Gym.formLane form))

twoPi :
  ∀ {R E L CE} →
  AnalyticRadixQuantisationAuthority R E L CE →
  Real.Real R
twoPi {R = R} {CE = CE} authority =
  Real._*_ R (natToReal authority 2) (Complex.pi CE)

phaseCoordinate :
  ∀ {R E L CE} →
  (authority : AnalyticRadixQuantisationAuthority R E L CE) →
  (form : Gym.WallForm) →
  Real.Real R →
  Real.Real R
phaseCoordinate {R = R} authority form t =
  fractionalPart authority
    (divide authority
      (Real._*_ R t (logPrime authority form))
      (twoPi authority))

analyticHoleHeight :
  ∀ {R E L CE} →
  (authority : AnalyticRadixQuantisationAuthority R E L CE) →
  (form : Gym.WallForm) →
  Nat →
  Real.Real R
analyticHoleHeight {R = R} {E = E} authority form m =
  divide authority
    (Real._*_ R (twoPi authority) (natToReal authority m))
    (Real._*_ R
      (Real.power E
        (primeReal authority form)
        (Gym.formExponent form))
      (logPrime authority form))

vertexCoordinate :
  ∀ {R E L CE} →
  (authority : AnalyticRadixQuantisationAuthority R E L CE) →
  (form : Gym.WallForm) →
  Nat →
  Real.Real R
vertexCoordinate authority form m =
  fractionalPart authority
    (divide authority
      (natToReal authority m)
      (natToReal authority (Gym.wallFormN form)))

analyticPhaseAddress :
  ∀ {R E L CE} →
  (authority : AnalyticRadixQuantisationAuthority R E L CE) →
  (form : Gym.WallForm) →
  Real.Real R →
  Radix.RadialTreeAddress
    (Gym.oggPrimeRadixChart (Gym.formLane form))
    (Gym.formExponent form)
analyticPhaseAddress authority form t =
  quantizeAddress authority form (phaseCoordinate authority form t)

analyticHoleAddress :
  ∀ {R E L CE} →
  (authority : AnalyticRadixQuantisationAuthority R E L CE) →
  (form : Gym.WallForm) →
  Nat →
  Radix.RadialTreeAddress
    (Gym.oggPrimeRadixChart (Gym.formLane form))
    (Gym.formExponent form)
analyticHoleAddress authority form m =
  quantizeAddress authority form (vertexCoordinate authority form m)

analyticHoleLandsOnDeclaredVertex :
  ∀ {R E L CE}
    (authority : AnalyticRadixQuantisationAuthority R E L CE)
    (form : Gym.WallForm)
    (m : Nat) →
  analyticPhaseAddress authority form (analyticHoleHeight authority form m)
  ≡ analyticHoleAddress authority form m
analyticHoleLandsOnDeclaredVertex authority form m =
  cong (quantizeAddress authority form)
    (holePhaseIdentity authority form m)

------------------------------------------------------------------------
-- 3. Compile into the existing figure-facing observer socket.
------------------------------------------------------------------------

analyticWallObserver :
  ∀ {R E L CE} →
  AnalyticRadixQuantisationAuthority R E L CE →
  (form : Gym.WallForm) →
  Figure.WallHeightHoleObserver form
analyticWallObserver {R = R} authority form = record
  { Height = Real.Real R
  ; phaseAddress = analyticPhaseAddress authority form
  ; holeHeight = analyticHoleHeight authority form
  ; holeAddress = analyticHoleAddress authority form
  ; holeAtDeclaredVertex = analyticHoleLandsOnDeclaredVertex authority form
  ; phaseFormulaLabel = Figure.jmdPhaseFormulaLabel
  ; holeFormulaLabel = Figure.jmdHoleFormulaLabel
  ; spacingFormulaLabel = Figure.jmdHoleSpacingFormulaLabel
  }

------------------------------------------------------------------------
-- 4. Claim boundary.
------------------------------------------------------------------------

record AnalyticRadixAdapterBoundary : Set where
  constructor analytic-radix-adapter-boundary
  field
    analyticLogarithmReused : Bool
    constructedPiReused : Bool
    exactPhaseFormulaWired : Bool
    exactHoleFormulaWired : Bool
    holeVertexIdentityRequired : Bool
    sameRealCarrierFeedsRadixObserver : Bool
    quantisationAuthorityExplicit : Bool
    floorQuantisationConstructedFromCurrentRealSpine : Bool
    analyticAdapterProvesRiemannHypothesis : Bool

open AnalyticRadixAdapterBoundary public

canonicalAnalyticRadixAdapterBoundary : AnalyticRadixAdapterBoundary
canonicalAnalyticRadixAdapterBoundary =
  analytic-radix-adapter-boundary
    true true true true true true true false false
