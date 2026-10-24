module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact where

------------------------------------------------------------------------
-- S2b2d1b2 / MINIMAL LIVE R236 REGION PAYMENT
--
-- The exact physical-region pair ledger leaves six signed blocks.  Group them
-- according to whether BOTH incidences are in energy-payable deep regions:
--
--   deep-only:
--     DFL-DFL, DFL-DHH, DHH-DHH
--
--   critical-touching:
--     DFL-Core, DHH-Core, Core-Core.
--
-- A producer pays each deep-only block by E*D currency and proves ONE relative
-- covariance estimate for the signed sum of the three critical-touching blocks:
--
--   CoreTouch <= theta * Q_core + B_core,   theta < 1.
--
-- This is the literal same-object replacement for the historical R590 scalar
-- partition.  It retains the multiplier differences and introduces no fibre
-- cardinality or absolute-value observer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceCriticalRegionLiveExact as RegionLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianCriticalRegionPairBlocksExact as Region
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit

F : C3.RealField _
F = Rational.rationalRealField

module LiveRegionPayment
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Exact = RegionLive.LiveRegion physicalSystem S output

  blocks = Exact.regionBlocks

  deepFarLowFarLowSigned : ℚ
  deepFarLowFarLowSigned =
    0ℚ - Region.deepFarLowDeepFarLow blocks

  deepFarLowDeepHighHighSigned : ℚ
  deepFarLowDeepHighHighSigned =
    0ℚ - Region.deepFarLowDeepHighHigh blocks

  deepHighHighHighHighSigned : ℚ
  deepHighHighHighHighSigned =
    0ℚ - Region.deepHighHighDeepHighHigh blocks

  deepFarLowCoreSigned : ℚ
  deepFarLowCoreSigned =
    0ℚ - Region.deepFarLowCriticalCore blocks

  deepHighHighCoreSigned : ℚ
  deepHighHighCoreSigned =
    0ℚ - Region.deepHighHighCriticalCore blocks

  coreCoreSigned : ℚ
  coreCoreSigned =
    0ℚ - Region.criticalCoreCriticalCore blocks

  deepOnlySigned : ℚ
  deepOnlySigned =
      deepFarLowFarLowSigned
    + deepFarLowDeepHighHighSigned
    + deepHighHighHighHighSigned

  criticalTouchingSigned : ℚ
  criticalTouchingSigned =
      deepFarLowCoreSigned
    + deepHighHighCoreSigned
    + coreCoreSigned

  totalSignedIsDeepPlusCritical :
    ( deepFarLowFarLowSigned
    + deepFarLowDeepHighHighSigned
    + deepFarLowCoreSigned
    + deepHighHighHighHighSigned
    + deepHighHighCoreSigned
    + coreCoreSigned )
    ≡ deepOnlySigned + criticalTouchingSigned
  totalSignedIsDeepPlusCritical =
    solve
      ( deepFarLowFarLowSigned
      ∷ deepFarLowDeepHighHighSigned
      ∷ deepHighHighHighHighSigned
      ∷ deepFarLowCoreSigned
      ∷ deepHighHighCoreSigned
      ∷ coreCoreSigned
      ∷ [])

  ------------------------------------------------------------------------
  -- EXACT PHYSICAL B / original selected critical-touching R236 consumer.
  --
  -- This is the requested *correctly typed* same-carrier bridge:
  --
  --   nu * criticalTouching
  --      = (sum r_tau) W(M,M)
  --        - n [ W(M,commutator) - W(M,tangent) ]
  --        - nu * deepOnly.
  --
  -- The (sum r_tau) self-work is the finite-fibre centering companion.
  -- The deepOnly term is the literal R236 deep-block complement.
  -- This is a quartic covariance identity, not a cubic enstrophy identity
  -- or a cutoff-uniform upper estimate.
  ------------------------------------------------------------------------

  physicalR685RateKernel : ℚ
  physicalR685RateKernel =
    Work.coherentWork (Live.mixed output)
      (Work.fixedOutputCommutator
        S Live.velocity (Audit.projectedNonlinearity Live.system)
        Live.cutoff output)
    - Work.coherentWork (Live.mixed output)
      (Work.fixedOutputDampedTangent
        Live.rho S Live.velocity
        (Audit.projectedNonlinearity Live.system)
        Live.cutoff output)

  physicalRateCenteringCompanion : ℚ
  physicalRateCenteringCompanion =
    Pair.rateSum Live.rate (Live.fibre output)
      * Work.coherentWork (Live.mixed output) (Live.mixed output)

  originalCriticalTouchingIsCorrectedR685Rate :
    Field30.viscosity physicalSystem * criticalTouchingSigned
    ≡
      (physicalRateCenteringCompanion
      - Pair.natAsRational (length (Live.fibre output))
          * physicalR685RateKernel)
      - Field30.viscosity physicalSystem * deepOnlySigned
  originalCriticalTouchingIsCorrectedR685Rate =
    let
      nu = Field30.viscosity physicalSystem
      d = deepOnlySigned
      c = criticalTouchingSigned
      centered = physicalRateCenteringCompanion
      n = Pair.natAsRational (length (Live.fibre output))
      K = physicalR685RateKernel

      totalIsGrouped :
        Live.coherentCovarianceNumerator output
        ≡ nu * (d + c)
      totalIsGrouped =
        trans Exact.liveCovarianceIsSixSignedPhysicalRegionBlocks
          (cong (nu *_) totalSignedIsDeepPlusCritical)

      totalIsRate :
        nu * (d + c) ≡ centered - n * K
      totalIsRate =
        trans (sym totalIsGrouped)
          (Live.covarianceIsCommutatorMinusTangent output)
    in
      trans
        (solve (nu ∷ d ∷ c ∷ []))
        (cong (λ total → total - nu * d) totalIsRate)

  record PhysicalCriticalRegionPayment : Set where
    constructor physical-critical-region-payment
    field
      deepFarLowFarLowBudget
      deepFarLowDeepHighHighBudget
      deepHighHighHighHighBudget : ℚ

      coreCompanionMass coreEDBudget theta : ℚ

      viscosityNN :
        0ℚ ≤ Field30.viscosity physicalSystem

      thetaNN : 0ℚ ≤ theta
      thetaStrictlyBelowOne : theta < 1

      deepFarLowFarLowPaid :
        deepFarLowFarLowSigned
        ≤ deepFarLowFarLowBudget

      deepFarLowDeepHighHighPaid :
        deepFarLowDeepHighHighSigned
        ≤ deepFarLowDeepHighHighBudget

      deepHighHighHighHighPaid :
        deepHighHighHighHighSigned
        ≤ deepHighHighHighHighBudget

      criticalTouchingRelativeCovariance :
        criticalTouchingSigned
        ≤ theta * coreCompanionMass + coreEDBudget

  open PhysicalCriticalRegionPayment public

  deepBudget : PhysicalCriticalRegionPayment → ℚ
  deepBudget P =
      deepFarLowFarLowBudget P
    + deepFarLowDeepHighHighBudget P
    + deepHighHighHighHighBudget P

  fixedOutputBudget : PhysicalCriticalRegionPayment → ℚ
  fixedOutputBudget P =
    Field30.viscosity physicalSystem *
      ( deepBudget P
      + theta P * coreCompanionMass P
      + coreEDBudget P )

  deepOnlyPaid :
    (P : PhysicalCriticalRegionPayment) →
    deepOnlySigned ≤ deepBudget P
  deepOnlyPaid P =
    ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (deepFarLowFarLowPaid P)
        (deepFarLowDeepHighHighPaid P))
      (deepHighHighHighHighPaid P)

  totalSignedPaid :
    (P : PhysicalCriticalRegionPayment) →
    deepOnlySigned + criticalTouchingSigned
    ≤ deepBudget P
      + (theta P * coreCompanionMass P + coreEDBudget P)
  totalSignedPaid P =
    ℚP.+-mono-≤
      (deepOnlyPaid P)
      (criticalTouchingRelativeCovariance P)

  physicalCriticalRegionPaymentClosesFixedOutput :
    (P : PhysicalCriticalRegionPayment) →
    Live.coherentCovarianceNumerator output
    ≤ fixedOutputBudget P
  physicalCriticalRegionPaymentClosesFixedOutput P =
    let
      rawSigned =
        ( deepFarLowFarLowSigned
        + deepFarLowDeepHighHighSigned
        + deepFarLowCoreSigned
        + deepHighHighHighHighSigned
        + deepHighHighCoreSigned
        + coreCoreSigned )

      regrouped :
        rawSigned ≡ deepOnlySigned + criticalTouchingSigned
      regrouped = totalSignedIsDeepPlusCritical

      signedBound :
        rawSigned
        ≤ deepBudget P
          + (theta P * coreCompanionMass P + coreEDBudget P)
      signedBound =
        subst
          (_≤ deepBudget P
            + (theta P * coreCompanionMass P + coreEDBudget P))
          (sym regrouped)
          (totalSignedPaid P)

      scaled =
        let instance nuNN = nonNegative (viscosityNN P)
        in
        ℚP.*-monoˡ-≤-nonNeg
          (Field30.viscosity physicalSystem)
          signedBound

      endpoint :
        Field30.viscosity physicalSystem *
          ( deepBudget P
          + (theta P * coreCompanionMass P + coreEDBudget P))
        ≡ fixedOutputBudget P
      endpoint =
        solve
          ( Field30.viscosity physicalSystem
          ∷ deepBudget P
          ∷ theta P
          ∷ coreCompanionMass P
          ∷ coreEDBudget P
          ∷ [])
    in
    subst
      (_≤ fixedOutputBudget P)
      (sym Exact.liveCovarianceIsSixSignedPhysicalRegionBlocks)
      (subst
        (λ upper →
          Field30.viscosity physicalSystem * rawSigned ≤ upper)
        endpoint
        scaled)

livePhysicalCriticalRegionPaymentCompilerClosed : Bool
livePhysicalCriticalRegionPaymentCompilerClosed = true

liveDeepOnlyRegionPaymentsClosedHere : Bool
liveDeepOnlyRegionPaymentsClosedHere = false

liveCriticalTouchingRelativeCovarianceClosedHere : Bool
liveCriticalTouchingRelativeCovarianceClosedHere = false

liveCriticalRegionPaymentIntroducesFibreCardinality : Bool
liveCriticalRegionPaymentIntroducesFibreCardinality = false

historicalR440CommonCrossRequired : Bool
historicalR440CommonCrossRequired = false

clayPromotion : Bool
clayPromotion = false

livePhysicalCriticalRegionPaymentCompilerClosedIsTrue :
  livePhysicalCriticalRegionPaymentCompilerClosed ≡ true
livePhysicalCriticalRegionPaymentCompilerClosedIsTrue = refl
