module DASHI.Physics.Closure.W3SurrogateEmpiricalTargetBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String; primStringEquality)
open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.Chi2CanonicalPoolObservationCandidate as CHI2POOL
open import DASHI.Physics.Closure.Chi2ToShiftPressureTransportCandidate as CHI2SHIFT
open import DASHI.Physics.Closure.Chi2TransportDynamicsToFixedPointBridge as CHI2DYN
open import DASHI.Physics.Closure.MinimalCredibleShiftOriginObservation as ORIGIN
open import DASHI.Physics.Closure.P0BlockadeProofObligations as P0
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.Closure.Validation.Chi2BoundaryShiftLibrary as LIB
open import DASHI.Physics.Closure.Validation.RootSystemB4PromotionBridge as B4PB
open import DASHI.Physics.Closure.Validation.RootSystemB4ShellComparison as B4C
open import DASHI.Physics.Closure.W3EmpiricalTargetPromotionBridgeObligation as W3

------------------------------------------------------------------------
-- W3 surrogate empirical-target boundary.
--
-- This module tests only structural inhabitance of the W3 target/promotion
-- shape.  The target below is synthetic Nat data over the local chi2 pool and
-- transported shift-pressure carrier; it is not accepted empirical adequacy,
-- and it does not promote B4 or origin observation.

chi2BoundaryLabelSurrogateObservation :
  LIB.Chi2BoundaryCase →
  Nat
chi2BoundaryLabelSurrogateObservation boundary =
  if primStringEquality (LIB.Chi2BoundaryCase.label boundary) "tail-alt-signs"
  then zero
  else
    if primStringEquality (LIB.Chi2BoundaryCase.label boundary) "tail-block-signs"
    then suc zero
    else suc (suc zero)

shiftPressureSurrogateObservation :
  SPTI.ShiftPressurePoint →
  Nat
shiftPressureSurrogateObservation SPTI.shiftStartPoint = zero
shiftPressureSurrogateObservation SPTI.shiftNextPoint = suc zero
shiftPressureSurrogateObservation SPTI.shiftHeldExitPoint = suc (suc zero)

surrogateEmpiricalTarget :
  Nat
surrogateEmpiricalTarget =
  suc (suc zero)

primarySecondarySurrogateDistinct :
  CHI2POOL.chi2PoolObservation CHI2POOL.primaryPoolCase
    P0.≢
  CHI2POOL.chi2PoolObservation CHI2POOL.secondaryPoolCase
primarySecondarySurrogateDistinct ()

primaryTertiarySurrogateDistinct :
  CHI2POOL.chi2PoolObservation CHI2POOL.primaryPoolCase
    P0.≢
  CHI2POOL.chi2PoolObservation CHI2POOL.tertiaryPoolCase
primaryTertiarySurrogateDistinct ()

secondaryTertiarySurrogateDistinct :
  CHI2POOL.chi2PoolObservation CHI2POOL.secondaryPoolCase
    P0.≢
  CHI2POOL.chi2PoolObservation CHI2POOL.tertiaryPoolCase
secondaryTertiarySurrogateDistinct ()

poolObservationFactorsThroughBoundarySurrogate :
  (case : CHI2POOL.CanonicalChi2PoolCase) →
  CHI2POOL.chi2PoolObservation case
  ≡
  chi2BoundaryLabelSurrogateObservation
    (CHI2POOL.poolCaseToBoundaryCase case)
poolObservationFactorsThroughBoundarySurrogate CHI2POOL.primaryPoolCase = refl
poolObservationFactorsThroughBoundarySurrogate CHI2POOL.secondaryPoolCase = refl
poolObservationFactorsThroughBoundarySurrogate CHI2POOL.tertiaryPoolCase = refl

transportedPoolObservationPreservedSurrogate :
  (case : CHI2POOL.CanonicalChi2PoolCase) →
  shiftPressureSurrogateObservation
    (CHI2SHIFT.chi2PoolToShiftPressurePoint case)
  ≡
  CHI2POOL.chi2PoolObservation case
transportedPoolObservationPreservedSurrogate CHI2POOL.primaryPoolCase = refl
transportedPoolObservationPreservedSurrogate CHI2POOL.secondaryPoolCase = refl
transportedPoolObservationPreservedSurrogate CHI2POOL.tertiaryPoolCase = refl

w3SurrogateEmpiricalObservationTarget :
  W3.EmpiricalObservationTargetOverTransportedChi2Pool
w3SurrogateEmpiricalObservationTarget =
  record
    { Obs = Nat
    ; empirical = surrogateEmpiricalTarget
    ; boundaryObservation = chi2BoundaryLabelSurrogateObservation
    ; poolObservation = CHI2POOL.chi2PoolObservation
    ; transportedObservation = shiftPressureSurrogateObservation
    ; poolObservationFactorsThroughBoundary =
        poolObservationFactorsThroughBoundarySurrogate
    ; transportedPoolObservationPreserved =
        transportedPoolObservationPreservedSurrogate
    ; primarySecondaryEmpiricallyDistinct =
        primarySecondarySurrogateDistinct
    ; primaryTertiaryEmpiricallyDistinct =
        primaryTertiarySurrogateDistinct
    ; secondaryTertiaryEmpiricallyDistinct =
        secondaryTertiarySurrogateDistinct
    }

w3SurrogateEmpiricalAdequacy :
  P0.EmpiricalAdequacy
    {SPTI.ShiftPressurePoint}
    {Nat}
w3SurrogateEmpiricalAdequacy =
  record
    { fixedPoint = SPTI.shiftHeldExitPoint
    ; obs = shiftPressureSurrogateObservation
    ; empirical = surrogateEmpiricalTarget
    ; matches = refl
    }

localTransportPreservesSurrogateTarget :
  (case : CHI2POOL.CanonicalChi2PoolCase) →
  P0.EmpiricalAdequacy.obs w3SurrogateEmpiricalAdequacy
    (CHI2SHIFT.Chi2ToShiftPressureTransportCandidate.transport
      CHI2SHIFT.canonicalChi2ToShiftPressureTransportCandidate
      case)
  ≡
  CHI2POOL.chi2PoolObservation case
localTransportPreservesSurrogateTarget CHI2POOL.primaryPoolCase = refl
localTransportPreservesSurrogateTarget CHI2POOL.secondaryPoolCase = refl
localTransportPreservesSurrogateTarget CHI2POOL.tertiaryPoolCase = refl

w3SurrogateChi2PromotionBridge :
  W3.Chi2LocalCandidateToEmpiricalAdequacyPromotion
    w3SurrogateEmpiricalObservationTarget
w3SurrogateChi2PromotionBridge =
  record
    { localPoolCandidate =
        CHI2POOL.canonicalChi2PoolObservationCandidate
    ; localTransportCandidate =
        CHI2SHIFT.canonicalChi2ToShiftPressureTransportCandidate
    ; localDynamicsBridge =
        CHI2DYN.canonicalChi2TransportDynamicsToFixedPointBridge
    ; empiricalAdequacy =
        w3SurrogateEmpiricalAdequacy
    ; adequacyFixedPointIsHeld =
        refl
    ; adequacyObservationIsTransportedObservation =
        refl
    ; adequacyEmpiricalIsTarget =
        refl
    ; localTransportPreservesEmpiricalTarget =
        localTransportPreservesSurrogateTarget
    }

data W3SurrogateEmpiricalTargetBoundaryStatus : Set where
  surrogateSyntacticShapeOnly :
    W3SurrogateEmpiricalTargetBoundaryStatus
  notAcceptedEmpiricalAdequacy :
    W3SurrogateEmpiricalTargetBoundaryStatus
  b4EmpiricalPromotionStillBlocked :
    W3SurrogateEmpiricalTargetBoundaryStatus
  originPromotionStillBlocked :
    W3SurrogateEmpiricalTargetBoundaryStatus

record W3SurrogateEmpiricalTargetBoundaryReceipt : Setω where
  field
    target :
      W3.EmpiricalObservationTargetOverTransportedChi2Pool

    chi2PromotionBridge :
      W3.Chi2LocalCandidateToEmpiricalAdequacyPromotion target

    b4ShellReport :
      B4C.B4ShellComparisonReport

    b4StillStandalone :
      B4C.B4ShellComparisonReport.promotionStatus b4ShellReport
      ≡
      B4C.standaloneOnly

    b4ClosureBridgeAlreadyReady :
      B4PB.B4PromotionBridge.promotionStatus B4PB.bridge
      ≡
      B4PB.admissiblePromotionReady

    originObservationReceipt :
      P0.OriginObservationReceipt

    originObservationReceiptBlocked :
      P0.OriginObservationReceipt.empiricalStatus originObservationReceipt
      ≡
      P0.empiricalBlocked

    boundaryStatus :
      List W3SurrogateEmpiricalTargetBoundaryStatus

    boundaryStatement :
      List String

w3SurrogateEmpiricalTargetBoundaryReceipt :
  W3SurrogateEmpiricalTargetBoundaryReceipt
w3SurrogateEmpiricalTargetBoundaryReceipt =
  record
    { target =
        w3SurrogateEmpiricalObservationTarget
    ; chi2PromotionBridge =
        w3SurrogateChi2PromotionBridge
    ; b4ShellReport =
        B4C.report
    ; b4StillStandalone =
        refl
    ; b4ClosureBridgeAlreadyReady =
        refl
    ; originObservationReceipt =
        ORIGIN.minimalCredibleShiftOriginObservationReceipt
    ; originObservationReceiptBlocked =
        refl
    ; boundaryStatus =
        surrogateSyntacticShapeOnly
        ∷ notAcceptedEmpiricalAdequacy
        ∷ b4EmpiricalPromotionStillBlocked
        ∷ originPromotionStillBlocked
        ∷ []
    ; boundaryStatement =
        "Surrogate Nat target inhabits the local W3 chi2 target/promotion shape only"
        ∷ "This is not accepted empirical adequacy and carries no empirical authority"
        ∷ "B4 empirical promotion remains standaloneOnly, not admissibleReady"
        ∷ "Origin observation remains empiricalBlocked; no P0.OriginReceipt is claimed"
        ∷ []
    }
