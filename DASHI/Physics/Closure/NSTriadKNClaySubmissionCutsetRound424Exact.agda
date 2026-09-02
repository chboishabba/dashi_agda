module DASHI.Physics.Closure.NSTriadKNClaySubmissionCutsetRound424Exact where

------------------------------------------------------------------------
-- ROUND424 / CLAY-SUBMISSION CUTSET AFTER THE SAME-OBJECT R423 WELD
--
-- The current BIDI architecture now separates three kinds of remaining work:
--
--   A. ONE Navier--Stokes-specific discovery theorem:
--      cutoff-uniform signed quadratic-companion heat payment on the literal
--      R167 -> R329 -> R299 -> R406 carrier.
--
--   B. Standard finite-dimensional temporal analysis:
--      actual differentiation of the fixed R406 observable plus FTC.  R422
--      has already removed Hermitian calculus, fixed-resolvent scaling and
--      finite summation from this seam.
--
--   C. Standard post-barrier functional analysis:
--      topology realization of the uniform H^(1/2)/H^(3/2) barrier and the
--      three Simon/Sobolev/weak-* source instances isolated by R148/R104.
--
-- This file deliberately does NOT turn B or C into new discovery estimates.
-- It records the shortest proof-producing cutset that a Clay-grade submission
-- still has to instantiate, and prevents the project from counting generic
-- compiler adapters as independent mathematical theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Closure.NSTriadKNQuadraticCompanionSignedHeatToBarrierRound423Exact as R423
import DASHI.Physics.Closure.NSTriadKNR418FinitePairFamilyToR409Round422Exact as R422
import DASHI.Physics.Closure.NSTriadKNCriticalSimonUpgradeFollowsBarrierRound148Exact as R148
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalGalerkinSimonWeldRound104Exact as R104

-- Mathematical-discovery count only.  Routine source/formal-analysis work is
-- tracked separately below.
round424NovelNavierStokesDiscoveryTheoremCount : Nat
round424NovelNavierStokesDiscoveryTheoremCount = suc zero

round424NovelProducerIsSignedQuadraticCompanionPayment : Bool
round424NovelProducerIsSignedQuadraticCompanionPayment =
  R423.round423RemainingNovelProducerIsCutoffUniformSignedCompanionBudget

-- R422 proves all generic derivative assembly; only the actual physical cell
-- curve derivative remains to instantiate on the fixed R406 family.
round424FiniteDerivativeAssemblyAlreadyClosed : Bool
round424FiniteDerivativeAssemblyAlreadyClosed =
  R422.round422FinitePairSummationClosed

round424ActualCellCurveDerivativeStillRequired : Bool
round424ActualCellCurveDerivativeStillRequired =
  R422.round422RemainingTemporalLeafIsActualCellCurveDifferentiation

-- R148 proves no additional NS-specific discovery estimate is required after
-- the A barrier, but the source-level analytic instances are still absent.
round424PostBarrierNeedsNoNewNSDiscoveryEstimate : Bool
round424PostBarrierNeedsNoNewNSDiscoveryEstimate =
  R148.round148NoAdditionalNonlinearDiscoveryEstimateNeededAfterABarrier

round424StandardSimonSourceInstancesInstalled : Bool
round424StandardSimonSourceInstancesInstalled =
  R148.round148AgdaAnalyticSourceInstancesInstalled

round424CriticalBarrierTopologyIsKnownConsumer : Bool
round424CriticalBarrierTopologyIsKnownConsumer =
  R104.round104BarrierTopologyBelongsToUniformCriticalBarrier

-- No Clay promotion until the novel producer and all standard source instances
-- are actually supplied on the same physical Galerkin sequence.
round424ClayPromotion : Bool
round424ClayPromotion = false

round424NovelNavierStokesDiscoveryTheoremCountIsOne :
  round424NovelNavierStokesDiscoveryTheoremCount ≡ suc zero
round424NovelNavierStokesDiscoveryTheoremCountIsOne = refl

round424NovelProducerIsSignedQuadraticCompanionPaymentIsTrue :
  round424NovelProducerIsSignedQuadraticCompanionPayment ≡ true
round424NovelProducerIsSignedQuadraticCompanionPaymentIsTrue = refl

round424PostBarrierNeedsNoNewNSDiscoveryEstimateIsTrue :
  round424PostBarrierNeedsNoNewNSDiscoveryEstimate ≡ true
round424PostBarrierNeedsNoNewNSDiscoveryEstimateIsTrue = refl

round424ClayPromotionIsFalse : round424ClayPromotion ≡ false
round424ClayPromotionIsFalse = refl
