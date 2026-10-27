{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261005UExact where

------------------------------------------------------------------------
-- OVERLAY U / 2026-10-05: CORRECT R129 COMPOSITE/F^2 FRONTIER.
--
-- Audit correction to Overlay T:
--
-- `R109.completedSources` carries TWO marked source coordinates:
--   * `compositeData` : the generic completed composite coordinate;
--   * `stressData`    : the stress coordinate.
--
-- R129 exports `compositeData`, NOT `stressData`.  Therefore the old S3a
-- equation was not a stress=F^2 conflation.  The highest-alpha route is to
-- REUSE the existing R129 composite marked source (and its already-paid common
-- Hilbert modulus) and prove the remaining same-object semantics:
--
--     selected curvature/F^2 marked source = R129 compositeData.
--
-- A separately constructed F^2 marked source remains a valid fallback, but it
-- would repay marked-source/Hilbert-modulus data unnecessarily.
--
-- Haar refinement retained from T: exact cell Haar masses make the mass-
-- discrepancy budget zero.  Only shrinking-cell oscillation remains.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyP1PreferredPathDefinedPresentCutExact as P1
import DASHI.Physics.Foundations.CMP119CosmologyP2RenormalizedHilbertWardAuthorityExact as P2
import DASHI.Physics.Foundations.CMP119CosmologyP3R129RechartedLocalCF2Exact as P3R129
import DASHI.Physics.Foundations.CMP119CosmologyP3ApproximateExpectationHaarExact as P3Limit
import DASHI.Physics.YangMills.BalabanCompactHaarExactMassQuadratureExact as ExactMass
import DASHI.Physics.YangMills.YMClayLevel2SameFamilyStressRecoveryExact as Recovery

------------------------------------------------------------------------
-- Exact remaining frontier.
------------------------------------------------------------------------

remainingNovelSourceConstructionCount : Nat
remainingNovelSourceConstructionCount = 3

remainingStandardImportedAuthorityCount : Nat
remainingStandardImportedAuthorityCount = 1

-- U1: actual compact-gauge/B4 path on the literal CMP109/116 Background.
actualCMP109116BackgroundPathConstructionRequired : Bool
actualCMP109116BackgroundPathConstructionRequired =
  P1.remainingQ1LeafIsActualB4EquivariantSourcePath

-- U2: renormalized Hilbert/Weyl trace-anomaly Ward identity on the exact pair.
renormalizedHilbertWeylWardAuthorityRequired : Bool
renormalizedHilbertWeylWardAuthorityRequired =
  P2.remainingR2WorkIsInstantiationOfStandardWardAuthority

-- U3: same-object meaning of the ALREADY completed generic R129 composite.
r129F2TargetIsGenericCompositeData : Bool
r129F2TargetIsGenericCompositeData = true

r129F2TargetIsStressDataProjection : Bool
r129F2TargetIsStressDataProjection = false

preferredF2RouteReusesR129CompositeHilbertModulus : Bool
preferredF2RouteReusesR129CompositeHilbertModulus = true

r129CompositeToSelectedF2SemanticsRequired : Bool
r129CompositeToSelectedF2SemanticsRequired =
  P3R129.onlyR129MarkedSourceSelectionRemainsInSameCarrierAttachment

separatePhysicalF2MarkedSourceConstructionPreferred : Bool
separatePhysicalF2MarkedSourceConstructionPreferred = false

-- U4: product-Haar finite approximation.  Exact masses remove discrepancy.
productHaarShrinkingCellOscillationRequired : Bool
productHaarShrinkingCellOscillationRequired = true

independentHaarMassDiscrepancyRequired : Bool
independentHaarMassDiscrepancyRequired =
  ExactMass.independentMassDiscrepancyEstimateRequired

commonLimitAfterHaarApproximationIsCompilerOwned : Bool
commonLimitAfterHaarApproximationIsCompilerOwned =
  P3Limit.compiledCommonLimitNeedsNoPointwiseSourceWeld

------------------------------------------------------------------------
-- Accounting / retired debt.
------------------------------------------------------------------------

primitiveSignedCovarianceRequired : Bool
primitiveSignedCovarianceRequired = false

freeTraceFrameCalibrationRequired : Bool
freeTraceFrameCalibrationRequired = false

finiteDGammaR109TailRouteRequired : Bool
finiteDGammaR109TailRouteRequired = false

eq223VacuumGapRouteRequired : Bool
eq223VacuumGapRouteRequired = false

remainingAdapterDebt : Nat
remainingAdapterDebt = 0

noSyntheticPhysicalIdentificationAdded : Bool
noSyntheticPhysicalIdentificationAdded = true
