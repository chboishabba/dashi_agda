{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R343ToR396SourceNativeRound397Exact where

------------------------------------------------------------------------
-- ROUND397 / R343 -> R395/R396 SOURCE-NATIVE COMPATIBILITY
--
-- Archaeology found that the mature R343 producer already stores exactly the
-- application coordinates now exposed separately by R395/R396:
--
--   * selected sourceEnvelope = owned source shell at the same distance;
--   * selected sourceDistance = spectral time (stronger than time<=distance);
--   * a SourceExponentialShellMajorant whose criterion retains the ACTUAL
--     source per-shell decay q and only additionally proves q<=1/2.
--
-- R395 deliberately forgets the stronger dyadic criterion while preserving
-- that same q. Therefore an R343 producer can inhabit the current R396
-- application interface mechanically. No new localization, geometry, or
-- decay estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
import Data.Nat.Base as Nat
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116DyadicEnvelopeCalibrationRound343Exact as R343
import DASHI.Physics.YangMills.BalabanSourceNativeGeometricMajorantRound395Exact as R395
import DASHI.Physics.YangMills.BalabanSelectedSourceNativeMajorantRound396Exact as R396

r343SourceNativeMajorant :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  R343.DyadicLiteralTrajectoryCMP116Source
    base demands tests spectrumSource →
  R395.SourceNativeGeometricMajorant
r343SourceNativeMajorant source =
  R395.fromDyadicMajorant (R343.dyadicMajorant source)

r343AsR396Application :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  (source : R343.DyadicLiteralTrajectoryCMP116Source
    base demands tests spectrumSource) →
  R396.SelectedSourceNativeMajorantApplication
    (R343.asLiteralTrajectoryCMP116Source source)
    (r343SourceNativeMajorant source)
r343AsR396Application source = record
  { R396.SelectedSourceNativeMajorantApplication.selectedSourceEnvelopeIsMajorantShell =
      R343.selectedSourceEnvelopeIsDyadicShell source
  ; R396.SelectedSourceNativeMajorantApplication.selectedTimeBelowSourceDistance =
      λ observable time →
        subst
          (λ distance → time Nat.≤ distance)
          (sym (R343.selectedSourceDistanceIsTime source observable time))
          Nat.≤-refl
  }

------------------------------------------------------------------------
-- Pareto / authority boundary.
--
-- This adapter proves that the mature R343 producer already pays the current
-- R396 attachment and one-sided geometry coordinates FOR THAT PRODUCER. R343
-- itself still carries physical/source fields whose inhabitants are not created
-- here. The weaker R395/R396 ABI remains preferred architecture because a new
-- source producer need not prove q<=1/2 or distance=time.
------------------------------------------------------------------------

round397R343ToR396CompilerLevel : ProofLevel
round397R343ToR396CompilerLevel = machineChecked

r343ToR396CompilerOwned : Bool
r343ToR396CompilerOwned = true

r343RoutePreservesSourceNativeRatio : Bool
r343RoutePreservesSourceNativeRatio = true

r343RoutePaysSelectedEnvelopeShellAttachment : Bool
r343RoutePaysSelectedEnvelopeShellAttachment = true

r343RoutePaysOneSidedGeometry : Bool
r343RoutePaysOneSidedGeometry = true

r343RouteMandatoryArchitecture : Bool
r343RouteMandatoryArchitecture = false

clayPromotion : Bool
clayPromotion = false
