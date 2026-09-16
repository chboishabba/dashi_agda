{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R343ToR397SourceNativeRound398Exact where

------------------------------------------------------------------------
-- ROUND398 / MATURE R343 PRODUCER -> CURRENT ONE-SIDED R397 ABI
--
-- R397 is the authoritative current selected application interface:
--
--   selected sourceEnvelope <= source-native shell
--   time <= sourceDistance.
--
-- The historical R343 dyadic-calibration producer is stronger. It already
-- stores equality of the selected source envelope with its owned shell and
-- equality of source distance with spectral time. Its shell majorant also
-- retains the ACTUAL source ratio q; q<=1/2 is only an extra historical
-- criterion. R395 forgets that extra criterion while preserving q.
--
-- Therefore every inhabited R343 producer compiles mechanically into R397.
-- This is compatibility archaeology only: it does not inhabit R343's physical
-- source/application fields and does not make the stronger R343 carrier
-- mandatory architecture.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
import Data.Rational.Properties as ℚP
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
import DASHI.Physics.YangMills.BalabanSelectedSourceNativeUpperRound397Exact as R397

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

r343AsR397Application :
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
  R397.SelectedSourceNativeUpperApplication
    (R343.asLiteralTrajectoryCMP116Source source)
    (r343SourceNativeMajorant source)
r343AsR397Application source = record
  { R397.SelectedSourceNativeUpperApplication.selectedSourceEnvelopeBelowMajorantShell =
      λ cutoff observable time →
        subst
          (λ shell →
            R343.sourceEnvelope source cutoff
              (R343.sourceRoot source cutoff
                (DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact.sourceDirectionOf
                  (R318.meaning _)
                  (R278.left _ (R281.indexFor _ observable time)))
                (DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact.sourceDirectionOf
                  (R318.meaning _)
                  (R278.right _ (R281.indexFor _ observable time))))
              (R343.sourceDistance source
                (DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact.sourceDirectionOf
                  (R318.meaning _)
                  (R278.left _ (R281.indexFor _ observable time)))
                (DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact.sourceDirectionOf
                  (R318.meaning _)
                  (R278.right _ (R281.indexFor _ observable time))))
            ≤ shell)
          (R343.selectedSourceEnvelopeIsDyadicShell source cutoff observable time)
          ℚP.≤-refl
  ; R397.SelectedSourceNativeUpperApplication.selectedTimeBelowSourceDistance =
      λ observable time →
        subst
          (λ distance → time Nat.≤ distance)
          (sym (R343.selectedSourceDistanceIsTime source observable time))
          Nat.≤-refl
  }

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round398R343ToR397CompilerLevel : ProofLevel
round398R343ToR397CompilerLevel = machineChecked

r343ToCurrentOneSidedCompilerOwned : Bool
r343ToCurrentOneSidedCompilerOwned = true

r343RoutePreservesActualSourceRatio : Bool
r343RoutePreservesActualSourceRatio = true

r343RoutePaysCurrentAttachmentForItsOwnProducer : Bool
r343RoutePaysCurrentAttachmentForItsOwnProducer = true

r343RoutePaysCurrentGeometryForItsOwnProducer : Bool
r343RoutePaysCurrentGeometryForItsOwnProducer = true

r343ConcreteInhabitantConstructedHere : Bool
r343ConcreteInhabitantConstructedHere = false

r343RouteMandatoryArchitecture : Bool
r343RouteMandatoryArchitecture = false

clayPromotion : Bool
clayPromotion = false
