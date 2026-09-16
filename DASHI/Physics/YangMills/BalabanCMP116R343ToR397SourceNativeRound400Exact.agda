{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R343ToR397SourceNativeRound400Exact where

------------------------------------------------------------------------
-- ROUND400 / MATURE R343 PRODUCER -> CURRENT ONE-SIDED R397 ABI
--
-- Bookkeeping / compatibility owner.  Authoritative R398 and R399 are the
-- canonical R318 direct-shell construction and selected physical-time lower
-- geometry.  This owner merely records that the stronger historical R343
-- producer, if ever inhabited, compiles into current R397 without replacing
-- its actual source ratio q by 1/2.
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
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
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
  R343.DyadicLiteralTrajectoryCMP116Source base demands tests spectrumSource →
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
r343AsR397Application
    {base = base} {tests = tests} {spectrumSource = spectrumSource} source = record
  { R397.SelectedSourceNativeUpperApplication.selectedSourceEnvelopeBelowMajorantShell =
      λ cutoff observable time →
        let
          index = R281.indexFor spectrumSource observable time
          left = R278.left tests index
          right = R278.right tests index
          leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
          rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
          distance = R343.sourceDistance source leftJ rightJ
          sourceValue = R343.sourceEnvelope source cutoff
            (R343.sourceRoot source cutoff leftJ rightJ) distance
        in
        subst
          (λ shell → sourceValue ≤ shell)
          (R343.selectedSourceEnvelopeIsDyadicShell source cutoff observable time)
          ℚP.≤-refl
  ; R397.SelectedSourceNativeUpperApplication.selectedTimeBelowSourceDistance =
      λ observable time →
        subst
          (λ distance → time Nat.≤ distance)
          (sym (R343.selectedSourceDistanceIsTime source observable time))
          Nat.≤-refl
  }

round400R343ToR397CompilerLevel : ProofLevel
round400R343ToR397CompilerLevel = machineChecked

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
