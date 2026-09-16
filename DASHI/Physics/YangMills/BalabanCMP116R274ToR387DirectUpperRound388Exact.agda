{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R274ToR387DirectUpperRound388Exact where

------------------------------------------------------------------------
-- ROUND388 / ARCHAEOLOGY WELD: R274/R284 -> R387
--
-- R274 already isolated the direct physical theorem:
--
--   finite connected covariance of two literal physical J insertions
--     <= the same rooted connecting-cluster shell at support distance.
--
-- R284 adds only exact selected-pair/time calibration and the standard
-- finite->continuum route.  R387 is the least-privilege terminal ABI on the
-- selected literal mixed-log response.
--
-- This module proves the historical direct producer compiles into R387.  It
-- introduces no new YM estimate and does not make R274 mandatory: any direct
-- producer of the R387 inequality remains admissible.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116DirectT5ContinuumClusteringRound284Exact as R284
import DASHI.Physics.YangMills.BalabanCMP116R281ModeSelectedDirectRound341Exact as R341
import DASHI.Physics.YangMills.BalabanCMP116DirectSelectedSpectralUpperRound387Exact as R387

r284BuildsR387 :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  R284.DirectT5ContinuumClusteringPayment
    dataSet extension tests spectrumSource →
  R387.DirectSelectedSpectralUpper base tests spectrumSource
r284BuildsR387
    {base = base} {tests = tests} {spectrumSource = spectrumSource}
    payment = record
  { R387.DirectSelectedSpectralUpper.selectedResponseBelowSpectrumEnvelope =
      λ cutoff observable time →
        let
          index = R281.indexFor spectrumSource observable time
          left = R278.left tests index
          right = R278.right tests index
          covarianceUpper =
            R284.finiteSelectedUpper payment cutoff observable time
          mixedLogIsCovariance =
            R341.mixedLogMagnitudeIsFiniteSelectedCovarianceMagnitude
              base cutoff left right
        in
        subst
          (λ lower → lower ≤ R281.clusteringEnvelope spectrumSource observable time)
          (sym mixedLogIsCovariance)
          covarianceUpper
  }

r274R284DirectProducerCompilesToR387 : Bool
r274R284DirectProducerCompilesToR387 = true

r274R284DirectProducerCompilesToR387IsTrue :
  r274R284DirectProducerCompilesToR387 ≡ true
r274R284DirectProducerCompilesToR387IsTrue = refl

r274MandatoryForR387 : Bool
r274MandatoryForR387 = false

r274MandatoryForR387IsFalse : r274MandatoryForR387 ≡ false
r274MandatoryForR387IsFalse = refl

r388IntroducesFreshYMEstimate : Bool
r388IntroducesFreshYMEstimate = false

r388IntroducesFreshYMEstimateIsFalse :
  r388IntroducesFreshYMEstimate ≡ false
r388IntroducesFreshYMEstimateIsFalse = refl

round388ArchaeologyCompilerLevel : ProofLevel
round388ArchaeologyCompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
