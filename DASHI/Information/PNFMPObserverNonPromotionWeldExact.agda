module DASHI.Information.PNFMPObserverNonPromotionWeldExact where

-- Original DASHI cross-owner negative-control theorem.
-- PR #1480 owns MP classifier; EpistemicPowerHistoryAndNonSubstitutionExact
-- owns the actual distinguishability witness. No random-matrix theorem or
-- cortisol/cognitive-warfare causation is inferred from a spectral class.
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Governance.EpistemicPowerHistoryAndNonSubstitutionExact as Work
import DASHI.Information.PNFSpectralGeometry as PNF
import DASHI.Information.PNFMarchenkoPasturFiniteExact as MP
import DASHI.Interop.PNFSpectralNumericABICore as ABI

-- For *any* source-to-eigenvalue estimator which sees only recorded tasks,
-- applying an MP threshold cannot recover independent controller purpose.
-- The negative control remains legitimate review versus obstruction with
-- identical observable task records. No actual eigenvalue is fabricated.
taskOnlyMPClass :
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)) →
  (estimate : List Work.EpistemicTask → PNF.ScalarStructure.Scalar K) →
  Work.ReviewEpisode → PNF.SpectralClass
taskOnlyMPClass K C classifier estimate episode =
  PNF.NoiseClassifier.classify classifier
    (estimate (Work.observedTasks episode))

taskOnlyMPClassCannotDetermineIntent :
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)) →
  (estimate : List Work.EpistemicTask → PNF.ScalarStructure.Scalar K) →
  NF.FactorsThrough
    (taskOnlyMPClass K C classifier estimate)
    Work.statedPurpose → ⊥
taskOnlyMPClassCannotDetermineIntent K C classifier estimate =
  NF.rechartingCannotRecoverErasedPhenomenon
    (λ tasks → PNF.NoiseClassifier.classify classifier (estimate tasks))
    Work.sameTasksCannotIdentifyPurpose

-- Source-selected public disposition erases actual retention effort.
-- No postprocessed spectral label of that disposition can recover it.
publicOutcomeMPClassCannotRecoverRetention :
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)) →
  (estimate : Work.PublicDisposition → PNF.ScalarStructure.Scalar K) →
  NF.FactorsThrough
    (λ tasks → PNF.NoiseClassifier.classify classifier
      (estimate (Work.visibleDisposition tasks)))
    Work.retentionDemand → ⊥
publicOutcomeMPClassCannotRecoverRetention K C classifier estimate =
  NF.rechartingCannotRecoverErasedPhenomenon
    (λ outcome → PNF.NoiseClassifier.classify classifier (estimate outcome))
    Work.sameOutcomeDifferentRetentionHistory

-- A numerical mode classification is not the separate PNF numeric ABI
-- promotion right. This exact empty-type boundary already exists.
noMPClassCanAuthoriseNumericPromotion :
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)) →
  (estimate : List Work.EpistemicTask → PNF.ScalarStructure.Scalar K) →
  (episode : Work.ReviewEpisode) →
  ABI.PNFSpectralNumericABIPromotion → ⊥
noMPClassCanAuthoriseNumericPromotion K C classifier estimate episode =
  ABI.pnfSpectralNumericABIPromotionImpossible
