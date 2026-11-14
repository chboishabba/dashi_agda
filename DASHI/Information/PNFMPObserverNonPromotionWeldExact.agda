module DASHI.Information.PNFMPObserverNonPromotionWeldExact where

-- Generic cross-owner adapter. It imports ONLY PNF/MP owners present on
-- this PR's base/master, never PR #1479-only cognitive-work modules.
-- An external source-specific observer (e.g. epistemic work on #1479)
-- supplies its independently proved NonFactorabilityWitness.
-- Marchenko-Pastur supplies a numerical classifier, not causation or
-- truth promotion.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Information.PNFSpectralGeometry as PNF
import DASHI.Information.PNFMarchenkoPasturFiniteExact as MP
import DASHI.Interop.PNFSpectralNumericABICore as ABI

-- Any outcome erased by a selected observable cannot be recovered
-- merely by assigning a spectral value and an MP threshold to it.
mpClassOfObserver :
  ∀ {Situated Observation : Set} →
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)) →
  (observe : Situated → Observation) →
  (estimate : Observation → PNF.ScalarStructure.Scalar K) →
  Situated → PNF.SpectralClass
mpClassOfObserver K C classifier observe estimate state =
  PNF.NoiseClassifier.classify classifier (estimate (observe state))

mpRechartCannotRecoverErasedOutcome :
  ∀ {Situated Observation Outcome : Set} →
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)) →
  (observe : Situated → Observation) →
  (phenomenon : Situated → Outcome) →
  (witness : NF.NonFactorabilityWitness observe phenomenon) →
  (estimate : Observation → PNF.ScalarStructure.Scalar K) →
  NF.FactorsThrough
    (mpClassOfObserver K C classifier observe estimate)
    phenomenon → ⊥
mpRechartCannotRecoverErasedOutcome K C classifier observe
  phenomenon witness estimate =
  NF.rechartingCannotRecoverErasedPhenomenon
    (λ observed → PNF.NoiseClassifier.classify classifier
      (estimate observed))
    witness

-- No owner of a sample eigenvalue, MP null edge or selected
-- observational recharting may construct the existing empty
-- PNF spectral numeric ABI promotion authority.
mpClassCannotPromoteNumericABI :
  ∀ {Situated Observation : Set} →
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)) →
  (observe : Situated → Observation) →
  (estimate : Observation → PNF.ScalarStructure.Scalar K) →
  (state : Situated) →
  ABI.PNFSpectralNumericABIPromotion → ⊥
mpClassCannotPromoteNumericABI K C classifier observe estimate state =
  ABI.pnfSpectralNumericABIPromotionImpossible

-- After an explicit PR stack/merge, instantiate the generic theorem with
-- EpistemicPowerHistoryAndNonSubstitutionExact.sameTasksCannotIdentifyPurpose
-- or sameOutcomeDifferentRetentionHistory. The current #1480 branch
-- intentionally DOES NOT import that unmerged source owner.
