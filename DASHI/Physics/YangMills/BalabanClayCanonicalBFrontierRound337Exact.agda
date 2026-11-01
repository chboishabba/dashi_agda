{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound337Exact where

------------------------------------------------------------------------
-- ROUND337 / SOURCE THEOREM STATUS != LOCAL REPLAY STATUS
--
-- R335/R336 leave the CMP116 common-J pair-domain statement fail-closed because
-- the generic source ABI does not itself identify `AdmissibleSourcePair` with
-- the canonical R114 common J-domain.  The source extract, however, places the
-- differentiated/localized terms on one common analytic U,J domain before the
-- sum is formed (Sect. 1 around (1.23)--(1.29)).
--
-- This is therefore a source-established theorem/application statement, not a
-- fresh four-dimensional YM decay estimate.  What remains conditional locally
-- is replay/alignment into the proof-bearing `AdmissibleSourcePair` ABI.
--
-- This owner changes no theorem content and supplies no inhabitant by citation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116SelectedJPairDomainSourceFactorRound335Exact as R335
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound336Exact as R336

record Round337Boundary : Set where
  constructor round337-boundary
  field
    commonJPairDomainStatementIsFreshYMAnalysis : Bool
    commonJPairDomainStatementIsFreshYMAnalysisIsFalse :
      commonJPairDomainStatementIsFreshYMAnalysis ≡ false

    publishedDifferentiatedLocalizationSourceOwned : Bool
    publishedDifferentiatedLocalizationSourceOwnedIsTrue :
      publishedDifferentiatedLocalizationSourceOwned ≡ true

    localCommonJPairDomainReplayStillRequired : Bool
    localCommonJPairDomainReplayStillRequiredIsTrue :
      localCommonJPairDomainReplayStillRequired ≡ true

    citationMetadataAloneBuildsReplayWitness : Bool
    citationMetadataAloneBuildsReplayWitnessIsFalse :
      citationMetadataAloneBuildsReplayWitness ≡ false

    selectedJMeaningChargedAgainAfterBase : Bool
    selectedJMeaningChargedAgainAfterBaseIsFalse :
      selectedJMeaningChargedAgainAfterBase ≡ false

canonicalRound337Boundary : Round337Boundary
canonicalRound337Boundary =
  round337-boundary
    false refl
    true refl
    true refl
    false refl
    false refl

-- Source theorem authority is imported at its published strength.
round337PublishedCommonJDomainStatementLevel : ProofLevel
round337PublishedCommonJDomainStatementLevel =
  Source.cmp116DifferentiatedLocalizationAuthorityLevel

-- Local theorem replay/alignment into the generic proof-bearing pair-domain ABI
-- remains conditional until an actual inhabitant is supplied.
round337LocalCommonJPairDomainReplayLevel : ProofLevel
round337LocalCommonJPairDomainReplayLevel =
  R335.round335PublishedCommonJPairDomainAuthorityLevel

round337SelectedJMeaningDependencyCorrectionLevel : ProofLevel
round337SelectedJMeaningDependencyCorrectionLevel =
  R336.round336DependencyCorrectionLevel

round337ClassificationLevel : ProofLevel
round337ClassificationLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
