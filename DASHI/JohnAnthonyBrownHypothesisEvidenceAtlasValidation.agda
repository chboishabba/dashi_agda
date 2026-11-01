module DASHI.JohnAnthonyBrownHypothesisEvidenceAtlasValidation where

open import DASHI.Core.Prelude

import DASHI.Culture.JohnAnthonyBrownHypothesisEvidenceAtlasExact as Atlas
import DASHI.Culture.JohnAnthonyBrownPaperSectionHypothesisManifestExact as Manifest

------------------------------------------------------------------------
-- Focused consumer root:
--   agda -i . DASHI/JohnAnthonyBrownHypothesisEvidenceAtlasValidation.agda
------------------------------------------------------------------------

johnAnthonyBrownAttributionPinned :
  Atlas.HypothesisEvidenceAtlasBoundary.johnAnthonyBrownExplicitlyAttributed
    Atlas.canonicalHypothesisEvidenceAtlasBoundary
  ≡ true
johnAnthonyBrownAttributionPinned = refl

allHypothesesHaveCoordinateReceipts :
  Atlas.HypothesisEvidenceAtlasBoundary.allH1ToH5HaveCoordinateReceipts
    Atlas.canonicalHypothesisEvidenceAtlasBoundary
  ≡ true
allHypothesesHaveCoordinateReceipts = refl

earlierBibliographyRetained :
  Atlas.HypothesisEvidenceAtlasBoundary.earlierBibliographyRetainedAsProvenance
    Atlas.canonicalHypothesisEvidenceAtlasBoundary
  ≡ true
earlierBibliographyRetained = refl

earlierBibliographyNotAutoVerified :
  Atlas.HypothesisEvidenceAtlasBoundary.earlierBibliographyTreatedAsVerifiedAutomatically
    Atlas.canonicalHypothesisEvidenceAtlasBoundary
  ≡ false
earlierBibliographyNotAutoVerified = refl

comparatorEvidenceNotTargetPopulation :
  Atlas.ComparatorEvidencePromotesTargetPopulation → ⊥
comparatorEvidenceNotTargetPopulation = Atlas.comparatorDoesNotPromoteTargetPopulation

constructDefinitionNotValidatedMeasure :
  Atlas.ConstructDefinitionPromotesValidatedMeasure → ⊥
constructDefinitionNotValidatedMeasure =
  Atlas.constructDefinitionDoesNotPromoteValidatedMeasure

oneOutcomeNotWholeH2Vector :
  Atlas.OneOutcomePromotesWholeVector → ⊥
oneOutcomeNotWholeH2Vector = Atlas.oneOutcomeDoesNotPromoteWholeVector

adjustedAssociationNotCausation :
  Atlas.AdjustedAssociationPromotesCausation → ⊥
adjustedAssociationNotCausation = Atlas.adjustedAssociationDoesNotPromoteCausation

recoveredCitationNotIndependentVerification :
  Atlas.CitationRecoveredPromotesIndependentVerification → ⊥
recoveredCitationNotIndependentVerification =
  Atlas.citationRecoveredDoesNotPromoteIndependentVerification

moderationNotUniversalIntervention :
  Atlas.ModerationAssociationPromotesUniversalIntervention → ⊥
moderationNotUniversalIntervention = Atlas.moderationDoesNotPromoteUniversalIntervention

h1IsStillH1 :
  Atlas.CoordinateReceipt.hypothesis Atlas.h1PopulationReceipt ≡ Manifest.H1
h1IsStillH1 = refl

h3IsStillH3 :
  Atlas.CoordinateReceipt.hypothesis Atlas.h3InstitutionalBetrayalReceipt ≡ Manifest.H3
h3IsStillH3 = refl

h4ComparatorEvidenceIsNotTargetEffect :
  Atlas.CoordinateReceipt.status Atlas.h4ResilienceComparatorReceipt
  ≡ Atlas.recoveredFromEarlierBrownDraft
h4ComparatorEvidenceIsNotTargetEffect = refl

h5NeedsObservedAdjustedEstimate :
  Atlas.CoordinateReceipt.status Atlas.h5AdjustedAssociationReceipt
  ≡ Atlas.missingExternalReceipt
h5NeedsObservedAdjustedEstimate = refl

rightsPolicyStillDownstream :
  Atlas.RightsPolicyPromotionGate.empiricalFindingInstalled
    Atlas.canonicalRightsPolicyPromotionGate
  ≡ false
rightsPolicyStillDownstream = refl
