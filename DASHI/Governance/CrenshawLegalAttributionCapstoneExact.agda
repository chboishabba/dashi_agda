module DASHI.Governance.CrenshawLegalAttributionCapstoneExact where

-- Explicit attribution ladder:
-- judicial opinion -> Crenshaw's academic interpretation -> DASHI model
-- -> DASHI mathematical construction -> external legal adjudication.
-- Crenshaw's featured 1989 cases are DeGraffenreid, Moore, Payne.\n-- Jefferies is an independently selected DASHI positive comparator.\n-- These stages are distinct. None is automatically promoted by a citation.
open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Law.LegalAuthorityCitationExact as Legal
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.CrenshawLegalPrimaryCaseAtlasExact as Cases
import DASHI.Governance.CrenshawLegalCaseComparisonExact as Comparison
import DASHI.Governance.CrenshawLegalRepresentationRemedyExact as Rep

data AttributionStage : Set where
  judicialText scholarlyAnalysis finiteDASHIReconstruction
  formalDASHITheorem externallyAdjudicated : AttributionStage

courtTextIsNotCrenshawTheorem :
  judicialText ≡ formalDASHITheorem → ⊥
courtTextIsNotCrenshawTheorem ()

scholarlyAnalysisIsNotAdjudication :
  scholarlyAnalysis ≡ externallyAdjudicated → ⊥
scholarlyAnalysisIsNotAdjudication ()

record LegalCrossCaseCut : Set₁ where
  constructor legal-cross-case-cut
  field
    stageSeparation :
      Cases.districtCourt ≡ Cases.appellateCourt → ⊥
    recognisedClaimStillNeedsMerits :
      INF.FactorsThrough Comparison.observedRecognition
        Comparison.liability → ⊥
    classMembershipNotRepresentation :
      INF.FactorsThrough Rep.groupMember
        Rep.adequateRepresentation → ⊥
    classScopeNotRelief :
      INF.FactorsThrough Rep.classScope Rep.relief → ⊥
    combinationRecognitionPositiveControl :
      Comparison.boundedTreatment Comparison.jefferiesAppellateReading
        ≡ Comparison.recognisesCombinedCategory
    separateMoorePayneDispositions :
      Rep.reportedDisposition Rep.moore
        ≡ Rep.reportedDisposition Rep.payne → ⊥
    citationDoesNotClaimBinding :
      Legal.bindingForceClaimed Cases.jefferiesAppeal ≡ false
    crenshawBibliographyNoProofPromotion :
      Attr.citationImportsProof Cases.crenshawDemarginalizing ≡ false

crenshawLegalCrossCaseCut : LegalCrossCaseCut
crenshawLegalCrossCaseCut =
  legal-cross-case-cut
    Cases.districtNotAppellate
    Comparison.recognitionDoesNotEstablishMerits
    Rep.classMembershipCannotDecideRepresentativeAdequacy
    Rep.classScopeCannotDetermineRemedy
    Comparison.jefferiesIntersectionalRecognitionPositiveControl
    Rep.mooreAndPayneHaveDistinctAppellateDispositions
    refl refl
