module DASHI.Governance.CrenshawLegalAttributionCapstoneExact where

-- Explicit attribution ladder:
-- judicial opinion -> Crenshaw's academic interpretation -> DASHI model
-- -> DASHI mathematical construction -> external legal adjudication.
-- These stages are distinct. None is automatically promoted by a citation.
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

data SourceOwner : Set where
  districtCourtOwner eighthCircuitOwner fifthCircuitOwner
  ninthCircuitOwner crenshawOwner dashiOwner : SourceOwner

stageOwner : AttributionStage → SourceOwner
stageOwner judicialText = districtCourtOwner
stageOwner scholarlyAnalysis = crenshawOwner
stageOwner finiteDASHIReconstruction = dashiOwner
stageOwner formalDASHITheorem = dashiOwner
stageOwner externallyAdjudicated = fifthCircuitOwner

-- This assignment is only a demonstrative owner-function, not a universal
-- definition of who can judicially adjudicate. No legal authority derives
-- from this constructor map.
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
