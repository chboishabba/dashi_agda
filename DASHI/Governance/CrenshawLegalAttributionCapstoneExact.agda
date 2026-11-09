module DASHI.Governance.CrenshawLegalAttributionCapstoneExact where

-- Explicit attribution ladder:
-- judicial opinion -> Crenshaw's academic interpretation -> DASHI model
-- -> DASHI mathematical construction -> external legal adjudication.
-- Crenshaw's featured 1989 cases are DeGraffenreid, Moore, Payne.\n-- Jefferies is Crenshaw-cited (1989 p.143 n.13), selected by DASHI\n-- for a detailed positive comparison, but not a featured case study.\n-- These stages are distinct. None is automatically promoted by a citation.
open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Law.LegalAuthorityCitationExact as Legal
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.CrenshawLegalPrimaryCaseAtlasExact as Cases
import DASHI.Governance.CrenshawLegalCaseComparisonExact as Comparison
import DASHI.Governance.CrenshawLegalRepresentationRemedyExact as Rep
import DASHI.Governance.Crenshaw1989PassageWeldExact as CrenshawSource
import DASHI.Governance.CrenshawJudicialDisagreementExact as Disagreement
import DASHI.Governance.CrenshawSituatedStandpointExact as Standpoint
import DASHI.Governance.CrenshawRightsReformDualEffectExact as Rights
import DASHI.Governance.CrenshawHistoricalCarceralSourceAtlasExact as HistSources
import DASHI.Governance.CrenshawCrossInstitutionalEvidenceExact as CrossInstitution

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
    jefferiesCitedAsCounterexample :
      CrenshawSource.crenshaw1989Role CrenshawSource.jefferies
      ≡ CrenshawSource.citedContraryExample
    payneMajorityDisagreementNotCollapsed :
      INF.FactorsThrough
        Disagreement.caseOnly Disagreement.position → ⊥
    scholarRoleNotClientCounsel :
      Standpoint.authorityOfRole Standpoint.scholarRole
      ≡ Standpoint.authorityOfRole Standpoint.counselRole → ⊥
    rosterDoesNotPayVoice :
      INF.FactorsThrough
        Standpoint.reportedPeople Standpoint.effectiveVoice → ⊥
    formalRightsDoNotDetermineMaterialTransfer :
      INF.FactorsThrough
        Rights.formalRecognition Rights.materialReallocation → ⊥
    institutionalSchoolReceiptCannotPayCustody :
      CrossInstitution.Supports CrossInstitution.schoolRecord
        CrossInstitution.custodialOutcome → ⊥
    citedCarceralAtlasDoesNotCreateAuthority :
      Attr.atlasCreatesAuthority HistSources.historicalInstitutionalSourceAtlas
        ≡ false
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
    CrenshawSource.jefferiesIsCitedByCrenshaw
    Disagreement.caseCitationCannotSelectJudicialPosition
    Standpoint.scholarlyInterpretationIsNotClientRepresentation
    Standpoint.courtRosterNotSufficientToInferAuthority
    Rights.formalRightDoesNotGuaranteeMaterialTransformation
    CrossInstitution.schoolDisciplineDoesNotByItselfPayCustodialOutcome
    HistSources.historicalCitationDoesNotCreateAuthority
    refl refl
