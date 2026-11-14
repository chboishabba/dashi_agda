module DASHI.Governance.CrenshawLegalPrimaryCaseAtlasExact where

-- The courts own the judgments; Crenshaw owns her scholarly analyses.
-- DASHI owns only these typed formal reconstructions and finite proofs.
-- Online transcriptions have not been matched to digest-verified court PDFs.
open import DASHI.Core.Prelude
import DASHI.Law.LegalAuthorityCitationExact as Legal
import DASHI.Core.AttributedSourceCore as Attr

deGraffenreidTrial : Legal.LegalCitation
deGraffenreidTrial = Legal.legal-citation
  Legal.judgment Legal.primaryTextEvidence
  "US federal district court, Eastern District of Missouri"
  "United States District Court for the Eastern District of Missouri"
  "DeGraffenreid v General Motors Assembly Division"
  1976
  (Legal.bibliographicLegalFallback "413 F. Supp. 142")
  "143-145, combined race-and-sex claim"
  "District court declined a combined race-and-sex Title VII cause of action"
  false refl

deGraffenreidAppeal : Legal.LegalCitation
deGraffenreidAppeal = Legal.legal-citation
  Legal.judgment Legal.primaryTextEvidence
  "US federal appellate court, Eighth Circuit"
  "United States Court of Appeals for the Eighth Circuit"
  "DeGraffenreid v General Motors Assembly Division"
  1977
  (Legal.bibliographicLegalFallback "558 F.2d 480")
  "480-487, opening and disposition"
  "Affirmed in part, reversed in part and remanded, on grounds requiring stage-specific analysis"
  false refl

jefferiesAppeal : Legal.LegalCitation
jefferiesAppeal = Legal.legal-citation
  Legal.judgment Legal.primaryTextEvidence
  "US federal appellate court, Fifth Circuit"
  "United States Court of Appeals for the Fifth Circuit"
  "Jefferies v Harris County Community Action Association"
  1980
  (Legal.bibliographicLegalFallback "615 F.2d 1025")
  "1032-1034, combined claim and remand"
  "Recognised combined race-and-sex discrimination claims and remanded for findings"
  false refl

crenshawDemarginalizing : Attr.AttributedSource
crenshawDemarginalizing = Attr.mkNoDOISource
  "Kimberle Williams Crenshaw"
  "Demarginalizing the Intersection of Race and Sex"
  "University of Chicago Legal Forum 1989(1), Article 8"
  "1989"
  "https://chicagounbound.uchicago.edu/uclf/vol1989/iss1/8/"
  Attr.academicArticleSource
  "Source theorist; not the judicial opinion author or DASHI theorem author"
  Attr.publicAttribution

data ProvenanceLayer : Set where
  courtOpinionLayer crenshawAnalyticLayer dashiReconstructionLayer : ProvenanceLayer

data CaseKey : Set where
  deGraffenreid jefferies : CaseKey

data CourtStage : Set where
  districtCourt appellateCourt : CourtStage

data BoundedLegalTopic : Set where
  combinationClaimRejected combinationClaimRecognised
  partialAppealDisposition remandForFindings : BoundedLegalTopic

data ReportedCasePassage :
  CaseKey → CourtStage → BoundedLegalTopic → Set where
  districtCombinationPassage :
    ReportedCasePassage
      deGraffenreid districtCourt combinationClaimRejected
  deGraffenreidAppealPassage :
    ReportedCasePassage
      deGraffenreid appellateCourt partialAppealDisposition
  jefferiesRecognitionPassage :
    ReportedCasePassage
      jefferies appellateCourt combinationClaimRecognised
  jefferiesRemandPassage :
    ReportedCasePassage
      jefferies appellateCourt remandForFindings

districtNotAppellate :
  districtCourt ≡ appellateCourt → ⊥
districtNotAppellate ()

data MeritsStatus : Set where
  meritsNotDetermined meritsProved : MeritsStatus

data ClaimRecognition : Set where
  claimUnrecognised claimRecognised : ClaimRecognition

record ProceduralCaseStatus : Set where
  constructor procedural-case-status
  field
    recognition : ClaimRecognition
    merits : MeritsStatus

jefferiesCombinationAtRemand : ProceduralCaseStatus
jefferiesCombinationAtRemand =
  procedural-case-status claimRecognised meritsNotDetermined

jefferiesRecognitionAtRemand :
  ProceduralCaseStatus.recognition jefferiesCombinationAtRemand
  ≡ claimRecognised
jefferiesRecognitionAtRemand = refl

jefferiesCombinationMeritsNotEstablishedAtRemand :
  ProceduralCaseStatus.merits jefferiesCombinationAtRemand
  ≡ meritsNotDetermined
jefferiesCombinationMeritsNotEstablishedAtRemand = refl
