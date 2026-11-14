module DASHI.Ontology.RosarioPNFAdmissibleFactorisationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)

import DASHI.Cognition.PNF.TypePressure as PNFPressure
import DASHI.Cognition.PNF.WikidataRepairProposal as Repair
import DASHI.Core.QueryFactorisationSufficiency as Factor
open import DASHI.Ontology.RosarioConceptualDiagnosticsExact
open import DASHI.Ontology.RosarioPNFAdmissibleFactorisationExact

sampleHotspot : HotspotObservation
sampleHotspot =
  hotspotObservation
    software
    highEdgeDisagreementRate
    needsHumanAttention
    "bounded ACL/OCTF-style hotspot fixture"

sampleHotspotInterpretation : RosarioPNFInterpretation sampleHotspot
sampleHotspotInterpretation =
  rosarioPNFInterpretation (+ 1) "LLM disagreement observation" "bounded hotspot review"

hotspotEvidenceIsPreserved :
  PNFPressure.evidence (asHotspotPressure sampleHotspotInterpretation) ≡ sampleHotspot
hotspotEvidenceIsPreserved = refl

llmOnlyRepairRoutesToReview :
  llmOnlyRoute highEdgeDisagreementRate ≡ Repair.holdForReview
llmOnlyRepairRoutesToReview = refl

hotspotPressureStillCannotAssertType :
  PNFPressure.TypePressurePromotionPermission → ⊥
hotspotPressureStillCannotAssertType = PNFPressure.pressureAloneCannotAssertType

llmOnlyCannotClaimDestructiveRepairAuthority :
  LLMOnlyDestructiveRepairPermission → ⊥
llmOnlyCannotClaimDestructiveRepairAuthority = llmOnlyCannotAuthorizeDestructiveRepair

repairProposalStillCannotAssertOntologyTruth :
  Repair.RepairProposalTruthPermission Repair.proposalForReviewOnly → ⊥
repairProposalStillCannotAssertOntologyTruth = Repair.repairProposalCannotAssertOntologyTruth

subclassQueryFactorsThroughCoarseSurface :
  Factor.FactorsThrough alignmentQuestions coarseAlignmentSurface subclassQuery
subclassQueryFactorsThroughCoarseSurface = subclassFactorsThrough

disjointnessQueryDoesNotFactorThroughSameSurface :
  Factor.FactorsThrough alignmentQuestions coarseAlignmentSurface disjointnessQuery → ⊥
disjointnessQueryDoesNotFactorThroughSameSurface = disjointnessCannotFactorThrough
