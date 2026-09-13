module DASHI.ComputerScience.LiuDonghaoDSMMBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificCapabilityCarrierBidiExact as C
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T

------------------------------------------------------------------------
-- LIU DONGHAO: DATA-SECURITY CAPABILITY MATURITY / DSMM
--
-- Source coordinate: GB/T 37988-2019 context plus Liu's institutional DSMM
-- lecture/work surface.  This is security-governance/maturity engineering, not
-- an attribution of cryptographic primitive invention.
------------------------------------------------------------------------

data DataLifecycleStage : Set where
  collection transmission storage processing exchange destruction : DataLifecycleStage

data MaturityEvidenceCoordinate : Set where
  governanceRule implementedControl retainedEvidence repeatableAssessment
  measuredImprovement lifecycleCoverage : MaturityEvidenceCoordinate

record DSMMModel : Set where
  constructor dsmm-model
  field
    sourceReference : String
    standardCoordinate : String
    lifecycle : List DataLifecycleStage
    evidenceCoordinates : List MaturityEvidenceCoordinate
    intendedOutput : String
    openAuthorshipLeaf : String

open DSMMModel public

canonicalLiuDSMMModel : DSMMModel
canonicalLiuDSMMModel = dsmm-model
  "Liu Donghao institutional DSMM work; GB/T 37988-2019"
  "GB/T 37988-2019"
  (collection ∷ transmission ∷ storage ∷ processing ∷ exchange ∷ destruction ∷ [])
  (governanceRule ∷ implementedControl ∷ retainedEvidence ∷ repeatableAssessment ∷
   measuredImprovement ∷ lifecycleCoverage ∷ [])
  "an evidence-bearing maturity assessment over the data lifecycle"
  "exact Liu-authored standard clauses, assessment rubric, papers, patents and project implementations"

liuDSMMCarrier : C.ScientificCapabilityCarrier
liuDSMMCarrier = C.scientific-capability-carrier
  "data-security governance"
  "DSMM assessment and integration workflow"
  C.integrationProcedure
  C.carrierPartial
  "lifecycle-wide security maturity assessment and evidence collection"
  "GB/T 37988-2019 context; institutional DSMM work"
  "The standard/maturity context is source-backed; exact Liu-authored rule content remains bounded."

liuDSMMTransformation : T.ApplicationTransformation
liuDSMMTransformation = T.application-transformation
  "organisational data-security maturity"
  (T.integrationWorkflow ∷ T.uncertaintyModel ∷ [])
  (T.validationCorpus ∷ T.failureHistory ∷ T.tacitExecutionKnowledge ∷ T.qualificationEvidence ∷ [])
  "GB/T 37988-2019 context"
  "Operational maturity requires organisation-specific controls, evidence, assessors and remediation history."

data LiuDSMMReverseTarget : Set where
  acquireAuthoredClause acquireAssessmentRubric acquireScoringSemantics
  acquireValidationCases acquireProjectImplementation acquireGovernanceSuccession : LiuDSMMReverseTarget

DSMMImpliesCryptographicPrimitive : Bool
DSMMImpliesCryptographicPrimitive = false

maturityGovernanceImpliesAccessToProtectedScience : Bool
maturityGovernanceImpliesAccessToProtectedScience = false

DSMMCanServeIntegratedDataGovernanceRole : Bool
DSMMCanServeIntegratedDataGovernanceRole = true
