module DASHI.Philosophy.HardClosureRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Philosophy.ClosureInteractionLaws as Closure
import DASHI.Philosophy.CulturalProvenanceInstances as Cultural
import DASHI.Philosophy.MentalHealthEvidenceAdapter as Mental
import DASHI.Philosophy.RepairAdmissibility as Repair
import DASHI.Philosophy.TopologyChangeCriteria as Topology

feedbackStillDoesNotPromoteTopology :
  Topology.changedTransitionSystemImpliesChangedTopology
    Topology.canonicalChangePromotionBoundary
  ≡ false
feedbackStillDoesNotPromoteTopology = refl

administrativeClosureStillNotEpistemic :
  Closure.administrativeImpliesEpistemic
    Closure.canonicalClosureInteractionBoundary
  ≡ false
administrativeClosureStillNotEpistemic = refl

restitutionBeforeCessationStillInvalid :
  Repair.restitutionWithoutCessationValid
    Repair.canonicalRepairAdmissibilityBoundary
  ≡ false
restitutionBeforeCessationStillInvalid = refl

supportPlanStillNotClinicalClaim :
  Mental.supportPlanAutomaticallyClinical
    Mental.canonicalMentalHealthPromotionBoundary
  ≡ false
supportPlanStillNotClinicalClaim = refl

culturalInspirationStillNotRepresentation :
  Cultural.inspirationEqualsRepresentation
    Cultural.canonicalProvenanceInstanceBoundary
  ≡ false
culturalInspirationStillNotRepresentation = refl
