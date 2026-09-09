module DASHI.Cognition.PNF.SensibLawCullenAttributedAtomicCaseRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)

import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Provenance
import DASHI.Cognition.PNF.SensibLawAttributedAtomicCaseRegistryExact as Attributed
import DASHI.Cognition.PNF.SensibLawNSWCivilLiabilityActAtomicSourceAtlasExact as CLA
import DASHI.Cognition.PNF.SensibLawCullenNSWCLAAtomicApplicationExact as CullenCLA
import DASHI.Cognition.PNF.SensibLawCullenS43ASpecialStatutoryPowerAtomicExact as S43A
import DASHI.Cognition.PNF.SensibLawCullenVicariousLiabilityFamilyAtomicExact as Vicarious
import DASHI.Cognition.PNF.SensibLawNSWVicariousLiabilityActAtomicSourceAtlasExact as VicariousAct
import DASHI.Cognition.PNF.SensibLawCullenAtomicCaseRegistryExact as Registry

------------------------------------------------------------------------
-- CULLEN ATTRIBUTED ATOMIC CASE REGISTRY
--
-- Each legal proposition is a DASHI formal object supported by an exact source
-- receipt.  The proposition therefore remains a repository reconstruction even
-- when its support is primary legislation or primary High Court reasons.
--
-- Each +1/-1 gate is then a DASHI evaluation over the source-defined test and
-- attributed case-outcome evidence.  The gate is not attributed back to the
-- court or statute.
------------------------------------------------------------------------

cullenDefinitionLineage :
  ∀ {p} →
  Registry.CullenAtomicEntry p →
  Provenance.ClaimLineageReceipt p
cullenDefinitionLineage Registry.s5BForeseeableEntry =
  Provenance.reconstructionFromSourceReceipt
    CLA.s5BForeseeableSource
    "DASHI formal reconstruction of the s 5B(1)(a) statutory atom"
cullenDefinitionLineage Registry.s5BNotInsignificantEntry =
  Provenance.reconstructionFromSourceReceipt
    CLA.s5BNotInsignificantSource
    "DASHI formal reconstruction of the s 5B(1)(b) statutory atom"
cullenDefinitionLineage Registry.s5BReasonablePrecautionsEntry =
  Provenance.reconstructionFromSourceReceipt
    CLA.s5BReasonablePrecautionsSource
    "DASHI formal reconstruction of the s 5B(1)(c) reasonable-precautions atom"
cullenDefinitionLineage Registry.s43AEngagementEntry =
  Provenance.reconstructionFromSourceReceipt
    S43A.s43ABasedOnSource
    "DASHI formal reconstruction of the s 43A engagement atom"
cullenDefinitionLineage Registry.vicariousFamilyEntry =
  Provenance.reconstructionFromSourceReceipt
    VicariousAct.s8FamilySource
    "DASHI formal reconstruction of the statutory vicarious-liability family atom"

cullenOutcomeLineage :
  ∀ {p} →
  (entry : Registry.CullenAtomicEntry p) →
  Attributed.AtomicEntryOutcomeLineage Registry.cullenAtomicRegistry entry
cullenOutcomeLineage Registry.s5BForeseeableEntry =
  Attributed.positiveOutcomeLineage refl
    (Provenance.reconstructionFromSourceReceipt
      CullenCLA.joint39ForeseeableSource
      "DASHI formal reconstruction of Cullen joint reasons [39] as positive outcome evidence for s 5B(1)(a)")
cullenOutcomeLineage Registry.s5BNotInsignificantEntry =
  Attributed.positiveOutcomeLineage refl
    (Provenance.reconstructionFromSourceReceipt
      CullenCLA.joint39NotInsignificantSource
      "DASHI formal reconstruction of Cullen joint reasons [39] as positive outcome evidence for s 5B(1)(b)")
cullenOutcomeLineage Registry.s5BReasonablePrecautionsEntry =
  Attributed.negativeOutcomeLineage refl
    (Provenance.reconstructionFromSourceReceipt
      CullenCLA.joint48ReasonablePrecautionsSource
      "DASHI formal reconstruction of Cullen joint reasons [42]-[48] as sourced failure evidence for the exact s 5B(1)(c) atom")
cullenOutcomeLineage Registry.s43AEngagementEntry =
  Attributed.negativeOutcomeLineage refl
    (Provenance.reconstructionFromSourceReceipt
      S43A.noStatutoryPowerEvidenceSource
      "DASHI formal reconstruction of Edelman J [64] as sourced failure evidence for the exact s 43A engagement atom")
cullenOutcomeLineage Registry.vicariousFamilyEntry =
  Attributed.positiveOutcomeLineage refl
    (Provenance.reconstructionFromSourceReceipt
      Vicarious.cullen100SourceReceipt
      "DASHI formal reconstruction of Edelman J [100] as sourced positive evidence for the vicarious-liability family atom")

cullenEvaluationLineage :
  ∀ {p} →
  (entry : Registry.CullenAtomicEntry p) →
  Attributed.AtomicEvaluationLineageReceipt Registry.cullenAtomicRegistry entry
cullenEvaluationLineage Registry.s5BForeseeableEntry =
  Provenance.crossSourceInference ,
  Attributed.repositoryEvaluationInference
    "DASHI source-conditioned evaluation: statutory test definition + Cullen [39] outcome evidence => +1; the +1 is repository inference, not a quotation from the Court"
cullenEvaluationLineage Registry.s5BNotInsignificantEntry =
  Provenance.crossSourceInference ,
  Attributed.repositoryEvaluationInference
    "DASHI source-conditioned evaluation: statutory test definition + Cullen [39] outcome evidence => +1; the +1 is repository inference"
cullenEvaluationLineage Registry.s5BReasonablePrecautionsEntry =
  Provenance.crossSourceInference ,
  Attributed.repositoryEvaluationInference
    "DASHI source-conditioned evaluation: statutory s 5B(1)(c) test + Cullen [42]-[48] failure evidence => -1; the -1 is not itself a judicial proposition"
cullenEvaluationLineage Registry.s43AEngagementEntry =
  Provenance.crossSourceInference ,
  Attributed.repositoryEvaluationInference
    "DASHI source-conditioned evaluation: s 43A engagement test + Edelman [64] no-statutory-power evidence => -1; concurrence role and statutory definition remain separate"
cullenEvaluationLineage Registry.vicariousFamilyEntry =
  Provenance.crossSourceInference ,
  Attributed.repositoryEvaluationInference
    "DASHI source-conditioned evaluation: statutory family definition + Edelman [100] concurrence evidence => +1; family recognition remains conditional on an underlying tort"

cullenAttributedAtomicRegistry :
  Attributed.AttributedAtomicCaseRegistry Registry.cullenAtomicRegistry
cullenAttributedAtomicRegistry =
  Attributed.attributed-atomic-case-registry
    cullenDefinitionLineage
    cullenOutcomeLineage
    cullenEvaluationLineage
    "Cullen finite atomic registry with definition, case-outcome, and repository-evaluation provenance kept distinct."

------------------------------------------------------------------------
-- Explicit attribution firewalls for the Cullen fixture.
------------------------------------------------------------------------

data CullenGateIsJudicialQuotation : Set where
data CullenGateIsAdjudicatedFactByRegistration : Set where
data EdelmanConcurrenceGateBecomesJointRatio : Set where
data StatutoryDefinitionOwnsCaseOutcome : Set where

cullenGateIsNotJudicialQuotation : CullenGateIsJudicialQuotation → ⊥
cullenGateIsNotJudicialQuotation ()

registrationDoesNotMakeGateAdjudicatedFact :
  CullenGateIsAdjudicatedFactByRegistration → ⊥
registrationDoesNotMakeGateAdjudicatedFact ()

edelmanGateDoesNotBecomeJointRatio : EdelmanConcurrenceGateBecomesJointRatio → ⊥
edelmanGateDoesNotBecomeJointRatio ()

statutoryDefinitionDoesNotOwnCaseOutcome : StatutoryDefinitionOwnsCaseOutcome → ⊥
statutoryDefinitionDoesNotOwnCaseOutcome ()
