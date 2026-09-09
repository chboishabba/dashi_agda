module DASHI.Cognition.PNF.SensibLawCullenS43ASpecialStatutoryPowerAtomicExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Cognition.PNF.SensibLawSourceFormAuthorityRoleBidiExact as SourceRole
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic
import DASHI.Cognition.PNF.SensibLawRecentDutyCaseSourceAtlasExact as CullenSource

------------------------------------------------------------------------
-- CIVIL LIABILITY ACT 2002 (NSW) s 43A x CULLEN
--
-- Statute defines the applicability/standard atoms.  Cullen supplies separate
-- case-outcome evidence.  Procedural abandonment remains another proposition.
------------------------------------------------------------------------

claSource : Source.AttributedSource
claSource = Source.mkNoDOISource
  "Parliament of New South Wales; NSW Parliamentary Counsel"
  "Civil Liability Act 2002 No 22"
  "NSW legislation website — current consolidated Act"
  "2002"
  "https://legislation.nsw.gov.au/view/whole/html/inforce/current/act-2002-022"
  Source.governmentSource
  "primary statutory text for s 43A; citation does not establish engagement on Cullen facts"
  Source.publicAttribution

claLegalSource : Ontology.LegalSource
claLegalSource = Ontology.legalSource
  (Ontology.stableId "source:NSW:Civil-Liability-Act-2002-No22")
  Negligence.auCommonLawSystem Ontology.statute
  "Civil Liability Act 2002 No 22 (NSW)"
  "current consolidated source; point-in-time applicability separately required"
  "New South Wales"

claSourceRef : Algebra.LegalSourceRef
claSourceRef = Algebra.legal-source-ref claLegalSource
  "Parliament of New South Wales" "Civil Liability Act 2002 No 22"
  "NSW Act No 22 of 2002"

claAuthority : Edge.SourceIdentity
claAuthority = Edge.source-identity
  "Parliament of New South Wales" "Civil Liability Act 2002 No 22"
  "NSW Act No 22 of 2002" Edge.legislation

s43ARole : String → SourceRole.SourceFormRoleReceipt
s43ARole ref = SourceRole.source-form-role-receipt
  claAuthority Ontology.statute Algebra.legislativeRuleRole ref true true

s43AReceipt :
  (p : Algebra.LegalProposition) → String → String →
  SourceRule.PropositionSourceReceipt p
s43AReceipt p locator reference = SourceRule.proposition-source-receipt
  claSource claSourceRef locator SourceRule.primarySourceLayer
  (s43ARole reference) refl refl refl
  (Source.citationCreatesAuthorityIsFalse claSource) reference

specialPowerConferredByStatute : Algebra.LegalProposition
specialPowerConferredByStatute = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s43A-2-a:power-conferred-by-statute")
  Algebra.institutionalConstraint
  (Ontology.stableId "power:current")
  (Ontology.stableId "section:NSW-CLA:43A-2-a")
  Negligence.auCommonLawSystem
  "the relevant power is conferred by or under a statute"

powerNotGenerallyAvailableWithoutSpecificAuthority : Algebra.LegalProposition
powerNotGenerallyAvailableWithoutSpecificAuthority = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s43A-2-b:not-generally-authorised")
  Algebra.institutionalConstraint
  (Ontology.stableId "power:current")
  (Ontology.stableId "section:NSW-CLA:43A-2-b")
  Negligence.auCommonLawSystem
  "the power is of a kind persons generally are not authorised to exercise without specific statutory authority"

liabilityBasedOnExerciseOfSpecialStatutoryPower : Algebra.LegalProposition
liabilityBasedOnExerciseOfSpecialStatutoryPower = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s43A-1:liability-based-on-special-power")
  Algebra.doctrinalPredicate
  (Ontology.stableId "claim:Cullen")
  (Ontology.stableId "section:NSW-CLA:43A")
  Negligence.auCommonLawSystem
  "the civil-liability claim is based on exercise of or failure to exercise a special statutory power"

s43AUnreasonablenessStandard : Algebra.LegalProposition
s43AUnreasonablenessStandard = Algebra.legal-proposition
  (Ontology.stableId "prop:NSW-CLA:s43A-3:attenuated-standard")
  Algebra.wrongElementPredicate
  (Ontology.stableId "actor:public-authority")
  (Ontology.stableId "section:NSW-CLA:43A-3")
  Negligence.auCommonLawSystem
  "where s 43A is engaged, civil liability requires the source-defined no-authority-could-properly-consider-reasonable threshold"

s43AConferredSource : SourceRule.PropositionSourceReceipt specialPowerConferredByStatute
s43AConferredSource = s43AReceipt specialPowerConferredByStatute "s 43A(2)(a)" "NSW-CLA-s43A-2-a"

s43AGeneralAvailabilitySource : SourceRule.PropositionSourceReceipt powerNotGenerallyAvailableWithoutSpecificAuthority
s43AGeneralAvailabilitySource = s43AReceipt powerNotGenerallyAvailableWithoutSpecificAuthority "s 43A(2)(b)" "NSW-CLA-s43A-2-b"

s43ABasedOnSource : SourceRule.PropositionSourceReceipt liabilityBasedOnExerciseOfSpecialStatutoryPower
s43ABasedOnSource = s43AReceipt liabilityBasedOnExerciseOfSpecialStatutoryPower "s 43A(1)" "NSW-CLA-s43A-1"

s43AStandardSource : SourceRule.PropositionSourceReceipt s43AUnreasonablenessStandard
s43AStandardSource = s43AReceipt s43AUnreasonablenessStandard "s 43A(3)" "NSW-CLA-s43A-3"

------------------------------------------------------------------------
-- Cullen primary outcome evidence: Edelman J [64] and fn 103.
------------------------------------------------------------------------

edelman64Locator : String
edelman64Locator = "Cullen v New South Wales [2026] HCA 19, Edelman J [64] and fn 103"

noStatutoryPowerOutcome : Algebra.LegalProposition
noStatutoryPowerOutcome = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:Edelman:64:no-statutory-power-outcome")
  Algebra.factualFeature
  (Ontology.stableId "activity:OSG-intervention")
  (Ontology.stableId "section:NSW-CLA:43A")
  Negligence.auCommonLawSystem
  "the intervention was not said in the High Court to be pursuant to any statutory power"

s43AArgumentAbandoned : Algebra.LegalProposition
s43AArgumentAbandoned = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:HCA:s43A-argument-abandoned")
  Algebra.otherLegalPredicate
  (Ontology.stableId "party:NSW")
  (Ontology.stableId "section:NSW-CLA:43A")
  Negligence.auCommonLawSystem
  "reliance on s 43A was abandoned by New South Wales in the High Court"

cullenAuthority : Edge.SourceIdentity
cullenAuthority = Edge.source-identity
  "High Court of Australia; Edelman J"
  "Cullen v New South Wales"
  "[2026] HCA 19, Edelman J [64] fn 103"
  Edge.bindingPrecedent

cullenFactRole : String → SourceRole.SourceFormRoleReceipt
cullenFactRole ref = SourceRole.source-form-role-receipt
  cullenAuthority Ontology.caseLaw Algebra.adjudicatedFactRole ref true true

cullenLegalSourceRef : Algebra.LegalSourceRef
cullenLegalSourceRef = Algebra.legal-source-ref
  (Ontology.legalSource
    (Ontology.stableId "source:Cullen:[2026]HCA19")
    Negligence.auCommonLawSystem Ontology.caseLaw "[2026] HCA 19"
    "2026-06-17" "Australia / High Court")
  "High Court of Australia" "Cullen v New South Wales" "[2026] HCA 19"

cullenEvidenceReceipt :
  (p : Algebra.LegalProposition) → String →
  SourceRule.PropositionSourceReceipt p
cullenEvidenceReceipt p ref = SourceRule.proposition-source-receipt
  CullenSource.cullenHCA19 cullenLegalSourceRef edelman64Locator
  SourceRule.primarySourceLayer (cullenFactRole ref)
  refl refl refl
  (Source.citationCreatesAuthorityIsFalse CullenSource.cullenHCA19) ref

noStatutoryPowerEvidenceSource : SourceRule.PropositionSourceReceipt noStatutoryPowerOutcome
noStatutoryPowerEvidenceSource = cullenEvidenceReceipt noStatutoryPowerOutcome "Cullen-Edelman-64-no-power"

s43AAbandonmentEvidenceSource : SourceRule.PropositionSourceReceipt s43AArgumentAbandoned
s43AAbandonmentEvidenceSource = cullenEvidenceReceipt s43AArgumentAbandoned "Cullen-Edelman-64-fn103-abandonment"

data S43ABasedOnFits : Set where

data S43ABasedOnFails : Set where
  cullenNotPursuantToStatutoryPower : S43ABasedOnFails

s43ABasedOnOutcome : Atomic.AtomicOutcomeSource liabilityBasedOnExerciseOfSpecialStatutoryPower
s43ABasedOnOutcome = Atomic.atomic-outcome-source
  noStatutoryPowerOutcome
  noStatutoryPowerEvidenceSource
  (Algebra.propositionId liabilityBasedOnExerciseOfSpecialStatutoryPower)
  refl refl
  "Edelman [64] positively supports failure of the exact s 43A engagement atom on the retained Cullen fibre; fn 103 separately records procedural abandonment."

cullenS43ABasedOnAtom : Atomic.SourceConditionedAtomicLegalTest liabilityBasedOnExerciseOfSpecialStatutoryPower
cullenS43ABasedOnAtom = Atomic.source-conditioned-atomic-legal-test
  s43ABasedOnSource
  (Algebra.subjectReference liabilityBasedOnExerciseOfSpecialStatutoryPower)
  refl
  S43ABasedOnFits
  S43ABasedOnFails
  (λ ())
  (λ ())
  (λ _ → s43ABasedOnOutcome)
  BT.neg
  (λ ())
  (λ _ → cullenNotPursuantToStatutoryPower)
  "Cullen s 43A engagement axis = -1: positive sourced witness that this exact special-statutory-power applicability atom fails to fit."

cullenS43AIsNegative : Atomic.gate cullenS43ABasedOnAtom ≡ BT.neg
cullenS43AIsNegative = refl

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data S43ANegativeMeansNoNegligence : Set where
data AbandonedArgumentDefinesStatutoryMeaning : Set where
data NoStatutoryPowerMeansNoPoliceFunction : Set where
data S43ANotEngagedMeansPublicAuthorityImmune : Set where

data NoPowerOutcomeEqualsAbandonment : Set where

s43ANegativeDoesNotNegateNegligence : S43ANegativeMeansNoNegligence → ⊥
s43ANegativeDoesNotNegateNegligence ()

abandonmentDoesNotDefineS43A : AbandonedArgumentDefinesStatutoryMeaning → ⊥
abandonmentDoesNotDefineS43A ()

noStatutoryPowerDoesNotErasePoliceFunction : NoStatutoryPowerMeansNoPoliceFunction → ⊥
noStatutoryPowerDoesNotErasePoliceFunction ()

s43ANotEngagedDoesNotCreateImmunity : S43ANotEngagedMeansPublicAuthorityImmune → ⊥
s43ANotEngagedDoesNotCreateImmunity ()

noPowerOutcomeDoesNotCollapseIntoAbandonment : NoPowerOutcomeEqualsAbandonment → ⊥
noPowerOutcomeDoesNotCollapseIntoAbandonment ()
