module DASHI.Cognition.PNF.SensibLawCullenNSWCLAAtomicApplicationExact where

------------------------------------------------------------------------
-- CULLEN x NSW CIVIL LIABILITY ACT — ATOMIC SOURCE APPLICATION
--
-- Test definition source:
--   Civil Liability Act 2002 (NSW), s 5B.
--
-- Case-outcome source:
--   Cullen v New South Wales [2026] HCA 19, joint reasons [39]-[48].
--
-- The resulting source-conditioned vector is:
--
--   s 5B(1)(a) foreseeable risk                     +1
--   s 5B(1)(b) risk not insignificant               +1
--   s 5B(1)(c) reasonable person would take the
--              proposed alternative precautions     -1
--
-- `-1` is a positive sourced witness that the exact s 5B(1)(c) atom fails on
-- this case fibre.  It is not logical negation and does not establish an
-- opposite WrongType or proposition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic
import DASHI.Cognition.PNF.SensibLawNSWCivilLiabilityActAtomicSourceAtlasExact as CLA
import DASHI.Cognition.PNF.SensibLawCullenAtomicSourceConditionedDutyBreachExact as CullenAtomic
import DASHI.Cognition.PNF.SensibLawCullenDownstreamElementSourceAtlasExact as CullenElements

------------------------------------------------------------------------
-- 1. Direct HCA propositions used only as case-outcome evidence.
------------------------------------------------------------------------

joint39ForeseeableSatisfied : Algebra.LegalProposition
joint39ForeseeableSatisfied = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:joint39:s5B-1-a-satisfied")
  Algebra.adjudicatedFactRole
  (Ontology.stableId "risk:Cullen:physical-harm-crowd")
  (Ontology.stableId "section:NSW-CLA:5B-1-a")
  Negligence.auCommonLawSystem
  "joint reasons [39] conclude that s 5B(1)(a) was satisfied for the identified foreseeable physical-harm risk"

joint39NotInsignificantSatisfied : Algebra.LegalProposition
joint39NotInsignificantSatisfied = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:joint39:s5B-1-b-satisfied")
  Algebra.adjudicatedFactRole
  (Ontology.stableId "risk:Cullen:physical-harm-crowd")
  (Ontology.stableId "section:NSW-CLA:5B-1-b")
  Negligence.auCommonLawSystem
  "joint reasons [39] conclude that the relevant risk was not insignificant and s 5B(1)(b) was satisfied"

joint48ReasonablePrecautionsFailed : Algebra.LegalProposition
joint48ReasonablePrecautionsFailed = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:joint48:s5B-1-c-failed")
  Algebra.wrongElementPredicate
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "section:NSW-CLA:5B-1-c")
  Negligence.auCommonLawSystem
  "joint reasons [42]-[48] conclude that none of the proposed alternatives was a precaution a reasonable person in the OSG officers' position would have taken"

joint39ForeseeableSource : SourceRule.PropositionSourceReceipt joint39ForeseeableSatisfied
joint39ForeseeableSource = CullenAtomic.cullenPrimaryRatioReceipt
  joint39ForeseeableSatisfied refl
  "Cullen v New South Wales [2026] HCA 19, joint reasons [39]"
  "primary HCA application of s 5B(1)(a) to the Cullen facts"

joint39NotInsignificantSource : SourceRule.PropositionSourceReceipt joint39NotInsignificantSatisfied
joint39NotInsignificantSource = CullenAtomic.cullenPrimaryRatioReceipt
  joint39NotInsignificantSatisfied refl
  "Cullen v New South Wales [2026] HCA 19, joint reasons [39]"
  "primary HCA application of s 5B(1)(b) to the Cullen facts"

joint48ReasonablePrecautionsSource : SourceRule.PropositionSourceReceipt joint48ReasonablePrecautionsFailed
joint48ReasonablePrecautionsSource = CullenAtomic.cullenPrimaryRatioReceipt
  joint48ReasonablePrecautionsFailed refl
  "Cullen v New South Wales [2026] HCA 19, joint reasons [42]-[48]"
  "primary HCA application of s 5B(1)(c); negative atomic outcome only"

------------------------------------------------------------------------
-- 2. Outcome-source welds preserve statute-as-test / judgment-as-application.
------------------------------------------------------------------------

foreseeableOutcome : Atomic.AtomicOutcomeSource CLA.riskForeseeable
foreseeableOutcome = Atomic.atomic-outcome-source
  joint39ForeseeableSatisfied
  joint39ForeseeableSource
  (Algebra.propositionId CLA.riskForeseeable)
  refl refl
  "HCA [39] supplies positive outcome evidence for the statutory s 5B(1)(a) atom"

notInsignificantOutcome : Atomic.AtomicOutcomeSource CLA.riskNotInsignificant
notInsignificantOutcome = Atomic.atomic-outcome-source
  joint39NotInsignificantSatisfied
  joint39NotInsignificantSource
  (Algebra.propositionId CLA.riskNotInsignificant)
  refl refl
  "HCA [39] supplies positive outcome evidence for the statutory s 5B(1)(b) atom"

reasonablePrecautionsFailureOutcome :
  Atomic.AtomicOutcomeSource CLA.reasonablePersonWouldTakePrecautions
reasonablePrecautionsFailureOutcome = Atomic.atomic-outcome-source
  joint48ReasonablePrecautionsFailed
  joint48ReasonablePrecautionsSource
  (Algebra.propositionId CLA.reasonablePersonWouldTakePrecautions)
  refl refl
  "HCA [42]-[48] supplies positive failure evidence for the exact s 5B(1)(c) atom"

------------------------------------------------------------------------
-- 3. Exact atomic tests.
------------------------------------------------------------------------

data NoForeseeableFailure : Set where
data NoNotInsignificantFailure : Set where
data NoReasonablePrecautionsFit : Set where

cullenForeseeableAtom : Atomic.SourceConditionedAtomicLegalTest CLA.riskForeseeable
cullenForeseeableAtom = Atomic.source-conditioned-atomic-legal-test
  CLA.s5BForeseeableSource
  (Algebra.subjectReference CLA.riskForeseeable) refl
  (Atomic.AtomicOutcomeSource CLA.riskForeseeable)
  NoForeseeableFailure
  (λ fit ())
  (λ fit → fit)
  (λ ())
  BT.pos
  (λ _ → foreseeableOutcome)
  (λ ())
  "Cullen s5B(1)(a): positive atomic fit"

cullenNotInsignificantAtom :
  Atomic.SourceConditionedAtomicLegalTest CLA.riskNotInsignificant
cullenNotInsignificantAtom = Atomic.source-conditioned-atomic-legal-test
  CLA.s5BNotInsignificantSource
  (Algebra.subjectReference CLA.riskNotInsignificant) refl
  (Atomic.AtomicOutcomeSource CLA.riskNotInsignificant)
  NoNotInsignificantFailure
  (λ fit ())
  (λ fit → fit)
  (λ ())
  BT.pos
  (λ _ → notInsignificantOutcome)
  (λ ())
  "Cullen s5B(1)(b): positive atomic fit"

cullenReasonablePrecautionsAtom :
  Atomic.SourceConditionedAtomicLegalTest CLA.reasonablePersonWouldTakePrecautions
cullenReasonablePrecautionsAtom = Atomic.source-conditioned-atomic-legal-test
  CLA.s5BReasonablePrecautionsSource
  (Algebra.subjectReference CLA.reasonablePersonWouldTakePrecautions) refl
  NoReasonablePrecautionsFit
  (Atomic.AtomicOutcomeSource CLA.reasonablePersonWouldTakePrecautions)
  (λ () failure)
  (λ ())
  (λ failure → failure)
  BT.neg
  (λ ())
  (λ _ → reasonablePrecautionsFailureOutcome)
  "Cullen s5B(1)(c): negative means this exact proposed-precautions test fails"

------------------------------------------------------------------------
-- 4. The literal three-atom Cullen s5B fibre.
------------------------------------------------------------------------

record CullenS5BAtomicVector : Set₁ where
  constructor cullen-s5b-atomic-vector
  field
    foreseeable : Atomic.SourceConditionedAtomicLegalTest CLA.riskForeseeable
    notInsignificant : Atomic.SourceConditionedAtomicLegalTest CLA.riskNotInsignificant
    reasonablePrecautions :
      Atomic.SourceConditionedAtomicLegalTest CLA.reasonablePersonWouldTakePrecautions
    foreseeableGate : Atomic.gate foreseeable ≡ BT.pos
    notInsignificantGate : Atomic.gate notInsignificant ≡ BT.pos
    reasonablePrecautionsGate : Atomic.gate reasonablePrecautions ≡ BT.neg

open CullenS5BAtomicVector public

cullenS5BAtomicVector : CullenS5BAtomicVector
cullenS5BAtomicVector = cullen-s5b-atomic-vector
  cullenForeseeableAtom cullenNotInsignificantAtom cullenReasonablePrecautionsAtom
  refl refl refl

------------------------------------------------------------------------
-- 5. Consequences are fail-closed and atomic.
------------------------------------------------------------------------

data CullenS5BThresholdAllPositive : Set where
data NegativeS5B1CMeansOppositeWrong : Set where
data S5B1AFitPaysS5B1C : Set where
data JudgmentOutcomeReplacesStatutoryTestSource : Set where

cullenS5BIsNotAllPositive : CullenS5BThresholdAllPositive → ⊥
cullenS5BIsNotAllPositive ()

negativeS5B1CDoesNotMeanOppositeWrong : NegativeS5B1CMeansOppositeWrong → ⊥
negativeS5B1CDoesNotMeanOppositeWrong ()

foreseeabilityDoesNotPayReasonablePrecautions : S5B1AFitPaysS5B1C → ⊥
foreseeabilityDoesNotPayReasonablePrecautions ()

judgmentApplicationDoesNotReplaceStatutoryDefinition :
  JudgmentOutcomeReplacesStatutoryTestSource → ⊥
judgmentApplicationDoesNotReplaceStatutoryTestSource ()

------------------------------------------------------------------------
-- 6. Existing [48] breach result is consistent with, but not definitionally
-- identical to, the negative s5B(1)(c) atomic coordinate.
------------------------------------------------------------------------

record CullenBreachAtomicWeld : Set where
  constructor cullen-breach-atomic-weld
  field
    statutoryTest :
      Atomic.SourceConditionedAtomicLegalTest CLA.reasonablePersonWouldTakePrecautions
    statutoryTestIsNegative : Atomic.gate statutoryTest ≡ BT.neg
    primaryBreachDisposition : Algebra.LegalProposition
    primaryBreachDispositionIsJoint48 :
      primaryBreachDisposition ≡ CullenElements.joint48BreachNotEstablished
    sameSourceCase : Bool
    noIdentityBetweenElementDispositionAndAtomicTest : Bool

canonicalCullenBreachAtomicWeld : CullenBreachAtomicWeld
canonicalCullenBreachAtomicWeld = cullen-breach-atomic-weld
  cullenReasonablePrecautionsAtom refl
  CullenElements.joint48BreachNotEstablished refl true true
