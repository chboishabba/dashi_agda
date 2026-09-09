module DASHI.Law.SolomonIslandsWrongTypeLegalElementDerivationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Element
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Law.SolomonIslandsWrongTypeIntersectionalAdmissibilityExact as Solomon

------------------------------------------------------------------------
-- SECTION-LEVEL AUTHORITY -> WRONGTYPE LEGAL ELEMENT -> DERIVATION GATE
--
-- This module closes the next seam after the WrongType/non-factorability weld.
-- The legal rule does NOT have zero premises: source authority supplies the
-- rule, while a separate situated factual proposition must be present before
-- the statutory element can be derived.
------------------------------------------------------------------------

s92BenefitInfluenceFact : Algebra.LegalProposition
s92BenefitInfluenceFact = Algebra.legal-proposition
  (Ontology.stableId "prop:SB:s92:benefit-influence-fact")
  Algebra.relationalFeature
  (Ontology.stableId "actor:SB:public-official")
  (Ontology.stableId "relation:benefit-intended-to-influence-official-duty")
  Solomon.solomonSystemId
  "a benefit was promised, offered, given, solicited, accepted or received with the intent required by Anti-Corruption Act 2018 s 92 to influence official duties"

s92ElementProposition : Algebra.LegalProposition
s92ElementProposition = Algebra.legal-proposition
  (Ontology.stableId "prop:SB:s92:element-satisfied")
  Algebra.wrongElementPredicate
  (Ontology.WrongType.wrongTypeId Solomon.antiCorruptionSection92WrongType)
  (Ontology.stableId "element:SB:ACA2018:s92")
  Solomon.solomonSystemId
  "the Anti-Corruption Act 2018 s 92 benefit/influence element is satisfied for the selected event"

antiCorruptionSource : Ontology.LegalSource
antiCorruptionSource = Ontology.legalSource
  Solomon.antiCorruption92SourceId
  Solomon.solomonSystemId
  Ontology.statute
  "Anti-Corruption Act 2018 (Solomon Islands), s 92(1)-(2)"
  "2018"
  ""

antiCorruptionSourceRef : Algebra.LegalSourceRef
antiCorruptionSourceRef = Algebra.legal-source-ref
  antiCorruptionSource
  "Attorney-General's Chambers, Solomon Islands"
  "Anti-Corruption Act 2018"
  "Anti-Corruption Act 2018, s 92(1)-(2)"

s92Rule : Algebra.LegalRule
s92Rule = Algebra.legal-rule
  (Ontology.stableId "rule:SB:ACA2018:s92")
  (s92BenefitInfluenceFact ∷ [])
  s92ElementProposition
  []
  []
  antiCorruptionSourceRef
  Algebra.legislativeRuleRole
  "in-force statutory rule; current factual application requires event-time validity review"
  "Solomon Islands"

s92Element : Element.LegalElement Solomon.antiCorruptionSection92WrongType
s92Element = Element.legal-element
  (Ontology.stableId "element:SB:ACA2018:s92")
  Element.statutoryElement
  s92ElementProposition
  refl

s92Requirement : Element.ElementRequirement s92Element
s92Requirement = Element.element-requirement
  (Ontology.stableId "requirement:SB:ACA2018:s92:benefit-intent")
  s92BenefitInfluenceFact
  s92Rule
  ⊤

s92Graph : Algebra.LegalGraph
s92Graph = Algebra.legal-graph (s92Rule ∷ []) (antiCorruptionSourceRef ∷ [])

------------------------------------------------------------------------
-- Current facts deliberately do NOT contain the paying proposition.
------------------------------------------------------------------------

currentS92Facts : Algebra.FactSet
currentS92Facts = Algebra.fact-set []

record CurrentS92DerivationGate : Set where
  constructor current-s92-derivation-gate
  field
    sectionAuthorityMapped : Bool
    sectionAuthorityMappedIsTrue : sectionAuthorityMapped ≡ true
    wrongTypeMapped : Bool
    wrongTypeMappedIsTrue : wrongTypeMapped ≡ true
    legalElementMapped : Bool
    legalElementMappedIsTrue : legalElementMapped ≡ true
    elementRequirementMapped : Bool
    elementRequirementMappedIsTrue : elementRequirementMapped ≡ true
    payingSituatedFactAdmitted : Bool
    payingSituatedFactAdmittedIsFalse : payingSituatedFactAdmitted ≡ false
    applicabilityState : Status.ApplicabilityStatus
    applicabilityStateIsCandidate : applicabilityState ≡ Status.applicabilityCandidate
    derivationPromoted : Bool
    derivationPromotedIsFalse : derivationPromoted ≡ false

open CurrentS92DerivationGate public

currentS92DerivationGate : CurrentS92DerivationGate
currentS92DerivationGate = current-s92-derivation-gate
  true refl
  true refl
  true refl
  true refl
  false refl
  Status.applicabilityCandidate refl
  false refl

------------------------------------------------------------------------
-- Leadership Code s 17 gets the same proof-relevant shape.
------------------------------------------------------------------------

s17InducementFact : Algebra.LegalProposition
s17InducementFact = Algebra.legal-proposition
  (Ontology.stableId "prop:SB:s17:inducement-fact")
  Algebra.relationalFeature
  (Ontology.stableId "actor:SB:leader")
  (Ontology.stableId "relation:property-benefit-favour-as-consideration-inducement-reward")
  Solomon.solomonSystemId
  "property, benefit or favour was offered, given, sought or obtained with the consideration, inducement or reward nexus required by Leadership Code (Further Provisions) Act 1999 s 17"

s17ElementProposition : Algebra.LegalProposition
s17ElementProposition = Algebra.legal-proposition
  (Ontology.stableId "prop:SB:s17:element-satisfied")
  Algebra.wrongElementPredicate
  (Ontology.WrongType.wrongTypeId Solomon.leadershipSection17WrongType)
  (Ontology.stableId "element:SB:Leadership1999:s17")
  Solomon.solomonSystemId
  "the Leadership Code s 17 bribery/inducement element is satisfied for the selected event"

leadershipSource : Ontology.LegalSource
leadershipSource = Ontology.legalSource
  Solomon.leadership17SourceId
  Solomon.solomonSystemId
  Ontology.statute
  "Leadership Code (Further Provisions) Act 1999 (Solomon Islands), s 17(1)-(3)"
  "1999"
  ""

leadershipSourceRef : Algebra.LegalSourceRef
leadershipSourceRef = Algebra.legal-source-ref
  leadershipSource
  "Attorney-General's Chambers, Solomon Islands"
  "Leadership Code (Further Provisions) Act 1999"
  "Leadership Code (Further Provisions) Act 1999, s 17(1)-(3)"

s17Rule : Algebra.LegalRule
s17Rule = Algebra.legal-rule
  (Ontology.stableId "rule:SB:Leadership1999:s17")
  (s17InducementFact ∷ [])
  s17ElementProposition
  []
  []
  leadershipSourceRef
  Algebra.legislativeRuleRole
  "authorised reprint current 5 February 2024; event-time application separately reviewed"
  "Solomon Islands"

s17Element : Element.LegalElement Solomon.leadershipSection17WrongType
s17Element = Element.legal-element
  (Ontology.stableId "element:SB:Leadership1999:s17")
  Element.statutoryElement
  s17ElementProposition
  refl

s17Requirement : Element.ElementRequirement s17Element
s17Requirement = Element.element-requirement
  (Ontology.stableId "requirement:SB:Leadership1999:s17:inducement")
  s17InducementFact
  s17Rule
  ⊤

------------------------------------------------------------------------
-- Firewalls: law gives the implication; evidence must supply the premise.
------------------------------------------------------------------------

data AuthorityRuleAutomaticallySuppliesFact : Set where
data CandidateApplicabilityAutomaticallyDerivesElement : Set where
data ElementRequirementAutomaticallyIsElementDerivation : Set where

authorityDoesNotManufacturePremise : AuthorityRuleAutomaticallySuppliesFact → ⊥
authorityDoesNotManufacturePremise ()

candidateDoesNotDeriveElement : CandidateApplicabilityAutomaticallyDerivesElement → ⊥
candidateDoesNotDeriveElement ()

requirementDoesNotEqualDerivation : ElementRequirementAutomaticallyIsElementDerivation → ⊥
requirementDoesNotEqualDerivation ()
