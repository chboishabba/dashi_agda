module DASHI.Cognition.PNF.SensibLawCullenVicariousLiabilityFamilyAtomicExact where

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
import DASHI.Cognition.PNF.SensibLawWrongTypeDownstreamPrimarySourceDisciplineExact as Downstream
import DASHI.Cognition.PNF.SensibLawSourceConditionedTypedLiabilityExact as Typed
import DASHI.Cognition.PNF.SensibLawRecentDutyCaseSourceAtlasExact as CullenSource
import DASHI.Cognition.PNF.SensibLawNSWVicariousLiabilityActAtomicSourceAtlasExact as Act

cullen100Locator : String
cullen100Locator = "Cullen v New South Wales [2026] HCA 19, Edelman J [100]"

cullenVicariousCharacterisation : Algebra.LegalProposition
cullenVicariousCharacterisation = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:Edelman:100:true-vicarious-liability")
  Algebra.doctrinalPredicate
  (Ontology.stableId "party:State-of-New-South-Wales")
  (Typed.liabilityFamilyId Downstream.vicariousLiability)
  Negligence.auCommonLawSystem
  "the State liability route for established police tort liability is accurately characterised as true vicarious liability"

cullen100Authority : Edge.SourceIdentity
cullen100Authority = Edge.source-identity
  "High Court of Australia; Edelman J"
  "Cullen v New South Wales"
  "[2026] HCA 19, Edelman J [100]"
  Edge.bindingPrecedent

-- Edelman J wrote separately in concurrence.  The case source remains High
-- Court primary material, but this proposition-level role is not flattened into
-- the joint-reasons binding-ratio fibre.
cullen100Role : SourceRole.SourceFormRoleReceipt
cullen100Role = SourceRole.source-form-role-receipt
  cullen100Authority Ontology.caseLaw Algebra.concurrenceRole
  "Cullen-Edelman-100-vicarious-characterisation" true true

cullen100LegalSourceRef : Algebra.LegalSourceRef
cullen100LegalSourceRef = Algebra.legal-source-ref
  (Ontology.legalSource
    (Ontology.stableId "source:Cullen:[2026]HCA19")
    Negligence.auCommonLawSystem Ontology.caseLaw "[2026] HCA 19"
    "2026-06-17" "Australia / High Court")
  "High Court of Australia" "Cullen v New South Wales" "[2026] HCA 19"

cullen100SourceReceipt : SourceRule.PropositionSourceReceipt cullenVicariousCharacterisation
cullen100SourceReceipt = SourceRule.proposition-source-receipt
  CullenSource.cullenHCA19 cullen100LegalSourceRef cullen100Locator
  SourceRule.primarySourceLayer cullen100Role refl refl refl
  (Source.citationCreatesAuthorityIsFalse CullenSource.cullenHCA19)
  "Cullen-Edelman-100"

data CullenVicariousFits : Set where
  cullen100IdentifiesVicariousFamily : CullenVicariousFits

data CullenVicariousFails : Set where

cullenVicariousOutcome : Atomic.AtomicOutcomeSource Act.crownVicariousLiabilityRecognised
cullenVicariousOutcome = Atomic.atomic-outcome-source
  cullenVicariousCharacterisation cullen100SourceReceipt
  (Algebra.propositionId Act.crownVicariousLiabilityRecognised)
  refl refl
  "Edelman [100] positively identifies the State's police-tort attribution route as true vicarious liability; the statute remains the definition/recognition source."

cullenVicariousFamilyAtom : Atomic.SourceConditionedAtomicLegalTest Act.crownVicariousLiabilityRecognised
cullenVicariousFamilyAtom = Atomic.source-conditioned-atomic-legal-test
  Act.s8FamilySource
  (Algebra.subjectReference Act.crownVicariousLiabilityRecognised)
  refl
  CullenVicariousFits CullenVicariousFails
  (λ _ ())
  (λ _ → cullenVicariousOutcome)
  (λ ())
  BT.pos
  (λ _ → cullen100IdentifiesVicariousFamily)
  (λ ())
  "Cullen liability-family axis = +1 for the exact vicarious-liability family, conditional on an underlying police tort being established."

cullenVicariousFamilyIsPositive : Atomic.gate cullenVicariousFamilyAtom ≡ BT.pos
cullenVicariousFamilyIsPositive = refl

record CullenVicariousFamilyReceipt : Set₁ where
  constructor cullen-vicarious-family-receipt
  field
    wrongType : Ontology.WrongType
    wrongTypeIsNegligence : wrongType ≡ Negligence.negligenceWrongType
    family : Downstream.LiabilityFamily
    familyIsVicarious : family ≡ Downstream.vicariousLiability
    statutoryDefinitionSource : SourceRule.PropositionSourceReceipt Act.crownVicariousLiabilityRecognised
    caseOutcomeAtom : Atomic.SourceConditionedAtomicLegalTest Act.crownVicariousLiabilityRecognised
    caseOutcomePositive : Atomic.gate caseOutcomeAtom ≡ BT.pos
    familyObjectMatchesTypedFamily :
      Algebra.objectReference Act.crownVicariousLiabilityRecognised
      ≡ Typed.liabilityFamilyId family
    underlyingTortStillRequired : Bool
    receiptReference : String

open CullenVicariousFamilyReceipt public

cullenVicariousFamilyReceipt : CullenVicariousFamilyReceipt
cullenVicariousFamilyReceipt = cullen-vicarious-family-receipt
  Negligence.negligenceWrongType refl
  Downstream.vicariousLiability refl
  Act.s8FamilySource
  cullenVicariousFamilyAtom refl refl
  true
  "Cullen [100] concurrence + NSW Law Reform (Vicarious Liability) Act 1983 source-weld family=vicarious; underlying tort/violation remains an independent prerequisite."

data FamilyRecognitionProvesUnderlyingTort : Set where
data S9BClaimRoutingCreatesFamily : Set where
data S9EAntiCreationNegatesFamily : Set where
data VicariousFamilyMeansPublicAuthorityLiabilityFamily : Set where
data FamilyRecognitionProvesDamagesEntitlement : Set where
data ConcurrenceAutomaticallyBecomesJointRatio : Set where

familyRecognitionDoesNotProveTort : FamilyRecognitionProvesUnderlyingTort → ⊥
familyRecognitionDoesNotProveTort ()
s9BDoesNotCreateFamily : S9BClaimRoutingCreatesFamily → ⊥
s9BDoesNotCreateFamily ()
s9EDoesNotNegateFamily : S9EAntiCreationNegatesFamily → ⊥
s9EDoesNotNegateFamily ()
vicariousDoesNotCollapseToPublicAuthorityFamily : VicariousFamilyMeansPublicAuthorityLiabilityFamily → ⊥
vicariousDoesNotCollapseToPublicAuthorityFamily ()
familyDoesNotProveDamages : FamilyRecognitionProvesDamagesEntitlement → ⊥
familyDoesNotProveDamages ()
concurrenceDoesNotBecomeJointRatio : ConcurrenceAutomaticallyBecomesJointRatio → ⊥
concurrenceDoesNotBecomeJointRatio ()
