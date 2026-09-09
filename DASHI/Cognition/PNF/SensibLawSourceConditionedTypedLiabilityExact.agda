module DASHI.Cognition.PNF.SensibLawSourceConditionedTypedLiabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Cognition.PNF.SensibLawWrongTypeDownstreamPrimarySourceDisciplineExact as Downstream
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic
import DASHI.Cognition.PNF.SensibLawSourceConditionedAtomicLegalImplicationExact as AtomicImplication
import DASHI.Cognition.PNF.SensibLawSourceConditionedApplicabilityViolationExact as SourceViolation

liabilityFamilyId : Downstream.LiabilityFamily → Ontology.StableId
liabilityFamilyId Downstream.directWrongTypeLiability = Ontology.stableId "liability-family:direct-wrongtype"
liabilityFamilyId Downstream.vicariousLiability = Ontology.stableId "liability-family:vicarious"
liabilityFamilyId Downstream.statutoryLiability = Ontology.stableId "liability-family:statutory"
liabilityFamilyId Downstream.contributionLiability = Ontology.stableId "liability-family:contribution"
liabilityFamilyId Downstream.indemnityLiability = Ontology.stableId "liability-family:indemnity"
liabilityFamilyId Downstream.publicAuthorityLiability = Ontology.stableId "liability-family:public-authority"
liabilityFamilyId (Downstream.namedLiabilityFamily name) = Ontology.stableId name

record SourceConditionedTypedLiabilityProfile
    {wrong : Ontology.WrongType}
    (profile : Downstream.TypedLiabilityProfile wrong) : Set₁ where
  constructor source-conditioned-typed-liability-profile
  field
    familyRecognitionProposition : Algebra.LegalProposition
    familyRecognitionSource : SourceRule.PropositionSourceReceipt familyRecognitionProposition
    familyRecognitionTargetsFamily :
      Algebra.objectReference familyRecognitionProposition ≡ liabilityFamilyId (Downstream.family profile)
    familyRecognitionSystemMatchesWrongType :
      Algebra.legalSystem familyRecognitionProposition ≡ Ontology.WrongType.definingSystem wrong
    familyRecognitionRule : Algebra.LegalRule
    familyRecognitionRuleSource : SourceRule.SourceRealisedLegalRule familyRecognitionRule
    familyRecognitionRuleConclusion : Algebra.conclusion familyRecognitionRule ≡ familyRecognitionProposition
    conditionSource :
      ∀ {p} → p Algebra.∈ Downstream.conditions profile → SourceRule.PropositionSourceReceipt p
    limitationSource :
      ∀ {p} → p Algebra.∈ Downstream.limitationsAndDefeaters profile → SourceRule.PropositionSourceReceipt p
    temporalPredicate : Algebra.LegalProposition
    temporalSource : SourceRule.PropositionSourceReceipt temporalPredicate
    temporalPredicateKind : Algebra.propositionKind temporalPredicate ≡ Algebra.temporalPredicate
    competencePredicate : Algebra.LegalProposition
    competenceSource : SourceRule.PropositionSourceReceipt competencePredicate
    competencePredicateKind : Algebra.propositionKind competencePredicate ≡ Algebra.jurisdictionPredicate
    profileSystemMatchesFamilyRecognition :
      Downstream.profileSystem profile ≡ Algebra.legalSystem familyRecognitionProposition
    profileReference : String

open SourceConditionedTypedLiabilityProfile public

record SourceConditionedTypedLiabilityDecision
    {state : Status.SemanticCommitmentState}
    {wrong : Ontology.WrongType}
    {bundle : Elements.WrongTypeRuleBundle wrong}
    {facts : Algebra.FactSet}
    (liabilityGraph : Algebra.LegalGraph)
    (profile : Downstream.TypedLiabilityProfile wrong)
    (realised : SourceConditionedTypedLiabilityProfile profile) : Set₁ where
  constructor source-conditioned-typed-liability-decision
  field
    sourceConditionedViolation : SourceViolation.SourceConditionedViolation {state} wrong bundle facts
    legacyDecision : Downstream.SourceAttributedLiabilityDecision {state} profile
    sameViolationReceipt :
      Legal.violationReceipt (Downstream.liabilityReceipt legacyDecision)
      ≡ SourceViolation.legacyViolationProjection sourceConditionedViolation

    familyRecognitionImplication :
      AtomicImplication.SourceConditionedAtomicLegalImplication
        liabilityGraph facts (λ _ → ⊤) (familyRecognitionRule realised)
    familyRecognitionUsesCanonicalRuleSource :
      AtomicImplication.sourceRealisation familyRecognitionImplication ≡ familyRecognitionRuleSource realised
    familyRecognitionDerivationReceipt :
      AtomicImplication.AtomicImplicationDerivationReceipt familyRecognitionImplication

    familyRecognitionAtom : Atomic.SourceConditionedAtomicLegalTest (familyRecognitionProposition realised)
    familyAtomUsesCanonicalSource : Atomic.sourceReceipt familyRecognitionAtom ≡ familyRecognitionSource realised
    familyRecognized : Atomic.gate familyRecognitionAtom ≡ BT.pos
    familyRecognitionDerived :
      Algebra.Derivation liabilityGraph facts (λ _ → ⊤) (familyRecognitionProposition realised)

    conditionAtom :
      ∀ {p} → (membership : p Algebra.∈ Downstream.conditions profile) → Atomic.SourceConditionedAtomicLegalTest p
    conditionAtomUsesCanonicalSource :
      ∀ {p} (membership : p Algebra.∈ Downstream.conditions profile) →
      Atomic.sourceReceipt (conditionAtom membership) ≡ conditionSource realised membership
    conditionPasses :
      ∀ {p} (membership : p Algebra.∈ Downstream.conditions profile) →
      Atomic.gate (conditionAtom membership) ≡ BT.pos
    conditionDerived :
      ∀ {p} → p Algebra.∈ Downstream.conditions profile → Algebra.Derivation liabilityGraph facts (λ _ → ⊤) p

    limitationAtom :
      ∀ {p} → (membership : p Algebra.∈ Downstream.limitationsAndDefeaters profile) → Atomic.SourceConditionedAtomicLegalTest p
    limitationAtomUsesCanonicalSource :
      ∀ {p} (membership : p Algebra.∈ Downstream.limitationsAndDefeaters profile) →
      Atomic.sourceReceipt (limitationAtom membership) ≡ limitationSource realised membership
    limitationFailsToApply :
      ∀ {p} (membership : p Algebra.∈ Downstream.limitationsAndDefeaters profile) →
      Atomic.gate (limitationAtom membership) ≡ BT.neg
    limitationNotDerived :
      ∀ {p} → p Algebra.∈ Downstream.limitationsAndDefeaters profile →
      Algebra.Derivation liabilityGraph facts (λ _ → ⊤) p → ⊥

    temporalAtom : Atomic.SourceConditionedAtomicLegalTest (temporalPredicate realised)
    temporalAtomUsesCanonicalSource : Atomic.sourceReceipt temporalAtom ≡ temporalSource realised
    temporalPasses : Atomic.gate temporalAtom ≡ BT.pos
    temporalDerived : Algebra.Derivation liabilityGraph facts (λ _ → ⊤) (temporalPredicate realised)

    competenceAtom : Atomic.SourceConditionedAtomicLegalTest (competencePredicate realised)
    competenceAtomUsesCanonicalSource : Atomic.sourceReceipt competenceAtom ≡ competenceSource realised
    competencePasses : Atomic.gate competenceAtom ≡ BT.pos
    competenceDerived : Algebra.Derivation liabilityGraph facts (λ _ → ⊤) (competencePredicate realised)

    courtCompetence : Downstream.CourtCompetenceReceipt {state} profile
    decisionReference : String

open SourceConditionedTypedLiabilityDecision public

data TypedFamilyConstructorCreatesLegalRecognition : Set where
data SourceAttributedProfileIsSourceConditionedProfile : Set where
data NegativeLimitationAtomProvesOppositeProposition : Set where
data FailedConditionProvesDifferentLiabilityFamily : Set where
data ViolationAutomaticallyChoosesLiabilityFamily : Set where
data LiabilityFamilyAutomaticallyChoosesRemedy : Set where
data FamilySourceMetadataAloneCountsAsRecognition : Set where

typedFamilyConstructorDoesNotCreateRecognition : TypedFamilyConstructorCreatesLegalRecognition → ⊥
typedFamilyConstructorDoesNotCreateRecognition ()
sourceAttributedProfileDoesNotEqualSourceConditionedProfile : SourceAttributedProfileIsSourceConditionedProfile → ⊥
sourceAttributedProfileDoesNotEqualSourceConditionedProfile ()
negativeLimitationAtomDoesNotProveOpposite : NegativeLimitationAtomProvesOppositeProposition → ⊥
negativeLimitationAtomDoesNotProveOpposite ()
failedConditionDoesNotChooseDifferentFamily : FailedConditionProvesDifferentLiabilityFamily → ⊥
failedConditionDoesNotChooseDifferentFamily ()
violationDoesNotChooseLiabilityFamily : ViolationAutomaticallyChoosesLiabilityFamily → ⊥
violationDoesNotChooseLiabilityFamily ()
liabilityFamilyDoesNotChooseRemedy : LiabilityFamilyAutomaticallyChoosesRemedy → ⊥
liabilityFamilyDoesNotChooseRemedy ()
familyMetadataDoesNotCountAsRecognition : FamilySourceMetadataAloneCountsAsRecognition → ⊥
familyMetadataDoesNotCountAsRecognition ()

record SourceConditionedTypedLiabilityBoundary : Set where
  constructor source-conditioned-typed-liability-boundary
  field
    typedFamilySchemaNeedsSourceRealisation : Bool
    familyRecognitionNeedsAtomicSourceConditionedImplication : Bool
    everyPositiveConditionIsAtomicAndSourceConditioned : Bool
    everyLimitationIsAtomicAndSourceConditioned : Bool
    negativeMeansFailureOfSameAtom : Bool
    negativeMeansOppositeLegalProposition : Bool
    temporalValidityIsSourceConditioned : Bool
    courtCompetenceIsSourceConditioned : Bool
    violationChoosesLiabilityFamily : Bool
    liabilityFamilyChoosesRemedy : Bool

canonicalSourceConditionedTypedLiabilityBoundary : SourceConditionedTypedLiabilityBoundary
canonicalSourceConditionedTypedLiabilityBoundary =
  source-conditioned-typed-liability-boundary true true true true true false true true false false
