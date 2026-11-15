module DASHI.Core.ReopenableConsumerInterventionKernelExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Project-neutral kernel extracted from the convergent LES, Animalexic and
-- SeaMeInIt architectures.  The domains differ, but all three repeatedly need
-- consumer-relative descent, intertwining/commutation checks, reopenable
-- alternatives, explicit authority promotion, typed uncertainty, and bounded
-- completeness relative to a declared admissible language.
--
-- This module intentionally contains no ecological, garment, animal-behaviour,
-- or ontology assumptions.  Domain projects should instantiate these surfaces
-- rather than reimplement their semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- 1. Consumer-relative descent through a projection.
------------------------------------------------------------------------

record ConsumerDescent
    {Fine Coarse Output : Set}
    (project : Fine → Coarse)
    (consume : Fine → Output) : Set₁ where
  constructor consumerDescent
  field
    quotientConsumer : Coarse → Output
    factorises :
      ∀ fine → consume fine ≡ quotientConsumer (project fine)

open ConsumerDescent public

record ConsumerDescentDefect
    {Fine Coarse Output : Set}
    (project : Fine → Coarse)
    (consume : Fine → Output) : Set where
  constructor consumerDescentDefect
  field
    left right : Fine
    sameProjection : project left ≡ project right
    consumerDistinguishes : consume left ≡ consume right → ⊥

open ConsumerDescentDefect public

consumerDescentDefectContradictsDescent :
  ∀ {Fine Coarse Output}
    {project : Fine → Coarse}
    {consume : Fine → Output} →
  ConsumerDescent project consume →
  ConsumerDescentDefect project consume →
  ⊥
consumerDescentDefectContradictsDescent descent defect =
  consumerDistinguishes defect
    (trans
      (factorises descent (left defect))
      (trans
        (cong (quotientConsumer descent) (sameProjection defect))
        (sym (factorises descent (right defect)))))

------------------------------------------------------------------------
-- 2. Generic intertwining / commutation law and explicit defect witness.
------------------------------------------------------------------------

record Intertwiner
    {FineIn FineOut CoarseIn CoarseOut : Set}
    (projectIn : FineIn → CoarseIn)
    (projectOut : FineOut → CoarseOut)
    (fineMap : FineIn → FineOut)
    (coarseMap : CoarseIn → CoarseOut) : Set₁ where
  constructor intertwiner
  field
    commutes :
      ∀ fine →
      projectOut (fineMap fine) ≡ coarseMap (projectIn fine)

open Intertwiner public

record IntertwiningDefect
    {FineIn FineOut CoarseIn CoarseOut : Set}
    (projectIn : FineIn → CoarseIn)
    (projectOut : FineOut → CoarseOut)
    (fineMap : FineIn → FineOut)
    (coarseMap : CoarseIn → CoarseOut) : Set where
  constructor intertwiningDefect
  field
    witnessInput : FineIn
    commutationFails :
      projectOut (fineMap witnessInput)
      ≡ coarseMap (projectIn witnessInput) → ⊥

open IntertwiningDefect public

intertwiningDefectContradictsIntertwiner :
  ∀ {FineIn FineOut CoarseIn CoarseOut}
    {projectIn : FineIn → CoarseIn}
    {projectOut : FineOut → CoarseOut}
    {fineMap : FineIn → FineOut}
    {coarseMap : CoarseIn → CoarseOut} →
  Intertwiner projectIn projectOut fineMap coarseMap →
  IntertwiningDefect projectIn projectOut fineMap coarseMap →
  ⊥
intertwiningDefectContradictsIntertwiner witness defect =
  commutationFails defect (commutes witness (witnessInput defect))

------------------------------------------------------------------------
-- 3. Alternatives are triaged, not collapsed to active versus false.
------------------------------------------------------------------------

data AlternativeStatus : Set where
  active : AlternativeStatus
  reopenable : AlternativeStatus
  refuted : AlternativeStatus

record Alternative (Payload : Set) : Set where
  constructor alternative
  field
    payload : Payload
    status : AlternativeStatus
    provenance : List String
    dependencies : List String
    scoreOrOrderReference : String

open Alternative public

record LiveAlternativeFamily (Payload : Set) : Set where
  constructor liveAlternativeFamily
  field
    alternatives : List (Alternative Payload)
    activeBound : Nat
    pruningPolicy : String
    residualReopeningPolicy : String
    excludedRequiresRefutationEvidence : Bool

open LiveAlternativeFamily public

record AlternativeTriageBoundary : Set where
  constructor alternativeTriageBoundary
  field
    inactiveDoesNotMeanRefuted : Bool
    pruningDoesNotMeanRefutation : Bool
    reopenableStateRetainsDependencies : Bool
    refutationNeedsDomainEvidence : Bool

open AlternativeTriageBoundary public

canonicalAlternativeTriageBoundary : AlternativeTriageBoundary
canonicalAlternativeTriageBoundary =
  alternativeTriageBoundary true true true true

------------------------------------------------------------------------
-- 4. Evidence distinctions and provenance roots.
------------------------------------------------------------------------

data EvidenceDisposition : Set where
  support : EvidenceDisposition
  opposition : EvidenceDisposition
  ignorance : EvidenceDisposition
  conflict : EvidenceDisposition

data EvidenceKind : Set where
  proofEvidence : EvidenceKind
  measurementEvidence : EvidenceKind
  statisticalEvidence : EvidenceKind
  expertEvidence : EvidenceKind
  hypothesisEvidence : EvidenceKind

record EvidenceItem : Set where
  constructor evidenceItem
  field
    evidenceId : String
    provenanceRoot : String
    kind : EvidenceKind
    disposition : EvidenceDisposition
    reliabilityBasis : String
    scope : String

open EvidenceItem public

record EvidenceIndependenceReceipt : Set where
  constructor evidenceIndependenceReceipt
  field
    evidence : List EvidenceItem
    distinctProvenanceRoots : List String
    independenceCriterion : String
    noDownstreamMultiplicityInflation : Bool

open EvidenceIndependenceReceipt public

------------------------------------------------------------------------
-- 5. Uncertainty axes remain typed rather than scalarised prematurely.
------------------------------------------------------------------------

data UncertaintyAxis : Set where
  epistemic : UncertaintyAxis
  fidelity : UncertaintyAxis
  scenario : UncertaintyAxis
  aleatoric : UncertaintyAxis

record TypedUncertainty : Set where
  constructor typedUncertainty
  field
    axis : UncertaintyAxis
    magnitude : Nat
    basis : String
    provenance : List String

open TypedUncertainty public

------------------------------------------------------------------------
-- 6. Authority is a separate promotion relation from computation/evidence.
------------------------------------------------------------------------

data AuthorityLevel : Set where
  computed : AuthorityLevel
  validated : AuthorityLevel
  supported : AuthorityLevel
  authorised : AuthorityLevel
  actionable : AuthorityLevel

record PromotionWitness
    {Carrier : Set}
    (item : Carrier) : Set where
  constructor promotionWitness
  field
    fromLevel : AuthorityLevel
    toLevel : AuthorityLevel
    policyReference : String
    evidenceReferences : List String
    authorityReference : String
    scope : String

open PromotionWitness public

record AuthorityBoundary : Set where
  constructor authorityBoundary
  field
    computationDoesNotImplyValidation : Bool
    validationDoesNotImplySupport : Bool
    supportDoesNotImplyAuthorisation : Bool
    authorisationDoesNotAutomaticallyImplyActionability : Bool
    moreEvidenceDoesNotAutomaticallyRaiseAuthority : Bool

open AuthorityBoundary public

canonicalAuthorityBoundary : AuthorityBoundary
canonicalAuthorityBoundary =
  authorityBoundary true true true true true

------------------------------------------------------------------------
-- 7. Proof-carrying state records validity plus the conditions that can reopen
--    it.  A hash alone is not the validity predicate.
------------------------------------------------------------------------

record ProofCarryingReopenableState
    (Carrier Change : Set)
    (Valid : Carrier → Set) : Set₁ where
  constructor proofCarryingReopenableState
  field
    state : Carrier
    validity : Valid state
    dependencyReferences : List String
    ChangeAffects : Change → Set
    reopenPolicy : String
    provenance : List String

open ProofCarryingReopenableState public

------------------------------------------------------------------------
-- 8. Bounded completeness is always relative to a declared admissible set.
------------------------------------------------------------------------

record BoundedEnumeration
    {Item : Set}
    (Admissible : Item → Set) : Set₁ where
  constructor boundedEnumeration
  field
    enumerated : List Item
    languageReference : String
    horizonOrDepth : Nat
    completeRelativeToDeclaredLanguage :
      ∀ item → Admissible item → item ∈ enumerated

open BoundedEnumeration public

record BoundedCompletenessBoundary : Set where
  constructor boundedCompletenessBoundary
  field
    finiteExhaustionIsLanguageRelative : Bool
    boundedExhaustionDoesNotProveContinuousGlobalOptimality : Bool
    searchFrontierTerminationIsNotCompletenessByItself : Bool

open BoundedCompletenessBoundary public

canonicalBoundedCompletenessBoundary : BoundedCompletenessBoundary
canonicalBoundedCompletenessBoundary =
  boundedCompletenessBoundary true true true

------------------------------------------------------------------------
-- 9. Shared claim boundary.
------------------------------------------------------------------------

record ReopenableConsumerInterventionBoundary : Set where
  constructor reopenableConsumerInterventionBoundary
  field
    descentIsConsumerRelative : Bool
    commutationMustBeProvedPerMap : Bool
    ambiguityCanRemainFirstClass : Bool
    evidenceMultiplicityNeedsProvenanceAccounting : Bool
    uncertaintyAxesShouldNotBeSilentlyCollapsed : Bool
    authorityNeedsExplicitPromotion : Bool
    validStateCanRequireReopeningAfterDependencyChange : Bool
    boundedCompletenessNeedsDeclaredLanguage : Bool

open ReopenableConsumerInterventionBoundary public

canonicalReopenableConsumerInterventionBoundary :
  ReopenableConsumerInterventionBoundary
canonicalReopenableConsumerInterventionBoundary =
  reopenableConsumerInterventionBoundary
    true true true true true true true true
