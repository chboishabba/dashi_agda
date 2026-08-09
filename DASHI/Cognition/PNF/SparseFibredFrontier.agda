module DASHI.Cognition.PNF.SparseFibredFrontier where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.DemandResolutionState
open import DASHI.Cognition.PNF.NumericAuthority
open import DASHI.Cognition.PNF.ParentInterfaceReduction

------------------------------------------------------------------------
-- A closed fibre hides its interior.  The only semantic values observable by
-- a parent are admitted exports, compressed actor/action summaries, unresolved
-- typed demands, and explicit scope or definition declarations.
------------------------------------------------------------------------

data BoundaryCarrier : Set where
  promotedExportCarrier : BoundaryCarrier
  actorActionSummaryCarrier : BoundaryCarrier
  unresolvedDemandCarrier : BoundaryCarrier
  explicitScopeCarrier : BoundaryCarrier

data BoundaryAdmission : Set where
  admittedBoundary rejectedInterior : BoundaryAdmission

data OutsideObservation : BoundaryAdmission → BoundaryCarrier → Set where
  observePromotedExport :
    OutsideObservation admittedBoundary promotedExportCarrier
  observeActorActionSummary :
    OutsideObservation admittedBoundary actorActionSummaryCarrier
  observeUnresolvedDemand :
    OutsideObservation admittedBoundary unresolvedDemandCarrier
  observeExplicitScope :
    OutsideObservation admittedBoundary explicitScopeCarrier

closedInteriorCannotEscape :
  ∀ {carrier} → OutsideObservation rejectedInterior carrier → ⊥
closedInteriorCannotEscape ()

record ClosedFibreBoundary : Set where
  constructor closedFibreBoundary
  field
    retainedChildEvidenceState : ChildEvidenceState
    rejectedInteriorHasNoOutsideObservation :
      ∀ {carrier} → OutsideObservation rejectedInterior carrier → ⊥

open ClosedFibreBoundary public

canonicalClosedFibreBoundary : ClosedFibreBoundary
canonicalClosedFibreBoundary =
  closedFibreBoundary retainedChildEvidence closedInteriorCannotEscape

------------------------------------------------------------------------
-- A typed demand is a hole constrained by target, discourse role, factor
-- participation, lexical evidence, residual class, and structural scope.  It
-- is not an unrestricted search over every object in the document.
------------------------------------------------------------------------

record TypedBoundaryDemand : Set where
  constructor typedBoundaryDemand
  field
    typedDemandIdentity : DemandId
    expectedTargetKind : Nat
    expectedObjectKind : Nat
    expectedRole : Nat
    expectedFactorType : Nat
    expectedPredicate : Nat
    residualClass : Nat
    scopeClass : Nat

open TypedBoundaryDemand public

record ActorActionSummary : Set where
  constructor actorActionSummary
  field
    actorIdentity : Nat
    actorKind : Nat
    actorRole : Nat
    participatingFactorType : Nat
    participatingPredicate : Nat
    occurrenceCount : Nat
    firstPosition lastPosition : Nat

open ActorActionSummary public

data Compatibility : TypedBoundaryDemand → ActorActionSummary → Set where
  compatibleSummary :
    ∀ {demand summary} →
    expectedObjectKind demand ≡ actorKind summary →
    expectedRole demand ≡ actorRole summary →
    expectedFactorType demand ≡ participatingFactorType summary →
    expectedPredicate demand ≡ participatingPredicate summary →
    Compatibility demand summary

record WitnessedActorBinding
  (demand : TypedBoundaryDemand)
  (summary : ActorActionSummary) : Set where
  constructor witnessedActorBinding
  field
    compatibilityWitness : Compatibility demand summary
    selectedTarget : ResolvedTarget
    selectedActorIdentityMatchesSummary :
      resolvedIdentity selectedTarget ≡ actorIdentity summary

open WitnessedActorBinding public

------------------------------------------------------------------------
-- Candidate multiplicity is preserved.  Only exactly one compatible witness
-- grants a resolved target.  Zero witnesses remain open/deferred and several
-- witnesses remain ambiguous.
------------------------------------------------------------------------

data WitnessMultiplicity : Set where
  noWitness oneWitness severalWitnesses : WitnessMultiplicity

data FrontierOutcome : WitnessMultiplicity → Set where
  noLocalWitness : FrontierOutcome noWitness
  resolvedUniqueWitness :
    ResolvedTarget → FrontierOutcome oneWitness
  ambiguousWitnesses : FrontierOutcome severalWitnesses

uniqueFrontierOutcomeCarriesTarget :
  FrontierOutcome oneWitness → ResolvedTarget
uniqueFrontierOutcomeCarriesTarget (resolvedUniqueWitness target) = target

noWitnessCannotClaimUniqueResolution :
  FrontierOutcome noWitness →
  FrontierOutcome oneWitness →
  noWitness ≡ oneWitness → ⊥
noWitnessCannotClaimUniqueResolution noLocalWitness unique ()

severalWitnessesCannotClaimUniqueResolution :
  FrontierOutcome severalWitnesses →
  FrontierOutcome oneWitness →
  severalWitnesses ≡ oneWitness → ⊥
severalWitnessesCannotClaimUniqueResolution ambiguousWitnesses unique ()

record RootDemandDisposition (multiplicity : WitnessMultiplicity) : Set where
  constructor rootDemandDisposition
  field
    localOutcome : FrontierOutcome multiplicity
    rootDemandState : DemandStatus

open RootDemandDisposition public

rootNoWitnessDefersToWorld : RootDemandDisposition noWitness
rootNoWitnessDefersToWorld =
  rootDemandDisposition noLocalWitness deferredWorldDemand

rootUniqueWitnessResolves :
  ResolvedTarget → RootDemandDisposition oneWitness
rootUniqueWitnessResolves target =
  rootDemandDisposition (resolvedUniqueWitness target) resolvedDemand

rootSeveralWitnessesRemainOpen :
  RootDemandDisposition severalWitnesses
rootSeveralWitnessesRemainOpen =
  rootDemandDisposition ambiguousWitnesses openDemand

------------------------------------------------------------------------
-- The global lookup is a projection of the closed document frontier only.
-- Closed sentence, paragraph, and adaptive-block interiors have no permission
-- to enter the global index.
------------------------------------------------------------------------

data LookupAuthority : Set where
  closedDocumentFrontier : LookupAuthority
  closedInteriorAuthority : LookupAuthority

data GlobalLookupPermission : LookupAuthority → Set where
  documentFrontierMayIndex :
    GlobalLookupPermission closedDocumentFrontier

closedInteriorCannotEnterGlobalLookup :
  GlobalLookupPermission closedInteriorAuthority → ⊥
closedInteriorCannotEnterGlobalLookup ()

record RootOnlyLookupBoundary : Set where
  constructor rootOnlyLookupBoundary
  field
    rootMayProject : GlobalLookupPermission closedDocumentFrontier
    childInteriorMayNotProject :
      GlobalLookupPermission closedInteriorAuthority → ⊥

open RootOnlyLookupBoundary public

canonicalRootOnlyLookupBoundary : RootOnlyLookupBoundary
canonicalRootOnlyLookupBoundary =
  rootOnlyLookupBoundary
    documentFrontierMayIndex
    closedInteriorCannotEnterGlobalLookup

------------------------------------------------------------------------
-- Reduction certificates expose the computational invariant: the admitted
-- parent frontier and its searchable projection cannot exceed the copied child
-- boundary inventory.  This is a boundary statement, not a claim that child
-- provenance has been deleted.
------------------------------------------------------------------------

record SparseFrontierCertificate : Set where
  constructor sparseFrontierCertificate
  field
    childBoundaryCount : Nat
    parentFrontierCount : Nat
    rootLookupCount : Nat
    parentFrontierIsReductive :
      parentFrontierCount ≤ᶜ childBoundaryCount
    rootLookupProjectsParentOnly :
      rootLookupCount ≤ᶜ parentFrontierCount

open SparseFrontierCertificate public

canonicalEmptySparseFrontierCertificate : SparseFrontierCertificate
canonicalEmptySparseFrontierCertificate =
  sparseFrontierCertificate
    zero
    zero
    zero
    (≤ᶜ-refl zero)
    (≤ᶜ-refl zero)

record SparseFibredFrontierBoundary : Set where
  constructor sparseFibredFrontierBoundary
  field
    closedFibreBoundaryWitness : ClosedFibreBoundary
    rootLookupBoundaryWitness : RootOnlyLookupBoundary
    noWitnessDisposition : RootDemandDisposition noWitness
    ambiguousDisposition : RootDemandDisposition severalWitnesses

open SparseFibredFrontierBoundary public

canonicalSparseFibredFrontierBoundary : SparseFibredFrontierBoundary
canonicalSparseFibredFrontierBoundary =
  sparseFibredFrontierBoundary
    canonicalClosedFibreBoundary
    canonicalRootOnlyLookupBoundary
    rootNoWitnessDefersToWorld
    rootSeveralWitnessesRemainOpen
