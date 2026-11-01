module DASHI.Core.FrozenProvenanceDynamicRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- FROZEN PROVENANCE-AWARE DYNAMIC REFINEMENT
--
-- Generic DASHI synthesis over three already-existing repo patterns:
--
--   * static observer collisions/refinement;
--   * provenance / inference-ancestry as an independently retained axis;
--   * train/select first, freeze, then evaluate downstream behaviour.
--
-- The motivating domain owners retain their own source attribution.  This file
-- does not transfer authorship, legal authority, empirical status, or mechanism
-- claims from those domains into the generic theorem.
------------------------------------------------------------------------

ProvenanceJoin :
  ∀ {State Surface Provenance : Set} →
  (State → Surface) →
  (State → Provenance) →
  State → Surface × Provenance
ProvenanceJoin = Observer.pairObserver

provenanceJoinRefinesSurface :
  ∀ {State Surface Provenance : Set}
    (surface : State → Surface)
    (provenance : State → Provenance) →
  Observer.Refines surface (ProvenanceJoin surface provenance)
provenanceJoinRefinesSurface = Observer.pairRefinesLeft

provenanceJoinStrictRefinement :
  ∀ {State Surface Provenance : Set}
    (surface : State → Surface)
    (provenance : State → Provenance)
    (left right : State) →
  surface left ≡ surface right →
  (provenance left ≡ provenance right → ⊥) →
  Observer.StrictRefinement surface (ProvenanceJoin surface provenance)
provenanceJoinStrictRefinement = Observer.strictPairRefinement

------------------------------------------------------------------------
-- Frozen-selection receipt.
--
-- Observer/refinement selection is fixed before downstream outcome comparison.
-- This is a methodological receipt only: freezing a bad observer does not make
-- it sufficient, dynamically congruent, true, or authoritative.
------------------------------------------------------------------------

record FrozenSelectionReceipt (Rule : Set) : Set where
  constructor frozen-selection-receipt
  field
    rule : Rule
    selectedBeforeOutcomeComparison : Bool
    selectionRuleStable : Bool
    heldOutOutcomeUsedForSelection : Bool

    selectedBeforeOutcomeComparisonPaid :
      selectedBeforeOutcomeComparison ≡ true
    selectionRuleStablePaid :
      selectionRuleStable ≡ true
    heldOutOutcomeNotUsedForSelection :
      heldOutOutcomeUsedForSelection ≡ false

open FrozenSelectionReceipt public

------------------------------------------------------------------------
-- Static repair + frozen methodology is still not future safety.
-- Dynamic trace congruence is a separate required witness.
------------------------------------------------------------------------

record FrozenStaticRefinementCandidate
    {State Surface Provenance Rule : Set}
    (surface : State → Surface)
    (provenance : State → Provenance) : Set₁ where
  constructor frozen-static-refinement-candidate
  field
    staticRefinement :
      Observer.StrictRefinement surface (ProvenanceJoin surface provenance)
    frozenSelection : FrozenSelectionReceipt Rule

open FrozenStaticRefinementCandidate public

record FrozenProvenanceDynamicPromotion
    {State Action Surface Provenance : Set}
    (system : Dependency.DependentActionSystem State Action)
    (surface : State → Surface)
    (provenance : State → Provenance)
    (Rule : Set) : Set₁ where
  constructor frozen-provenance-dynamic-promotion
  field
    staticCandidate :
      FrozenStaticRefinementCandidate {Rule = Rule} surface provenance
    dynamicSafety :
      Dynamic.DynamicConsumerSafety system (ProvenanceJoin surface provenance)

open FrozenProvenanceDynamicPromotion public

promotionRetainsStaticStrictRefinement :
  ∀ {State Action Surface Provenance Rule : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance} →
  (promotion :
    FrozenProvenanceDynamicPromotion system surface provenance Rule) →
  Observer.StrictRefinement surface (ProvenanceJoin surface provenance)
promotionRetainsStaticStrictRefinement promotion =
  staticRefinement (staticCandidate promotion)

promotionRetainsFrozenSelection :
  ∀ {State Action Surface Provenance Rule : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance} →
  (promotion :
    FrozenProvenanceDynamicPromotion system surface provenance Rule) →
  FrozenSelectionReceipt Rule
promotionRetainsFrozenSelection promotion =
  frozenSelection (staticCandidate promotion)

------------------------------------------------------------------------
-- Exact future-safety obstruction.
--
-- Even after a provenance-aware strict refinement has separated a known static
-- collision, and even after the refinement rule was frozen without held-out
-- leakage, a terminalisation defect on that joined observer forbids promotion.
------------------------------------------------------------------------

terminalisationDefectBlocksFrozenPromotion :
  ∀ {State Action Surface Provenance Rule : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance} →
  Dynamic.TerminalisationDefect system (ProvenanceJoin surface provenance) →
  FrozenProvenanceDynamicPromotion system surface provenance Rule →
  ⊥
terminalisationDefectBlocksFrozenPromotion defect promotion =
  Dynamic.terminalisationDefectContradictsSafety
    (dynamicSafety promotion)
    defect

staticFrozenCandidateStillNeedsDynamicSafety :
  ∀ {State Action Surface Provenance Rule : Set}
    {system : Dependency.DependentActionSystem State Action}
    {surface : State → Surface}
    {provenance : State → Provenance} →
  FrozenStaticRefinementCandidate {Rule = Rule} surface provenance →
  Dynamic.TerminalisationDefect system (ProvenanceJoin surface provenance) →
  FrozenProvenanceDynamicPromotion system surface provenance Rule →
  ⊥
staticFrozenCandidateStillNeedsDynamicSafety candidate defect promotion =
  terminalisationDefectBlocksFrozenPromotion defect promotion

------------------------------------------------------------------------
-- Promotion / attribution firewalls.
------------------------------------------------------------------------

data StaticSeparationCreatesDynamicSafetyPermission : Set where
data FrozenSelectionCreatesDynamicSafetyPermission : Set where
data ProvenanceAxisCreatesTruthPermission : Set where
data InRepoCrossPollinationTransfersAuthorshipPermission : Set where

staticSeparationDoesNotCreateDynamicSafety :
  StaticSeparationCreatesDynamicSafetyPermission → ⊥
staticSeparationDoesNotCreateDynamicSafety ()

frozenSelectionDoesNotCreateDynamicSafety :
  FrozenSelectionCreatesDynamicSafetyPermission → ⊥
frozenSelectionDoesNotCreateDynamicSafety ()

provenanceAxisDoesNotCreateTruth : ProvenanceAxisCreatesTruthPermission → ⊥
provenanceAxisDoesNotCreateTruth ()

crossPollinationDoesNotTransferAuthorship :
  InRepoCrossPollinationTransfersAuthorshipPermission → ⊥
crossPollinationDoesNotTransferAuthorship ()

record FrozenProvenanceDynamicBoundary : Set where
  constructor frozen-provenance-dynamic-boundary
  field
    provenanceJoinMayStrictlyRefineVisibleSurface : Bool
    staticSeparationImpliesDynamicSafety : Bool
    frozenRuleImpliesDynamicSafety : Bool
    heldOutSelectionLeakageAdmitted : Bool
    terminalisationDefectBlocksPromotion : Bool
    provenanceCreatesTruthOrAuthority : Bool
    crossDomainReuseTransfersSourceAuthorship : Bool

canonicalFrozenProvenanceDynamicBoundary : FrozenProvenanceDynamicBoundary
canonicalFrozenProvenanceDynamicBoundary =
  frozen-provenance-dynamic-boundary
    true false false false true false false
