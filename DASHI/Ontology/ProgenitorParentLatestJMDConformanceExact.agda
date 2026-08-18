module DASHI.Ontology.ProgenitorParentLatestJMDConformanceExact where

open import DASHI.Core.Prelude using (Bool; false; true; _≡_; ⊥)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.FibrePreservingDynamicsExact as Dynamics
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.PolicyRelativeProjectionSafety as Policy
import DASHI.Ontology.LeanWikidataFullSourceManifest as Manifest
import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge as Lean
import DASHI.Ontology.ProgenitorParentProjectionFibre as ParentFibre
import DASHI.Ontology.ProgenitorParentPNFPullbackLattice as ParentPNF
import DASHI.Ontology.ProgenitorParentObserverDynamicsBridge as ParentDynamics
import DASHI.Ontology.ProgenitorParentAuthorityRoutingNonfactorabilityExact as Routing
import DASHI.Ontology.ProgenitorParentObserverFutureSafetyExact as Future
import DASHI.Ontology.ProgenitorParentResidualDynamicsExact as Residual

------------------------------------------------------------------------
-- Cross-kernel conformance with the later supplied JMD / Aristotle source.
--
-- A SourceLocalConformance value contains BOTH:
--   * the exact source-pinned Lean theorem contract, and
--   * the corresponding Agda proof term already established on this branch.
--
-- This is not an FFI proof import and does not claim proof-term identity across
-- kernels.  It records that two independently checked developments expose the
-- same mathematical contract.
------------------------------------------------------------------------

latestParentingFibresSource : Manifest.LeanSourceModule
latestParentingFibresSource =
  Manifest.leanSourceModule
    "RequestProject.Wikidata.ParentingFibres"
    "68ae2c3739594353abf828c48bc34b2fefbb7219b8ac8bc00d291b2379070ab3"
    Manifest.classHierarchy
    (Manifest.epistemicAnchor ∷ Manifest.derivationFibreAnchor ∷ [])

latestParentingAuthoritySource : Manifest.LeanSourceModule
latestParentingAuthoritySource =
  Manifest.leanSourceModule
    "RequestProject.Wikidata.ParentingAuthority"
    "e276a92b709633a5dac74fcb6e423be59a9addf061451301afcb450eb95fd516"
    Manifest.classHierarchy
    (Manifest.epistemicAnchor ∷ Manifest.authorityBoundaryAnchor ∷ [])

record SourceLocalConformance (LocalClaim : Set) : Set where
  constructor sourceLocalConformance
  field
    leanContract : Lean.LeanTheoremContract
    localProof : LocalClaim

open SourceLocalConformance public

slotNotSeparatingContract : Lean.LeanTheoremContract
slotNotSeparatingContract =
  Lean.leanTheoremContract latestParentingFibresSource
    "Wikidata.Parenting.slotObserver_not_separating"
    "the Wikidata parent slot observer is not separating"
    Lean.negativeConstraintTheorem

legalFinalizationHiddenContract : Lean.LeanTheoremContract
legalFinalizationHiddenContract =
  Lean.leanTheoremContract latestParentingFibresSource
    "Wikidata.Parenting.finalizeLegal_hidden_transition"
    "legal finalisation is a nontrivial fine-state transition invisible to the parent slot"
    Lean.structuralTheorem

legalResidualMotionContract : Lean.LeanTheoremContract
legalResidualMotionContract =
  Lean.leanTheoremContract latestParentingFibresSource
    "Wikidata.Parenting.legal_finalization_moves_residual"
    "exact reopening forces hidden legal motion to move the residual"
    Lean.structuralTheorem

routeNonfactorabilityContract : Lean.LeanTheoremContract
routeNonfactorabilityContract =
  Lean.leanTheoremContract latestParentingFibresSource
    "Wikidata.Parenting.route_not_factorsThrough"
    "legal-parent authority routing does not factor through the coarse parent slot"
    Lean.negativeConstraintTheorem

coarsePolicyUnsafeContract : Lean.LeanTheoremContract
coarsePolicyUnsafeContract =
  Lean.leanTheoremContract latestParentingAuthoritySource
    "Wikidata.Parenting.coarse_policy_unsafe"
    "a coarse parent-surface authority policy is unsafe on the donor/adoptive collision"
    Lean.negativeConstraintTheorem

slotNotSeparatingConformance :
  SourceLocalConformance
    (Observer.Separating ParentDynamics.parentSlotObserver → ⊥)
slotNotSeparatingConformance =
  sourceLocalConformance
    slotNotSeparatingContract
    ParentDynamics.p8810SlotNotSeparating

legalFinalizationHiddenConformance :
  SourceLocalConformance
    (Dynamics.HiddenTransition
      ParentPNF.parentFibreRestrictionCore
      ParentDynamics.finalizeLegalParenthood
      ParentDynamics.preFinalizationCarrier)
legalFinalizationHiddenConformance =
  sourceLocalConformance
    legalFinalizationHiddenContract
    ParentDynamics.legalFinalizationIsHiddenP8810Transition

legalResidualMotionConformance :
  SourceLocalConformance
    (Residual.parentResidual
      (ParentDynamics.finalizeLegalParenthood ParentDynamics.preFinalizationCarrier)
     ≡ Residual.parentResidual ParentDynamics.preFinalizationCarrier → ⊥)
legalResidualMotionConformance =
  sourceLocalConformance
    legalResidualMotionContract
    Residual.legalFinalizationMustMoveResidual

routeNonfactorabilityConformance :
  SourceLocalConformance
    (NonFactor.FactorsThrough
      ParentFibre.projectParentSlot
      Routing.routeParentAuthority → ⊥)
routeNonfactorabilityConformance =
  sourceLocalConformance
    routeNonfactorabilityContract
    Routing.parentSlotInsufficiencyBlocksAuthorityRouting

coarsePolicyUnsafeConformance :
  SourceLocalConformance
    (Policy.PolicyRelativeSafety
      Future.parentDecisionSystem
      (Future.parentDecisionProject Future.authorityDecisionConsumer)
      Future.parentAuthorityPolicy → ⊥)
coarsePolicyUnsafeConformance =
  sourceLocalConformance
    coarsePolicyUnsafeContract
    Future.coarseParentAuthorityPolicyIsUnsafe

------------------------------------------------------------------------
-- Boundary: theorem-surface agreement does not promote either bridge to global
-- truth authority or identify the two proof objects.
------------------------------------------------------------------------

record ParentCrossKernelBoundary : Set where
  constructor parentCrossKernelBoundary
  field
    sameMathematicalContractsObserved : Bool
    proofTermsIdentifiedAcrossKernels : Bool
    importedContractsPromoteWorldTruth : Bool

canonicalParentCrossKernelBoundary : ParentCrossKernelBoundary
canonicalParentCrossKernelBoundary =
  parentCrossKernelBoundary true false false
