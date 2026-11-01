module DASHI.Physics.Closure.YMResidualStrongRouteFastPath where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary.Negation using (¬_)

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMResidualSpatialSupportCore as Core
import DASHI.Physics.Closure.YMResolvedMembershipSemantics as Membership
import DASHI.Physics.Closure.YMResidualTermMembershipResolver as Resolver
import DASHI.Physics.Closure.YMStrongGateBCarriers as Strong
import DASHI.Physics.Closure.YMStrongGateBKP as KPKPI

------------------------------------------------------------------------
-- Fast-path compatibility surface for the requested sector-tagged stack.
--
-- The repository already contains the strong route proofs, but the names here
-- match your exact stack so downstream workers can reference a single target
-- surface.

ActionSector : Set
ActionSector = Core.ActionTermSector

ActionTerm : Set
ActionTerm = Core.ActionTerm

TermUsesLink : ActionTerm → Support.Link → Set
TermUsesLink = Core.TermUsesLink

TemporalOrMixedTerm : ActionTerm → Set
TemporalOrMixedTerm = Core.TemporalOrMixedTerm

TransferMatrixTerm : ActionTerm → Set
TransferMatrixTerm = Core.TransferMatrixTerm

ResidualActionTerm : ActionTerm → Set
ResidualActionTerm = Core.ResidualActionTerm

ResidualTermHasNoTemporalSupport :
  (t : ActionTerm) →
  (e : Support.Link) →
  ResidualActionTerm t →
  TermUsesLink t e →
  Support.TemporalLink e →
  ⊥
ResidualTermHasNoTemporalSupport =
  Core.ResidualTermHasNoTemporalSupportEvidence.residualTermHasNoTemporalSupport
    (Core.residualTermHasNoTemporalSupportFromAbsorption
      Core.temporalTermAbsorbedNotResidualFromSectors
      Core.canonicalTemporalLinkUseClassifiesTemporalTerm)

TransferResidualDisjoint :
  ∀ t →
  TransferMatrixTerm t →
  ResidualActionTerm t →
  ⊥
TransferResidualDisjoint = Core.transferMatrixTermNotResidualBySector

defaultStrongActionTermCarrier :
  Strong.StrongActionTermTransferResidualDisjointness
defaultStrongActionTermCarrier =
  Strong.strongActionTermTransferResidualDisjointnessFromSectors

-- A direct constructor-style output matching the requested split.
TemporalTermAbsorbedNotResidual :
  ∀ t →
  TemporalOrMixedTerm t →
  TransferMatrixTerm t × ¬ ResidualActionTerm t
TemporalTermAbsorbedNotResidual t temporal =
  let absorbed = Core.temporalTermAbsorbedNotResidual
                  Core.temporalTermAbsorbedNotResidualFromSectors t temporal
  in
    ( Core.AbsorbedNotResidual.absorbedAsTransferMatrixTerm absorbed
    , Core.AbsorbedNotResidual.notResidualAfterTransferAbsorption absorbed )

-- Strong residual membership in the exact fast-path shape:
-- a thin wrapper over the existing strong carrier used by the in-repo route.
StrongResidualPolymerMembership :
  Support.BalabanEffectiveAction →
  Support.Polymer → Set
StrongResidualPolymerMembership = Membership.StrongResidualPolymerMembership

strongResidualTerm :
  {S : Support.BalabanEffectiveAction} →
  {γ : Support.Polymer} →
  StrongResidualPolymerMembership S γ →
  ActionTerm
strongResidualTerm strong =
  Resolver.actionTermFromResidualEffectiveActionTerm
    (Membership.StrongResidualPolymerMembership.resolvedResidualTerm strong)

StrongResidualTermInAction :
  Support.BalabanEffectiveAction →
  Support.Polymer →
  {S : Support.BalabanEffectiveAction} →
  {γ : Support.Polymer} →
  StrongResidualPolymerMembership S γ →
  ActionTerm →
  Set
StrongResidualTermInAction S γ strong t =
  t ≡ strongResidualTerm strong

strongResidualIsResidual :
  {S : Support.BalabanEffectiveAction} →
  {γ : Support.Polymer} →
  (strong : StrongResidualPolymerMembership S γ) →
  ResidualActionTerm (strongResidualTerm strong)
strongResidualIsResidual strong =
  Resolver.residualActionTermFromResidualFlag
    (Membership.StrongResidualPolymerMembership.resolvedResidualTerm strong)
    (Membership.StrongResidualPolymerMembership.resolvedResidualFlag strong)

strongSupportLaw :
  {S : Support.BalabanEffectiveAction} →
  {γ : Support.Polymer} →
  (strong : StrongResidualPolymerMembership S γ) →
  Core.AllTermUsesLinks (strongResidualTerm strong) (Support.supportLinks γ)
strongSupportLaw strong =
  Membership.StrongResidualPolymerMembership.resolvedSupportLinksUseResidualTerm strong

ResidualEffectiveActionSpatialSupportEvidence :
  Strong.StrongActionTermTransferResidualDisjointness →
  (S : Support.BalabanEffectiveAction) →
  (γ : Support.Polymer) →
  StrongResidualPolymerMembership S γ →
  Support.SpatialSupport γ
ResidualEffectiveActionSpatialSupportEvidence carrier S γ strong =
  Core.allSpatialFromNoTemporalTermSupport
    (λ e use temporalLink →
      ResidualTermHasNoTemporalSupport
        (strongResidualTerm strong)
        e
        (strongResidualIsResidual strong)
        use
        temporalLink)
    (strongSupportLaw strong)

ResidualEffectiveActionSpatialSupportEvidenceFromCurrentCarrier :
  (S : Support.BalabanEffectiveAction) →
  (γ : Support.Polymer) →
  StrongResidualPolymerMembership S γ →
  Support.SpatialSupport γ
ResidualEffectiveActionSpatialSupportEvidenceFromCurrentCarrier S γ strong =
  ResidualEffectiveActionSpatialSupportEvidence
    defaultStrongActionTermCarrier
    S
    γ
    strong

EffectiveActionPolymersSpatialOnlyForA1 :
  Strong.StrongActionTermTransferResidualDisjointness →
  (S : Support.BalabanEffectiveAction) →
  (γ : Support.Polymer) →
  StrongResidualPolymerMembership S γ →
  Support.SpatialSupport γ
EffectiveActionPolymersSpatialOnlyForA1 carrier S γ strong =
  ResidualEffectiveActionSpatialSupportEvidence carrier S γ strong

EffectiveActionPolymersSpatialOnlyForA1FromCurrentCarrier :
  (S : Support.BalabanEffectiveAction) →
  (γ : Support.Polymer) →
  StrongResidualPolymerMembership S γ →
  Support.SpatialSupport γ
EffectiveActionPolymersSpatialOnlyForA1FromCurrentCarrier S γ strong =
  ResidualEffectiveActionSpatialSupportEvidenceFromCurrentCarrier S γ strong

PolymerDefinedOnBlockedLattice :
  Strong.StrongActionTermTransferResidualDisjointness →
  (S : Support.BalabanEffectiveAction) →
  (γ : Support.Polymer) →
  StrongResidualPolymerMembership S γ →
  Support.DefinedOnBlockedL2SpatialGraph γ
PolymerDefinedOnBlockedLattice carrier S γ strong =
  Support.blockedL2SpatialGraph
    (EffectiveActionPolymersSpatialOnlyForA1 carrier S γ strong)
    true

PolymerDefinedOnBlockedLatticeFromCurrentCarrier :
  (S : Support.BalabanEffectiveAction) →
  (γ : Support.Polymer) →
  StrongResidualPolymerMembership S γ →
  Support.DefinedOnBlockedL2SpatialGraph γ
PolymerDefinedOnBlockedLatticeFromCurrentCarrier S γ strong =
  PolymerDefinedOnBlockedLattice
    defaultStrongActionTermCarrier
    S
    γ
    strong

KPEntropyAtBlockedScaleL2 :
  KPKPI.StrongKPEntropyAtBlockedScaleL2Theorem
KPEntropyAtBlockedScaleL2 = KPKPI.strongKPEntropyAtBlockedScaleL2

-- Route-level fact: these are the exact theorem objects requested.
ResidualSupportRouteStackComplete :
  Strong.StrongActionTermTransferResidualDisjointness →
  (S : Support.BalabanEffectiveAction) →
  (γ : Support.Polymer) →
  StrongResidualPolymerMembership S γ →
  Support.DefinedOnBlockedL2SpatialGraph γ × KPKPI.StrongKPEntropyAtBlockedScaleL2Theorem
ResidualSupportRouteStackComplete carrier S γ strong =
  (PolymerDefinedOnBlockedLattice carrier S γ strong , KPEntropyAtBlockedScaleL2)

ResidualSupportRouteStackCompleteFromCurrentCarrier :
  (S : Support.BalabanEffectiveAction) →
  (γ : Support.Polymer) →
  StrongResidualPolymerMembership S γ →
  Support.DefinedOnBlockedL2SpatialGraph γ × KPKPI.StrongKPEntropyAtBlockedScaleL2Theorem
ResidualSupportRouteStackCompleteFromCurrentCarrier S γ strong =
  ResidualSupportRouteStackComplete
    defaultStrongActionTermCarrier
    S
    γ
    strong
