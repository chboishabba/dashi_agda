module DASHI.Moonshine.MoonshineGroupBase where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- Exact group presentations and their theorem-facing equivalences.

record MoonshineGroupDatum
  (MonsterClass FuchsianGroup : Set)
  (actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData :
    FuchsianGroup → Set) : Set where
  field
    group : FuchsianGroup
    groupActsOnUpperHalfPlane : actsOnUpperHalfPlane group
    groupDiscrete : discrete group
    groupFiniteCovolume : finiteCovolume group
    groupGenusZero : genusZero group
    groupCuspData : cuspData group
    monsterClass : MonsterClass
    classMoonshineGroup : FuchsianGroup
    groupIdentification : classMoonshineGroup ≡ group

record MoonshineGroupEquivalence
  {MonsterClass FuchsianGroup : Set}
  {actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData :
    FuchsianGroup → Set}
  (GroupCarrier : FuchsianGroup → Set)
  (GroupIso : FuchsianGroup → FuchsianGroup → Set)
  (UpperHalfPlane : Set)
  (upperHalfPlaneAction : (Γ : FuchsianGroup) → GroupCarrier Γ →
    UpperHalfPlane → UpperHalfPlane)
  (Cusp : FuchsianGroup → Set)
  (FundamentalDomainCompatible LaplacianIntertwining ModularFunctionTransport :
    FuchsianGroup → FuchsianGroup → Set)
  (Γ Δ : MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane
    discrete finiteCovolume genusZero cuspData) : Setω where
  field
    groupIso : GroupIso (MoonshineGroupDatum.group Γ) (MoonshineGroupDatum.group Δ)
    groupMap : GroupCarrier (MoonshineGroupDatum.group Γ) →
      GroupCarrier (MoonshineGroupDatum.group Δ)
    actionIntertwining : ∀ γ z →
      upperHalfPlaneAction (MoonshineGroupDatum.group Δ) (groupMap γ) z ≡
      upperHalfPlaneAction (MoonshineGroupDatum.group Γ) γ z
    cuspForward : Cusp (MoonshineGroupDatum.group Γ) → Cusp (MoonshineGroupDatum.group Δ)
    cuspBackward : Cusp (MoonshineGroupDatum.group Δ) → Cusp (MoonshineGroupDatum.group Γ)
    cuspForwardBackward : ∀ cusp → cuspBackward (cuspForward cusp) ≡ cusp
    cuspBackwardForward : ∀ cusp → cuspForward (cuspBackward cusp) ≡ cusp
    fundamentalDomainCompatibility : FundamentalDomainCompatible
      (MoonshineGroupDatum.group Γ) (MoonshineGroupDatum.group Δ)
    laplacianIntertwining : LaplacianIntertwining
      (MoonshineGroupDatum.group Γ) (MoonshineGroupDatum.group Δ)
    modularFunctionTransport : ModularFunctionTransport
      (MoonshineGroupDatum.group Γ) (MoonshineGroupDatum.group Δ)
