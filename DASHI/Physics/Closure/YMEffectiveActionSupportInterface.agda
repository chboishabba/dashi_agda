module DASHI.Physics.Closure.YMEffectiveActionSupportInterface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Typed YM effective-action support interface.
--
-- This module supplies the first theorem-level carrier layer needed by the
-- Gate-B/KP lane.  It intentionally separates interface definition from the
-- still-open analytic theorem that residual Balaban effective-action polymers
-- are spatial-only after temporal transfer-matrix absorption.

Scale : Set
Scale = String

Identifier : Set
Identifier = String

data LinkKind : Set where
  temporal : LinkKind
  spatial : LinkKind

record Link : Set where
  constructor link
  field
    linkId : Identifier
    kind : LinkKind

open Link public

TemporalLink : Link → Set
TemporalLink e = kind e ≡ temporal

SpatialLink : Link → Set
SpatialLink e = kind e ≡ spatial

data AllSpatialLinks : List Link → Set where
  allSpatialNil :
    AllSpatialLinks []
  allSpatialCons :
    {e : Link} →
    {es : List Link} →
    SpatialLink e →
    AllSpatialLinks es →
    AllSpatialLinks (e ∷ es)

record Polymer : Set where
  constructor polymer
  field
    polymerId : Identifier
    supportLinks : List Link

open Polymer public

PolymerSupport : Polymer → Set
PolymerSupport γ = AllSpatialLinks (supportLinks γ)

SpatialSupport : Polymer → Set
SpatialSupport = PolymerSupport

record ResidualEffectiveActionTerm : Set where
  constructor residualTerm
  field
    termId : Identifier
    termPolymer : Polymer
    residualAfterTransferAbsorption : Bool
    activityDependsOnlyOnOwnPolymerLinks : Bool

open ResidualEffectiveActionTerm public

record BalabanEffectiveAction : Set where
  constructor balabanEffectiveAction
  field
    rgScale : Scale
    residualTerms : List ResidualEffectiveActionTerm

open BalabanEffectiveAction public

record PolymerIn (S : BalabanEffectiveAction) (γ : Polymer) : Set where
  constructor polymerIn
  field
    membershipWitness : Identifier

record ActivityDependsOnlyOnLinksInsidePolymer
  (term : ResidualEffectiveActionTerm) : Set where
  constructor activityLocality
  field
    activityLocalityWitness : activityDependsOnlyOnOwnPolymerLinks term ≡ true

record TemporalMeasureFactorizationLambdaOneReconciled : Set where
  constructor temporalLambdaOneReconciled
  field
    sprint71LambdaOneOpenAccountedFor : Bool
    sprint73LeakageLambdaOneAccountedFor : Bool
    sprint78LambdaOneInputAccountedFor : Bool

record DefinedOnBlockedL2SpatialGraph (γ : Polymer) : Set where
  constructor blockedL2SpatialGraph
  field
    spatialSupportWitness : SpatialSupport γ
    blockingFactorL2 : Bool

record EffectiveActionPolymersSpatialOnlyForA1Theorem : Set₁ where
  field
    provesSpatialSupport :
      (S : BalabanEffectiveAction) →
      (γ : Polymer) →
      PolymerIn S γ →
      SpatialSupport γ

record PolymerDefinedOnBlockedLatticeTheorem : Set₁ where
  field
    provesBlockedL2SpatialGraph :
      (γ : Polymer) →
      SpatialSupport γ →
      DefinedOnBlockedL2SpatialGraph γ

record GateBSupportInterfaceDefined : Set₁ where
  field
    linkKindDefined :
      LinkKind ≡ LinkKind
    linkCarrierDefined :
      Link ≡ Link
    temporalLinkPredicateDefined :
      TemporalLink ≡ TemporalLink
    spatialLinkPredicateDefined :
      SpatialLink ≡ SpatialLink
    polymerCarrierDefined :
      Polymer ≡ Polymer
    balabanEffectiveActionCarrierDefined :
      BalabanEffectiveAction ≡ BalabanEffectiveAction
    residualEffectiveActionTermCarrierDefined :
      ResidualEffectiveActionTerm ≡ ResidualEffectiveActionTerm
    polymerInRelationDefined :
      PolymerIn ≡ PolymerIn
    spatialSupportPredicateDefined :
      SpatialSupport ≡ SpatialSupport
    activityLocalityPredicateDefined :
      ActivityDependsOnlyOnLinksInsidePolymer
        ≡ ActivityDependsOnlyOnLinksInsidePolymer
    temporalMeasureFactorizationReconciliationDefined :
      TemporalMeasureFactorizationLambdaOneReconciled
        ≡ TemporalMeasureFactorizationLambdaOneReconciled
    blockedL2SpatialGraphPredicateDefined :
      DefinedOnBlockedL2SpatialGraph ≡ DefinedOnBlockedL2SpatialGraph

gateBSupportInterfaceDefined : GateBSupportInterfaceDefined
gateBSupportInterfaceDefined =
  record
    { linkKindDefined = refl
    ; linkCarrierDefined = refl
    ; temporalLinkPredicateDefined = refl
    ; spatialLinkPredicateDefined = refl
    ; polymerCarrierDefined = refl
    ; balabanEffectiveActionCarrierDefined = refl
    ; residualEffectiveActionTermCarrierDefined = refl
    ; polymerInRelationDefined = refl
    ; spatialSupportPredicateDefined = refl
    ; activityLocalityPredicateDefined = refl
    ; temporalMeasureFactorizationReconciliationDefined = refl
    ; blockedL2SpatialGraphPredicateDefined = refl
    }

data GateBPromotion : Set where

gateBPromotionImpossibleFromInterfaceOnly : GateBPromotion → ⊥
gateBPromotionImpossibleFromInterfaceOnly ()

effectiveActionSpatialOnlyNotProvedByInterfaceAlone : Bool
effectiveActionSpatialOnlyNotProvedByInterfaceAlone = false

polymerDefinedOnBlockedLatticeNotProvedByInterfaceAlone : Bool
polymerDefinedOnBlockedLatticeNotProvedByInterfaceAlone = false

kpEntropyAtBlockedScaleL2NotProvedByInterfaceAlone : Bool
kpEntropyAtBlockedScaleL2NotProvedByInterfaceAlone = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

record GateBSupportInterfaceBoundary : Set₁ where
  field
    interfaceDefined :
      GateBSupportInterfaceDefined
    noEffectiveActionSpatialOnlyPromotion :
      effectiveActionSpatialOnlyNotProvedByInterfaceAlone ≡ false
    noBlockedLatticePromotion :
      polymerDefinedOnBlockedLatticeNotProvedByInterfaceAlone ≡ false
    noKPEntropyPromotion :
      kpEntropyAtBlockedScaleL2NotProvedByInterfaceAlone ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      GateBPromotion → ⊥

gateBSupportInterfaceBoundary : GateBSupportInterfaceBoundary
gateBSupportInterfaceBoundary =
  record
    { interfaceDefined = gateBSupportInterfaceDefined
    ; noEffectiveActionSpatialOnlyPromotion = refl
    ; noBlockedLatticePromotion = refl
    ; noKPEntropyPromotion = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = gateBPromotionImpossibleFromInterfaceOnly
    }
