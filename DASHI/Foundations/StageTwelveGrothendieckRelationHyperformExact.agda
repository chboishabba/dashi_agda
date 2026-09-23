module DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Construct a genuine finite Grothendieck-topology surface on the existing
-- twelve-position StageAtlasZeroToEleven carrier, and construct the typed
-- 12 x 12 = 144 ordered-relation carrier suggested by the complete
-- twelve-axis relational cycle.
--
-- This module intentionally keeps three facts separate:
--
--   * StageAtlasZeroToEleven has exactly twelve typed coordinates;
--   * RelationalAppraisalPointedPhaseExact has a complete 12-axis cycle;
--   * modular forms have an independently sourced weight-12 lane.
--
-- The first two are welded here through an explicit coordinate carrier.
-- No theorem here identifies this finite site with the analytic modular curve.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _^_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import Base369 as Base
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Foundations.StageValuationBundleAtlas as Bundle
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel

------------------------------------------------------------------------
-- 1. Twelve typed axes and the 144 ordered relation carrier.
------------------------------------------------------------------------

StageAxis12 : Set
StageAxis12 = Atlas.StageAtlasZeroToEleven

stageAxisCount : Nat
stageAxisCount = Atlas.carrierSize

stageAxisCountIs12 : stageAxisCount ≡ 12
stageAxisCountIs12 = Atlas.carrierSizeIsTwelve

completeRelationalCycleAlsoHas12Axes :
  Rel.completeCycleAxisCount ≡ stageAxisCount
completeRelationalCycleAlsoHas12Axes = refl

StageRelation144 : Set
StageRelation144 = StageAxis12 × StageAxis12

stageRelationCellCount : Nat
stageRelationCellCount = stageAxisCount * stageAxisCount

stageRelationCellCountIs144 :
  stageRelationCellCount ≡ 144
stageRelationCellCountIs144 = refl

StageRelationField : Set
StageRelationField = StageRelation144 → Base.TriTruth

relationAt :
  StageRelationField →
  StageAxis12 →
  StageAxis12 →
  Base.TriTruth
relationAt field left right = field (left , right)

transposeRelation :
  StageRelationField →
  StageRelationField
transposeRelation field (left , right) = field (right , left)

transposeRelationInvolutive :
  (field : StageRelationField) →
  (cell : StageRelation144) →
  transposeRelation (transposeRelation field) cell ≡ field cell
transposeRelationInvolutive field (left , right) = refl

diagonalObservation :
  StageRelationField →
  StageAxis12 →
  Base.TriTruth
diagonalObservation field axis = field (axis , axis)

------------------------------------------------------------------------
-- 2. The 144 cells are a relation carrier, not 144 ternary states.
--
-- A ternary-valued relation field over the 144 ordered cells has 3^144
-- profiles.  This keeps "144 relation slots" separate from "3^144 states".
------------------------------------------------------------------------

ternaryRelationProfileCount : Nat
ternaryRelationProfileCount = 3 ^ stageRelationCellCount

relationCellsAre144NotStateCount :
  stageRelationCellCount ≡ 144
relationCellsAre144NotStateCount = stageRelationCellCountIs144

data RelationCellCountCreatesModularWeightIdentity : Set where
data RelationCarrierCreatesAnalyticJSite : Set where

relation144DoesNotCreateWeightTwelveIdentity :
  RelationCellCountCreatesModularWeightIdentity → ⊥
relation144DoesNotCreateWeightTwelveIdentity ()

relation144DoesNotCreateAnalyticJSite :
  RelationCarrierCreatesAnalyticJSite → ⊥
relation144DoesNotCreateAnalyticJSite ()

------------------------------------------------------------------------
-- 3. Small category interface with laws.
------------------------------------------------------------------------

record SmallCategory : Set₁ where
  field
    Obj : Set
    Hom : Obj → Obj → Set
    id : (U : Obj) → Hom U U
    _∘_ : {U V W : Obj} → Hom V W → Hom U V → Hom U W
    idLeft :
      {U V : Obj} →
      (f : Hom U V) →
      _∘_ (id V) f ≡ f
    idRight :
      {U V : Obj} →
      (f : Hom U V) →
      _∘_ f (id U) ≡ f
    assoc :
      {U V W X : Obj} →
      (h : Hom W X) →
      (g : Hom V W) →
      (f : Hom U V) →
      _∘_ (_∘_ h g) f ≡ _∘_ h (_∘_ g f)

open SmallCategory public

------------------------------------------------------------------------
-- 4. Sieves and pullback.
------------------------------------------------------------------------

record Sieve (C : SmallCategory) (U : Obj C) : Set₁ where
  field
    contains :
      {V : Obj C} →
      Hom C V U →
      Set
    closed :
      {V W : Obj C} →
      (f : Hom C V U) →
      contains f →
      (g : Hom C W V) →
      contains (_∘_ C f g)

open Sieve public

maximalSieve :
  (C : SmallCategory) →
  (U : Obj C) →
  Sieve C U
maximalSieve C U = record
  { contains = λ f → ⊤
  ; closed = λ f witness g → tt
  }

pullbackSieve :
  (C : SmallCategory) →
  {U V : Obj C} →
  Hom C V U →
  Sieve C U →
  Sieve C V
pullbackSieve C arrow sieve = record
  { contains = λ g → Sieve.contains sieve (_∘_ C arrow g)
  ; closed = λ g witness h →
      subst
        (λ k → Sieve.contains sieve k)
        (assoc C arrow g h)
        (Sieve.closed sieve (_∘_ C arrow g) witness h)
  }
  where
    subst :
      ∀ {A : Set} (P : A → Set) {x y : A} →
      x ≡ y → P x → P y
    subst P refl px = px

------------------------------------------------------------------------
-- 5. Genuine Grothendieck topology axioms.
------------------------------------------------------------------------

record GrothendieckTopology (C : SmallCategory) : Set₁ where
  field
    Cover :
      {U : Obj C} →
      Sieve C U →
      Set

    maximal :
      (U : Obj C) →
      Cover (maximalSieve C U)

    stable :
      {U V : Obj C} →
      (arrow : Hom C V U) →
      (sieve : Sieve C U) →
      Cover sieve →
      Cover (pullbackSieve C arrow sieve)

    transitive :
      {U : Obj C} →
      (sieve : Sieve C U) →
      Cover sieve →
      (target : Sieve C U) →
      (({V : Obj C} →
        (f : Hom C V U) →
        Sieve.contains sieve f →
        Cover (pullbackSieve C f target))) →
      Cover target

open GrothendieckTopology public

------------------------------------------------------------------------
-- 6. Concrete discrete twelve-axis category.
------------------------------------------------------------------------

trans :
  ∀ {A : Set} {x y z : A} →
  x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

stageDiscreteCategory : SmallCategory
stageDiscreteCategory = record
  { Obj = StageAxis12
  ; Hom = _≡_
  ; id = λ U → refl
  ; _∘_ = λ g f → trans f g
  ; idLeft = λ f → refl
  ; idRight = λ f → refl
  ; assoc = λ h g f → refl
  }

------------------------------------------------------------------------
-- 7. Maximal-only coverage is an actual Grothendieck topology.
--
-- Covering means every arrow into U is already in the sieve.  On the
-- discrete stage category this is the canonical conservative topology.
------------------------------------------------------------------------

IsMaximal :
  {U : StageAxis12} →
  Sieve stageDiscreteCategory U →
  Set
IsMaximal {U} sieve =
  {V : StageAxis12} →
  (f : Hom stageDiscreteCategory V U) →
  Sieve.contains sieve f

maximalOnlyStageTopology :
  GrothendieckTopology stageDiscreteCategory
maximalOnlyStageTopology = record
  { Cover = IsMaximal
  ; maximal = λ U f → tt
  ; stable = λ arrow sieve cover g →
      cover (_∘_ stageDiscreteCategory arrow g)
  ; transitive = λ sieve sieveCover target localCover f →
      let coverAtIdentity =
            localCover f (sieveCover f) (id stageDiscreteCategory _)
      in
      subst
        (λ k → Sieve.contains target k)
        (idRight stageDiscreteCategory f)
        coverAtIdentity
  }
  where
    subst :
      ∀ {A : Set} (P : A → Set) {x y : A} →
      x ≡ y → P x → P y
    subst P refl px = px

------------------------------------------------------------------------
-- 8. Reuse the pre-existing BundleSheaf gluing interface.
------------------------------------------------------------------------

StageBundleSheaf :
  (LocalSection GlobalSection : Set) →
  Set₁
StageBundleSheaf LocalSection GlobalSection =
  Bundle.BundleSheaf StageAxis12 LocalSection GlobalSection

record StageTwelveSiteSheafReceipt : Set₁ where
  field
    topology :
      GrothendieckTopology stageDiscreteCategory
    relationCarrier : Set
    relationCarrierIsTypedPair :
      relationCarrier ≡ StageRelation144
    relationCellCount : Nat
    relationCellCountPaid :
      relationCellCount ≡ 144
    completeCycleAxisCountPaid :
      Rel.completeCycleAxisCount ≡ 12
    bundleSheafInterfaceReused : Bool
    grothendieckAxiomsConstructed : Bool
    analyticModularSiteIdentified : Bool
    modularWeightTwelveIdentifiedWithAxisTwelve : Bool

canonicalStageTwelveSiteSheafReceipt :
  StageTwelveSiteSheafReceipt
canonicalStageTwelveSiteSheafReceipt = record
  { topology = maximalOnlyStageTopology
  ; relationCarrier = StageRelation144
  ; relationCarrierIsTypedPair = refl
  ; relationCellCount = stageRelationCellCount
  ; relationCellCountPaid = stageRelationCellCountIs144
  ; completeCycleAxisCountPaid = Rel.completeCycleAxisCountIsTwelve
  ; bundleSheafInterfaceReused = true
  ; grothendieckAxiomsConstructed = true
  ; analyticModularSiteIdentified = false
  ; modularWeightTwelveIdentifiedWithAxisTwelve = false
  }
