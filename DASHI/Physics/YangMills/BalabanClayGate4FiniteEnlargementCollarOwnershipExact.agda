module DASHI.Physics.YangMills.BalabanClayGate4FiniteEnlargementCollarOwnershipExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Sigma using (Σ) renaming (_,_ to _,Σ_)
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (Not)

import DASHI.Physics.YangMills.BalabanClayP2BadComponentGeometryExact as Geometry

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban, "Large Field Renormalization. I. The Basic Step of the
-- R Operation", Communications in Mathematical Physics 122 (1989), 175--202.
-- DOI: 10.1007/BF01257412.
--
-- Tadeusz Bałaban, "Large Field Renormalization. II. Localization,
-- Exponentiation, and Bounds for the R Operation", Communications in
-- Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- Relationship: Bałaban's determining sets, enlarged large-field regions and
-- boundary terms motivate these proof-relevant finite carriers. This module
-- proves only the combinatorial bookkeeping; metric scale choices and analytic
-- collar bounds remain separate inputs.
------------------------------------------------------------------------

data ReachWithin {Block : Set}
    (Adjacent : Block → Block → Set) : Nat → Block → Block → Set where
  stay : ∀ {radius block} → ReachWithin Adjacent radius block block
  step : ∀ {radius start next finish} →
    Adjacent start next →
    ReachWithin Adjacent radius next finish →
    ReachWithin Adjacent (suc radius) start finish

reachMonotone :
  ∀ {Block} {Adjacent : Block → Block → Set}
    {radius start finish} →
  ReachWithin Adjacent radius start finish →
  ReachWithin Adjacent (suc radius) start finish
reachMonotone stay = stay
reachMonotone (step adjacent rest) = step adjacent (reachMonotone rest)

record FiniteLargeFieldRegion (Block : Set) : Set₁ where
  field
    Contains : Block → Set

open FiniteLargeFieldRegion public

record EnlargementData (Block : Set) : Set₁ where
  field
    Adjacent : Block → Block → Set
    adjacentSymmetric : ∀ {left right} →
      Adjacent left right → Adjacent right left

open EnlargementData public

Enlarged :
  ∀ {Block} → EnlargementData Block →
  FiniteLargeFieldRegion Block → Nat → Block → Set
Enlarged dataSet region radius block =
  Σ _ (λ seed →
    Contains region seed × ReachWithin (Adjacent dataSet) radius seed block)

regionIncludedInEnlargement :
  ∀ {Block} (dataSet : EnlargementData Block)
    (region : FiniteLargeFieldRegion Block) radius block →
  Contains region block → Enlarged dataSet region radius block
regionIncludedInEnlargement dataSet region radius block member =
  block ,Σ (member , stay)

EnlargementMonotone :
  ∀ {Block} (dataSet : EnlargementData Block)
    (region : FiniteLargeFieldRegion Block) radius block → Set
EnlargementMonotone dataSet region radius block =
  Enlarged dataSet region radius block →
  Enlarged dataSet region (suc radius) block

enlargementMonotone :
  ∀ {Block} (dataSet : EnlargementData Block)
    (region : FiniteLargeFieldRegion Block) radius block →
  EnlargementMonotone dataSet region radius block
enlargementMonotone dataSet region radius block
  (seed ,Σ (member , reach)) =
  seed ,Σ (member , reachMonotone reach)

Collar :
  ∀ {Block} → EnlargementData Block → FiniteLargeFieldRegion Block →
  Nat → Nat → Block → Set
Collar dataSet region inner outer block =
  Enlarged dataSet region outer block ×
  Not (Enlarged dataSet region inner block)

------------------------------------------------------------------------
-- Support ownership and boundary classification.
------------------------------------------------------------------------

data Every {A : Set} (P : A → Set) : List A → Set where
  every[] : Every P []
  every∷  : ∀ {value values} → P value → Every P values → Every P (value ∷ values)

data Any {A : Set} (P : A → Set) : List A → Set where
  anyHere  : ∀ {value values} → P value → Any P (value ∷ values)
  anyThere : ∀ {value values} → Any P values → Any P (value ∷ values)

record LocalizedSupport (Term Block : Set) : Set₁ where
  field
    support : Term → List Block

open LocalizedSupport public

OwnedByEnlargement :
  ∀ {Term Block} → LocalizedSupport Term Block →
  EnlargementData Block → FiniteLargeFieldRegion Block →
  Nat → Term → Set
OwnedByEnlargement supportData enlargement region radius term =
  Every (Enlarged enlargement region radius) (support supportData term)

IntersectsEnlargement :
  ∀ {Term Block} → LocalizedSupport Term Block →
  EnlargementData Block → FiniteLargeFieldRegion Block →
  Nat → Term → Set
IntersectsEnlargement supportData enlargement region radius term =
  Any (Enlarged enlargement region radius) (support supportData term)

record BoundaryOwnership
    {Term Block : Set}
    (supportData : LocalizedSupport Term Block)
    (enlargement : EnlargementData Block)
    (region : FiniteLargeFieldRegion Block)
    (inner outer : Nat)
    (term : Term) : Set where
  field
    intersectsOuter :
      IntersectsEnlargement supportData enlargement region outer term
    notOwnedByInner :
      Not (OwnedByEnlargement supportData enlargement region inner term)

open BoundaryOwnership public

record DeterminingSetReinjection
    (Term EffectiveDensity : Set) : Set₁ where
  field
    emptyDensity : EffectiveDensity
    insertBoundary : Term → EffectiveDensity → EffectiveDensity
    insertAllBoundary : List Term → EffectiveDensity → EffectiveDensity
    insertAllDefinition : List Term → EffectiveDensity → Set
    supportOwnerPreserved : Term → EffectiveDensity → Set
    determiningSetUpdated : Term → EffectiveDensity → Set

open DeterminingSetReinjection public

------------------------------------------------------------------------
-- Adapter from the repository's existing proof-relevant bad component.
------------------------------------------------------------------------

badComponentRegion :
  ∀ {Configuration Gauge Block}
    {geometry : Geometry.BadBlockGeometry Configuration Gauge Block}
    {configuration : Configuration} →
  Geometry.BadComponent geometry configuration →
  FiniteLargeFieldRegion Block
badComponentRegion component = record
  { Contains = Geometry.Contains component }

finiteReachAndEnlargementDefinitionLevel : ProofLevel
finiteReachAndEnlargementDefinitionLevel = machineChecked

largeFieldRegionIncludedInEnlargementLevel : ProofLevel
largeFieldRegionIncludedInEnlargementLevel = machineChecked

enlargementMonotonicityLevel : ProofLevel
enlargementMonotonicityLevel = machineChecked

finiteCollarDefinitionLevel : ProofLevel
finiteCollarDefinitionLevel = machineChecked

supportOwnershipAndBoundaryClassificationLevel : ProofLevel
supportOwnershipAndBoundaryClassificationLevel = machineChecked

literalMetricRadiusAndCollarFinitenessInputsLevel : ProofLevel
literalMetricRadiusAndCollarFinitenessInputsLevel = conditional

analyticBoundaryReinjectionInputsLevel : ProofLevel
analyticBoundaryReinjectionInputsLevel = conditional
