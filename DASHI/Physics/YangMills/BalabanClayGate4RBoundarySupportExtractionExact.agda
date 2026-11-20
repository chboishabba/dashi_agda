module DASHI.Physics.YangMills.BalabanClayGate4RBoundarySupportExtractionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ) renaming (_,_ to _,Σ_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (_∈_; here; there; Not)

import DASHI.Physics.YangMills.BalabanClayGate4FiniteEnlargementCollarOwnershipExact as Collar
import DASHI.Physics.YangMills.BalabanClayP2BadComponentGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanClayGate4LiteralWilsonLargeFieldPredicateExact as Wilson
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicReachCollarEnumerationExact as Reach
import DASHI.Physics.YangMills.BalabanClayGate4FiniteROperationAndDecayAssemblyExact as R

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Target locator pending direct verification: equation (1.69), p. 377.
-- The module below proves the exact finite source/support transport; the
-- quantitative boundary-activity bound remains a separate analytic theorem.
------------------------------------------------------------------------

mapMembershipSource :
  ∀ {A B : Set} (function : A → B) {target values} →
  target ∈ R.map function values →
  Σ A (λ source → source ∈ values × function source ≡ target)
mapMembershipSource function {values = source ∷ rest} here =
  source ,Σ (here , refl)
mapMembershipSource function {values = head ∷ rest} (there membership)
  with mapMembershipSource function membership
... | source ,Σ (sourceMember , equality) =
  source ,Σ (there sourceMember , equality)

boundaryListDefinition :
  ∀ {Scale Polymer BoundaryCondition Region Term LocalizedTerm BoundaryTerm
      RExpression}
    (dataSet : R.FiniteROperationData Scale Polymer BoundaryCondition Region Term
      LocalizedTerm BoundaryTerm RExpression)
    scale polymer boundary →
  R.B dataSet scale polymer boundary
  ≡ R.map (R.extractBoundary dataSet scale polymer)
      (R.map (R.localize dataSet scale polymer)
        (R.boundarySourceTerms dataSet scale polymer boundary))
boundaryListDefinition dataSet scale polymer boundary = refl

record BoundarySourceCollarData
    {Scale Polymer BoundaryCondition Region Term LocalizedTerm BoundaryTerm
      RExpression Block : Set}
    (dataSet : R.FiniteROperationData Scale Polymer BoundaryCondition Region Term
      LocalizedTerm BoundaryTerm RExpression)
    (supportData : Collar.LocalizedSupport BoundaryTerm Block)
    (enlargement : Collar.EnlargementData Block)
    (largeRegion : Collar.FiniteLargeFieldRegion Block)
    (inner outer : Nat) : Set₁ where
  field
    boundarySourceGeneratesCollar :
      ∀ scale polymer boundary source →
      source ∈ R.boundarySourceTerms dataSet scale polymer boundary →
      Reach.GeneratedBoundaryTerm supportData enlargement largeRegion inner outer
        (R.extractBoundary dataSet scale polymer
          (R.localize dataSet scale polymer source))

open BoundarySourceCollarData public

generatedBoundaryTermHasCollarSupport :
  ∀ {Scale Polymer BoundaryCondition Region Term LocalizedTerm BoundaryTerm
      RExpression Block}
    {dataSet : R.FiniteROperationData Scale Polymer BoundaryCondition Region Term
      LocalizedTerm BoundaryTerm RExpression}
    {supportData : Collar.LocalizedSupport BoundaryTerm Block}
    {enlargement : Collar.EnlargementData Block}
    {largeRegion : Collar.FiniteLargeFieldRegion Block}
    {inner outer}
    (collarData : BoundarySourceCollarData dataSet supportData enlargement
      largeRegion inner outer)
    scale polymer boundary boundaryTerm →
  boundaryTerm ∈ R.B dataSet scale polymer boundary →
  Reach.GeneratedBoundaryTerm supportData enlargement largeRegion inner outer
    boundaryTerm
generatedBoundaryTermHasCollarSupport
  {dataSet = dataSet} {supportData = supportData}
  {enlargement = enlargement} {largeRegion = largeRegion}
  {inner = inner} {outer = outer}
  collarData scale polymer boundary boundaryTerm membership
  with mapMembershipSource (R.extractBoundary dataSet scale polymer)
    (subst
      (λ boundaryTerms → boundaryTerm ∈ boundaryTerms)
      (boundaryListDefinition dataSet scale polymer boundary)
      membership)
... | localized ,Σ (localizedMember , outerEquality)
  with mapMembershipSource (R.localize dataSet scale polymer) localizedMember
... | source ,Σ (sourceMember , innerEquality) =
  subst
    (Reach.GeneratedBoundaryTerm supportData enlargement largeRegion inner outer)
    (trans
      (cong (R.extractBoundary dataSet scale polymer) innerEquality)
      outerEquality)
    (boundarySourceGeneratesCollar collarData
      scale polymer boundary source sourceMember)

everyWeaken :
  ∀ {A : Set} {P Q : A → Set} {values : List A} →
  (∀ value → P value → Q value) →
  Collar.Every P values → Collar.Every Q values
everyWeaken inclusion Collar.every[] = Collar.every[]
everyWeaken inclusion (Collar.every∷ proof rest) =
  Collar.every∷ (inclusion _ proof) (everyWeaken inclusion rest)

record CollarDeterminingSetBridge
    {Block : Set}
    (enlargement : Collar.EnlargementData Block)
    (largeRegion : Collar.FiniteLargeFieldRegion Block)
    (inner outer : Nat) : Set₁ where
  field
    DeterminingSet : Block → Set
    collarIncluded : ∀ block →
      Collar.Collar enlargement largeRegion inner outer block →
      DeterminingSet block

open CollarDeterminingSetBridge public

generatedBoundarySupportOwnedByDeterminingSet :
  ∀ {Term Block}
    {supportData : Collar.LocalizedSupport Term Block}
    {enlargement : Collar.EnlargementData Block}
    {largeRegion : Collar.FiniteLargeFieldRegion Block}
    {inner outer term}
    (bridge : CollarDeterminingSetBridge enlargement largeRegion inner outer) →
  Reach.GeneratedBoundaryTerm supportData enlargement largeRegion inner outer term →
  Collar.Every (DeterminingSet bridge) (Collar.support supportData term)
generatedBoundarySupportOwnedByDeterminingSet bridge generated =
  everyWeaken (collarIncluded bridge)
    (Reach.boundaryTermSupportInCollar generated)

rBoundarySourceExtractionLevel : ProofLevel
rBoundarySourceExtractionLevel = machineChecked

rBoundaryCollarSupportTransportLevel : ProofLevel
rBoundaryCollarSupportTransportLevel = machineChecked

rBoundaryDeterminingSetOwnershipLevel : ProofLevel
rBoundaryDeterminingSetOwnershipLevel = machineChecked

rBoundarySourceCollarClassificationInputsLevel : ProofLevel
rBoundarySourceCollarClassificationInputsLevel = conditional

nextDeterminingSetContainsCollarInputsLevel : ProofLevel
nextDeterminingSetContainsCollarInputsLevel = conditional

------------------------------------------------------------------------
-- Literal Wilson complement of ALL enlarged bad components.  A collar
-- of one component alone is not a certificate of global smallness.
------------------------------------------------------------------------

OutsideAllWilsonEnlargements :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData Scale Configuration Gauge Block Plaquette)
    (scale : Scale) (configuration : Configuration)
    (enlargement : Collar.EnlargementData Block) (radius : Nat)
    (block : Block) → Set
OutsideAllWilsonEnlargements dataSet scale configuration enlargement radius block =
  (polymer : Geometry.BadComponent (Wilson.literalWilsonBadBlockGeometry dataSet scale)
    configuration) →
  Not (Collar.Enlarged enlargement
    (Collar.badComponentRegion polymer) radius block)

outsideAllEnlargementsImpliesOutsideComponents :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData Scale Configuration Gauge Block Plaquette)
    scale configuration enlargement radius block →
  OutsideAllWilsonEnlargements dataSet scale configuration enlargement radius block →
  Wilson.OutsideWilsonComponents dataSet scale configuration block
outsideAllEnlargementsImpliesOutsideComponents
    dataSet scale configuration enlargement radius block outside polymer member =
  outside polymer (Collar.regionIncludedInEnlargement enlargement
    (Collar.badComponentRegion polymer) radius block member)

outsideAllEnlargementsOwnedSmall :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData Scale Configuration Gauge Block Plaquette)
    scale configuration enlargement radius block →
  OutsideAllWilsonEnlargements dataSet scale configuration enlargement radius block →
  ∀ plaquette → Wilson._∈_ plaquette (Wilson.ownedPlaquettes dataSet block) →
  Wilson.SmallPlaquette dataSet scale configuration plaquette
outsideAllEnlargementsOwnedSmall dataSet scale configuration enlargement radius block outside =
  Wilson.outsideWilsonComponentsOwnedSmall dataSet scale configuration block
    (outsideAllEnlargementsImpliesOutsideComponents
      dataSet scale configuration enlargement radius block outside)

-- Consume the original support list, not a reconstructed set of blocks.
-- The source must provide global exclusion over that exact list.
boundarySupportOwnedPlaquettesSmall :
  ∀ {Scale Configuration Gauge Block Plaquette Term}
    (dataSet : Wilson.LiteralWilsonLargeFieldData Scale Configuration Gauge Block Plaquette)
    scale configuration enlargement radius
    (supportData : Collar.LocalizedSupport Term Block) term →
  Collar.Every
    (OutsideAllWilsonEnlargements dataSet scale configuration enlargement radius)
    (Collar.support supportData term) →
  Collar.Every
    (λ block → ∀ plaquette →
      Wilson._∈_ plaquette (Wilson.ownedPlaquettes dataSet block) →
      Wilson.SmallPlaquette dataSet scale configuration plaquette)
    (Collar.support supportData term)
boundarySupportOwnedPlaquettesSmall dataSet scale configuration enlargement radius
    supportData term =
  everyWeaken
    (outsideAllEnlargementsOwnedSmall dataSet scale configuration enlargement radius)

-- A source-owned regular domain may be smaller than the global complement.
-- Only the forward inclusion is consumed; no equality is imposed.
regularDomainSupportOwnedSmall :
  ∀ {Scale Configuration Gauge Block Plaquette Term}
    (dataSet : Wilson.LiteralWilsonLargeFieldData Scale Configuration Gauge Block Plaquette)
    scale configuration enlargement radius
    (supportData : Collar.LocalizedSupport Term Block) term
    (Regular : Block → Set) →
  (∀ block → Regular block →
    OutsideAllWilsonEnlargements dataSet scale configuration enlargement radius block) →
  Collar.Every Regular (Collar.support supportData term) →
  Collar.Every
    (λ block → ∀ plaquette →
      Wilson._∈_ plaquette (Wilson.ownedPlaquettes dataSet block) →
      Wilson.SmallPlaquette dataSet scale configuration plaquette)
    (Collar.support supportData term)
regularDomainSupportOwnedSmall dataSet scale configuration enlargement radius
    supportData term Regular inclusion members =
  boundarySupportOwnedPlaquettesSmall dataSet scale configuration enlargement radius
    supportData term (everyWeaken inclusion members)
