module DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)
open import Data.Rational using (_*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact
  using (PeriodicBlock)

import DASHI.Physics.YangMills.BalabanClayGate4LiteralWilsonLargeFieldPredicateExact as Wilson
import DASHI.Physics.YangMills.BalabanClayP2BadComponentGeometryExact as Geometry

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban, "The Variational Problem and Background Fields in
-- Renormalization Group Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
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
-- Relationship: the positive periodic plaquette enumeration below is a
-- DASHI-specific finite carrier. The papers own the averaging, background and
-- large-field architecture; they do not replace the exact finite proofs here.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Duplicate-free finite positive plaquettes based at one periodic block.
------------------------------------------------------------------------

data NoDuplicates {A : Set} : List A → Set where
  unique[] : NoDuplicates []
  unique∷ : ∀ {value values} →
    Not (value ∈ values) → NoDuplicates values →
    NoDuplicates (value ∷ values)

mapMembershipInverse :
  ∀ {A B : Set} {f : A → B} →
  (∀ {left right} → f left ≡ f right → left ≡ right) →
  ∀ {value values} → f value ∈ map f values → value ∈ values
mapMembershipInverse injective here = here
mapMembershipInverse injective (there member) =
  there (mapMembershipInverse injective member)

mapNoDuplicates :
  ∀ {A B : Set} {f : A → B} →
  (∀ {left right} → f left ≡ f right → left ≡ right) →
  ∀ {values} → NoDuplicates values → NoDuplicates (map f values)
mapNoDuplicates injective unique[] = unique[]
mapNoDuplicates injective (unique∷ notMember rest) =
  unique∷
    (λ member → notMember (mapMembershipInverse injective member))
    (mapNoDuplicates injective rest)

zeroNotInSuccessorMap :
  ∀ {n} (values : List (CyclicIndex n)) →
  Not (zeroᵢ ∈ map sucᵢ values)
zeroNotInSuccessorMap [] ()
zeroNotInSuccessorMap (value ∷ values) (there member) =
  zeroNotInSuccessorMap values member

allCyclicIndicesNoDuplicates : ∀ n → NoDuplicates (allCyclicIndices n)
allCyclicIndicesNoDuplicates zero = unique[]
allCyclicIndicesNoDuplicates (suc n) =
  unique∷
    (zeroNotInSuccessorMap (allCyclicIndices n))
    (mapNoDuplicates sucInjective (allCyclicIndicesNoDuplicates n))

six : Nat
six = suc (suc (suc (suc (suc (suc zero)))))

PositivePlane4 : Set
PositivePlane4 = CyclicIndex six

PeriodicPlaquette : Nat → Set
PeriodicPlaquette n = Product (PeriodicBlock n) PositivePlane4

ownedPeriodicPlaquettes : ∀ {n} → PeriodicBlock n → List (PeriodicPlaquette n)
ownedPeriodicPlaquettes block =
  map (λ plane → pair block plane) (allCyclicIndices six)

ownedPeriodicPlaquettesComplete :
  ∀ {n} (block : PeriodicBlock n) plane →
  pair block plane ∈ ownedPeriodicPlaquettes block
ownedPeriodicPlaquettesComplete block plane =
  mapMembership (λ selectedPlane → pair block selectedPlane)
    (allCyclicIndicesComplete plane)

ownedPeriodicPlaquettesNoDuplicates :
  ∀ {n} (block : PeriodicBlock n) →
  NoDuplicates (ownedPeriodicPlaquettes block)
ownedPeriodicPlaquettesNoDuplicates block =
  mapNoDuplicates productSecondInjective
    (allCyclicIndicesNoDuplicates six)

------------------------------------------------------------------------
-- Explicit six positive coordinate planes.
------------------------------------------------------------------------

axis0 axis1 axis2 axis3 : Axis4
axis0 = zeroᵢ
axis1 = sucᵢ zeroᵢ
axis2 = sucᵢ (sucᵢ zeroᵢ)
axis3 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))

planeAxes : PositivePlane4 → Product Axis4 Axis4
planeAxes zeroᵢ = pair axis0 axis1
planeAxes (sucᵢ zeroᵢ) = pair axis0 axis2
planeAxes (sucᵢ (sucᵢ zeroᵢ)) = pair axis0 axis3
planeAxes (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = pair axis1 axis2
planeAxes (sucᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))) = pair axis1 axis3
planeAxes (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))))) = pair axis2 axis3

------------------------------------------------------------------------
-- Adapter to the literal Wilson large-field data.
------------------------------------------------------------------------

record LiteralPeriodicPlaquetteOwnership
    (n : Nat) (Scale Configuration Gauge : Set) : Set₁ where
  field
    largeField : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge (PeriodicBlock n) (PeriodicPlaquette n)
    ownedPlaquettesArePeriodic : ∀ block →
      Wilson.ownedPlaquettes largeField block ≡ ownedPeriodicPlaquettes block

open LiteralPeriodicPlaquetteOwnership public

toWilsonMembership :
  ∀ {A : Set} {value : A} {values : List A} →
  value ∈ values → Wilson._∈_ value values
toWilsonMembership here = Wilson.here
toWilsonMembership (there member) = Wilson.there (toWilsonMembership member)

ownedPlaquettesComplete :
  ∀ {n Scale Configuration Gauge}
    (dataSet : LiteralPeriodicPlaquetteOwnership
      n Scale Configuration Gauge)
    block plane →
  Wilson._∈_ (pair block plane)
    (Wilson.ownedPlaquettes (largeField dataSet) block)
ownedPlaquettesComplete dataSet block plane
  rewrite ownedPlaquettesArePeriodic dataSet block =
  toWilsonMembership (ownedPeriodicPlaquettesComplete block plane)

ownedPlaquettesNoDuplicate :
  ∀ {n Scale Configuration Gauge}
    (dataSet : LiteralPeriodicPlaquetteOwnership
      n Scale Configuration Gauge)
    block →
  NoDuplicates (Wilson.ownedPlaquettes (largeField dataSet) block)
ownedPlaquettesNoDuplicate dataSet block
  rewrite ownedPlaquettesArePeriodic dataSet block =
  ownedPeriodicPlaquettesNoDuplicates block

------------------------------------------------------------------------
-- Exact derived threshold and witness bridges.
------------------------------------------------------------------------

scaleAdjustedThresholdExact :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    scale →
  Wilson.scaleAdjustedThreshold dataSet scale
  ≡ Wilson.etaSquared dataSet scale
      * (Wilson.coupling dataSet scale * Wilson.p0 dataSet scale)
scaleAdjustedThresholdExact dataSet scale =
  trans
    (Wilson.physicalThresholdBridge dataSet scale)
    (cong (Wilson.etaSquared dataSet scale *_)
      (Wilson.thresholdDefinition dataSet scale))

largeFieldBlockHasCanonicalWitness :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    scale configuration block →
  Wilson.LargeFieldBlock dataSet scale configuration block →
  Σ Plaquette (λ plaquette →
    Wilson._∈_ plaquette (Wilson.ownedPlaquettes dataSet block)
    × Wilson.LargePlaquette dataSet scale configuration plaquette)
largeFieldBlockHasCanonicalWitness dataSet scale configuration block
  (Wilson.largeWitness plaquette member large) =
  plaquette , (member , large)

ReachableThroughLiteralLargeBlocks :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    (scale : Scale) (configuration : Configuration) →
  Block → Block → Set
ReachableThroughLiteralLargeBlocks dataSet scale configuration =
  Geometry.BadPath (Wilson.literalWilsonBadBlockGeometry dataSet scale) configuration

infix 2 _↔_
record _↔_ (Left Right : Set) : Set where
  field
    forward : Left → Right
    backward : Right → Left

literalBadComponentAgreesWithLargeFieldReachability :
  ∀ {Scale Configuration Gauge Block Plaquette}
    (dataSet : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    (scale : Scale) (configuration : Configuration)
    (component : Geometry.BadComponent
      (Wilson.literalWilsonBadBlockGeometry dataSet scale) configuration)
    block →
  Geometry.Contains component block
  ↔ ReachableThroughLiteralLargeBlocks dataSet scale configuration
      (Geometry.seed component) block
literalBadComponentAgreesWithLargeFieldReachability
  dataSet scale configuration component block = record
  { forward = λ path → path
  ; backward = λ path → path
  }

literalPeriodicPlaquetteEnumerationLevel : ProofLevel
literalPeriodicPlaquetteEnumerationLevel = machineChecked

literalPeriodicPlaquetteNoDuplicateLevel : ProofLevel
literalPeriodicPlaquetteNoDuplicateLevel = machineChecked

literalScaleAdjustedThresholdExactLevel : ProofLevel
literalScaleAdjustedThresholdExactLevel = machineChecked

literalCanonicalBadPlaquetteWitnessLevel : ProofLevel
literalCanonicalBadPlaquetteWitnessLevel = machineChecked

literalBadComponentAgreementLevel : ProofLevel
literalBadComponentAgreementLevel = machineChecked

literalPeriodicHolonomyAndGaugeInstanceInputsLevel : ProofLevel
literalPeriodicHolonomyAndGaugeInstanceInputsLevel = conditional
