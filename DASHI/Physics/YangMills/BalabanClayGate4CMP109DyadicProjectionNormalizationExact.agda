module DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicProjectionNormalizationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using
    ( CyclicIndex; zeroᵢ; sucᵢ
    ; Product; pair; first; second; Fourfold
    ; FiniteEnumeration; elements; complete; productFinite
    ; _∈_; here; there; map; mapMembership
    )

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ProjectedEndpointBlocksExact as Endpoint

------------------------------------------------------------------------
-- Literal one-step dyadic projection in four dimensions.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- For a coarse cyclic side of cardinality n, the one-step fine side has
-- cardinality 2n.  Each fine coordinate is split into a coarse coordinate and
-- one parity bit.  Coordinatewise application therefore gives an explicit
-- bijection
--
--   fine site  <->  coarse site × Bool^4,
--
-- proving that every four-dimensional dyadic block contains exactly 2^4=16
-- fine sites.  This is the concrete site projection and block-volume datum
-- consumed by the CMP109 endpoint and normalization layers.
------------------------------------------------------------------------

twice : Nat → Nat
twice zero = zero
twice (suc value) = suc (suc (twice value))

dyadicFineN : Nat → Nat
dyadicFineN coarseN = suc (twice coarseN)

dyadicFineSideExact : ∀ coarseN →
  suc (dyadicFineN coarseN) ≡ twice (suc coarseN)
dyadicFineSideExact coarseN = refl

halveCyclic : ∀ {n} → CyclicIndex (twice n) → CyclicIndex n
halveCyclic {zero} ()
halveCyclic {suc n} zeroᵢ = zeroᵢ
halveCyclic {suc n} (sucᵢ zeroᵢ) = zeroᵢ
halveCyclic {suc n} (sucᵢ (sucᵢ index)) =
  sucᵢ (halveCyclic index)

parityCyclic : ∀ {n} → CyclicIndex (twice n) → Bool
parityCyclic {zero} ()
parityCyclic {suc n} zeroᵢ = false
parityCyclic {suc n} (sucᵢ zeroᵢ) = true
parityCyclic {suc n} (sucᵢ (sucᵢ index)) = parityCyclic index

liftCyclic : ∀ {n} → CyclicIndex n → Bool → CyclicIndex (twice n)
liftCyclic {zero} ()
liftCyclic {suc n} zeroᵢ false = zeroᵢ
liftCyclic {suc n} zeroᵢ true = sucᵢ zeroᵢ
liftCyclic {suc n} (sucᵢ index) bit =
  sucᵢ (sucᵢ (liftCyclic index bit))

halveLiftCyclic : ∀ {n} (index : CyclicIndex n) bit →
  halveCyclic (liftCyclic index bit) ≡ index
halveLiftCyclic {zero} ()
halveLiftCyclic {suc n} zeroᵢ false = refl
halveLiftCyclic {suc n} zeroᵢ true = refl
halveLiftCyclic {suc n} (sucᵢ index) bit =
  cong sucᵢ (halveLiftCyclic index bit)

liftHalveParityCyclic :
  ∀ {n} (index : CyclicIndex (twice n)) →
  liftCyclic (halveCyclic index) (parityCyclic index) ≡ index
liftHalveParityCyclic {zero} ()
liftHalveParityCyclic {suc n} zeroᵢ = refl
liftHalveParityCyclic {suc n} (sucᵢ zeroᵢ) = refl
liftHalveParityCyclic {suc n} (sucᵢ (sucᵢ index)) =
  cong (λ value → sucᵢ (sucᵢ value))
    (liftHalveParityCyclic index)

Bit4 : Set
Bit4 = Fourfold Bool

projectDyadicSite :
  ∀ {coarseN} →
  Periodic.PeriodicBlock (dyadicFineN coarseN) →
  Periodic.PeriodicBlock coarseN
projectDyadicSite
    (pair (pair coordinate0 coordinate1) (pair coordinate2 coordinate3)) =
  pair
    (pair (halveCyclic coordinate0) (halveCyclic coordinate1))
    (pair (halveCyclic coordinate2) (halveCyclic coordinate3))

liftDyadicSite :
  ∀ {coarseN} →
  Periodic.PeriodicBlock coarseN → Bit4 →
  Periodic.PeriodicBlock (dyadicFineN coarseN)
liftDyadicSite
    (pair (pair coordinate0 coordinate1) (pair coordinate2 coordinate3))
    (pair (pair bit0 bit1) (pair bit2 bit3)) =
  pair
    (pair
      (liftCyclic coordinate0 bit0)
      (liftCyclic coordinate1 bit1))
    (pair
      (liftCyclic coordinate2 bit2)
      (liftCyclic coordinate3 bit3))

parityDyadicSite :
  ∀ {coarseN} →
  Periodic.PeriodicBlock (dyadicFineN coarseN) → Bit4
parityDyadicSite
    (pair (pair coordinate0 coordinate1) (pair coordinate2 coordinate3)) =
  pair
    (pair (parityCyclic coordinate0) (parityCyclic coordinate1))
    (pair (parityCyclic coordinate2) (parityCyclic coordinate3))

projectLiftDyadicSite :
  ∀ {coarseN}
    (coarse : Periodic.PeriodicBlock coarseN)
    (bits : Bit4) →
  projectDyadicSite (liftDyadicSite coarse bits) ≡ coarse
projectLiftDyadicSite
    (pair (pair coordinate0 coordinate1) (pair coordinate2 coordinate3))
    (pair (pair bit0 bit1) (pair bit2 bit3))
  with halveLiftCyclic coordinate0 bit0
     | halveLiftCyclic coordinate1 bit1
     | halveLiftCyclic coordinate2 bit2
     | halveLiftCyclic coordinate3 bit3
... | refl | refl | refl | refl = refl

liftProjectParityDyadicSite :
  ∀ {coarseN}
    (fine : Periodic.PeriodicBlock (dyadicFineN coarseN)) →
  liftDyadicSite (projectDyadicSite fine) (parityDyadicSite fine) ≡ fine
liftProjectParityDyadicSite
    (pair (pair coordinate0 coordinate1) (pair coordinate2 coordinate3))
  with liftHalveParityCyclic coordinate0
     | liftHalveParityCyclic coordinate1
     | liftHalveParityCyclic coordinate2
     | liftHalveParityCyclic coordinate3
... | refl | refl | refl | refl = refl

dyadicCMP109SiteProjection :
  ∀ coarseN →
  Endpoint.PeriodicCMP109SiteProjection (dyadicFineN coarseN) coarseN
dyadicCMP109SiteProjection coarseN = record
  { coarseOfFineSite =
      projectDyadicSite
  }

------------------------------------------------------------------------
-- Exact sixteen-element fibre.
------------------------------------------------------------------------

boolFinite : FiniteEnumeration Bool
boolFinite = record
  { elements = false ∷ true ∷ []
  ; complete = λ where
      false → here
      true → there here
  }

bit4Finite : FiniteEnumeration Bit4
bit4Finite =
  productFinite
    (productFinite boolFinite boolFinite)
    (productFinite boolFinite boolFinite)

allBit4 : List Bit4
allBit4 = elements bit4Finite

allBit4Complete : ∀ bits → bits ∈ allBit4
allBit4Complete = complete bit4Finite

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

one : Nat
one = suc zero

two : Nat
two = twice one

fourCount : Nat
fourCount = twice two

eight : Nat
eight = twice fourCount

sixteen : Nat
sixteen = twice eight

sixtyFour : Nat
sixtyFour = twice (twice sixteen)

oneTwentyEight : Nat
oneTwentyEight = twice sixtyFour

allBit4Length : listLength allBit4 ≡ sixteen
allBit4Length = refl

dyadicFibre :
  ∀ {coarseN} →
  Periodic.PeriodicBlock coarseN →
  List (Periodic.PeriodicBlock (dyadicFineN coarseN))
dyadicFibre coarse = map (liftDyadicSite coarse) allBit4

dyadicFibreLength :
  ∀ {coarseN} (coarse : Periodic.PeriodicBlock coarseN) →
  listLength (dyadicFibre coarse) ≡ sixteen
dyadicFibreLength coarse = refl

data All {A : Set} (Predicate : A → Set) : List A → Set where
  allNil : All Predicate []
  allCons : ∀ {value values} →
    Predicate value → All Predicate values →
    All Predicate (value ∷ values)

allMap :
  ∀ {A B : Set} {Predicate : B → Set}
    (function : A → B) (values : List A) →
  (∀ value → Predicate (function value)) →
  All Predicate (map function values)
allMap function [] property = allNil
allMap function (value ∷ values) property =
  allCons (property value) (allMap function values property)

allMember :
  ∀ {A : Set} {Predicate : A → Set}
    {value : A} {values : List A} →
  All Predicate values → value ∈ values → Predicate value
allMember allNil ()
allMember (allCons property rest) here = property
allMember (allCons property rest) (there membership) =
  allMember rest membership

dyadicFibreSound :
  ∀ {coarseN}
    (coarse : Periodic.PeriodicBlock coarseN)
    (fine : Periodic.PeriodicBlock (dyadicFineN coarseN)) →
  fine ∈ dyadicFibre coarse →
  projectDyadicSite fine ≡ coarse
dyadicFibreSound coarse fine membership =
  allMember
    (allMap
      (liftDyadicSite coarse)
      allBit4
      (projectLiftDyadicSite coarse))
    membership

dyadicFibreComplete :
  ∀ {coarseN}
    (coarse : Periodic.PeriodicBlock coarseN)
    (fine : Periodic.PeriodicBlock (dyadicFineN coarseN)) →
  projectDyadicSite fine ≡ coarse →
  fine ∈ dyadicFibre coarse
dyadicFibreComplete coarse fine projectionExact =
  subst
    (λ selectedCoarse → fine ∈ dyadicFibre selectedCoarse)
    projectionExact
    (subst
      (λ selectedFine →
        selectedFine ∈ dyadicFibre (projectDyadicSite fine))
      (liftProjectParityDyadicSite fine)
      (mapMembership
        (liftDyadicSite (projectDyadicSite fine))
        (allBit4Complete (parityDyadicSite fine))))

------------------------------------------------------------------------
-- Exact one-step four-dimensional block normalization.
------------------------------------------------------------------------

record PositiveFraction : Set where
  constructor positiveFraction
  field
    numerator denominator : Nat

open PositiveFraction public

record CMP109Dyadic4Normalization : Set where
  constructor cmp109Dyadic4Normalization
  field
    blockSide : Nat
    spacetimeDimension : Nat
    blockVolume : Nat
    blockWeight : PositiveFraction

    blockSideExact : blockSide ≡ two
    spacetimeDimensionExact : spacetimeDimension ≡ fourCount
    blockVolumeExact : blockVolume ≡ sixteen
    blockWeightExact :
      blockWeight ≡ positiveFraction one sixteen

open CMP109Dyadic4Normalization public

canonicalCMP109Dyadic4Normalization : CMP109Dyadic4Normalization
canonicalCMP109Dyadic4Normalization = record
  { blockSide = two
  ; spacetimeDimension = fourCount
  ; blockVolume = sixteen
  ; blockWeight = positiveFraction one sixteen
  ; blockSideExact = refl
  ; spacetimeDimensionExact = refl
  ; blockVolumeExact = refl
  ; blockWeightExact = refl
  }

dyadicCyclicSplitRoundTripLevel : ProofLevel
dyadicCyclicSplitRoundTripLevel = machineChecked

dyadicFourTorusProjectionLevel : ProofLevel
dyadicFourTorusProjectionLevel = machineChecked

dyadicFourTorusFibreBijectionLevel : ProofLevel
dyadicFourTorusFibreBijectionLevel = machineChecked

dyadicFourTorusFibreCardinalityLevel : ProofLevel
dyadicFourTorusFibreCardinalityLevel = computed

cmp109DyadicFourDimensionalNormalizationLevel : ProofLevel
cmp109DyadicFourDimensionalNormalizationLevel = computed
