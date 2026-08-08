module DASHI.Physics.YangMills.BalabanWilsonD4SubsetCharacterExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368.
-- DOI: 10.1007/BF00531932.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Construct the dihedral action on the four plaquette slots and its induced
-- action on subset characteristic functions.  The action law is definitional
-- for composed permutations.  The eight named D4 symmetries are evaluated on
-- the literal fifteen nonempty Wilson subsets, giving fixed-point character
-- values 15,3,1,7,3 and five concrete orbit types.  Exact character inner
-- products yield
--
--   R[B4 - {empty}] = 5 A1 + 3 B1 + B2 + 3 E,
--
-- with A2 absent for the untwisted real subset-permutation representation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (filter; length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube

record SlotPermutation4 : Set where
  constructor slotPermutation
  field
    forward backward : Cube.BondSlot4 → Cube.BondSlot4
    forwardAfterBackward : ∀ slot → forward (backward slot) ≡ slot
    backwardAfterForward : ∀ slot → backward (forward slot) ≡ slot

open SlotPermutation4 public

identityPermutation4 : SlotPermutation4
identityPermutation4 = slotPermutation
  (λ slot → slot) (λ slot → slot)
  (λ slot → refl) (λ slot → refl)

composePermutation4 : SlotPermutation4 → SlotPermutation4 → SlotPermutation4
composePermutation4 left right = slotPermutation
  (λ slot → forward left (forward right slot))
  (λ slot → backward right (backward left slot))
  (λ slot →
    let first = forwardAfterBackward right (backward left slot)
    in
    let second = forwardAfterBackward left slot
    in
    case first of λ where refl → second)
  (λ slot →
    let first = backwardAfterForward left (forward right slot)
    in
    let second = backwardAfterForward right slot
    in
    case first of λ where refl → second)

subsetCharacteristic : Cube.Subset4 → Cube.BondSlot4 → Bool
subsetCharacteristic subset slot = Cube.contains slot subset

actOnCharacteristic :
  SlotPermutation4 →
  (Cube.BondSlot4 → Bool) →
  Cube.BondSlot4 → Bool
actOnCharacteristic symmetry subset slot =
  subset (backward symmetry slot)

subsetCharacteristicActionLaw :
  ∀ left right subset slot →
  actOnCharacteristic (composePermutation4 left right)
    (subsetCharacteristic subset) slot
  ≡ actOnCharacteristic left
      (actOnCharacteristic right (subsetCharacteristic subset)) slot
subsetCharacteristicActionLaw left right subset slot = refl

subsetCharacteristicIdentityLaw : ∀ subset slot →
  actOnCharacteristic identityPermutation4
    (subsetCharacteristic subset) slot
  ≡ subsetCharacteristic subset slot
subsetCharacteristicIdentityLaw subset slot = refl

quarterTurn : SlotPermutation4
quarterTurn = slotPermutation forwardQuarter backwardQuarter
  forwardBackward backwardForward
  where
  forwardQuarter : Cube.BondSlot4 → Cube.BondSlot4
  forwardQuarter Cube.slot0 = Cube.slot1
  forwardQuarter Cube.slot1 = Cube.slot2
  forwardQuarter Cube.slot2 = Cube.slot3
  forwardQuarter Cube.slot3 = Cube.slot0

  backwardQuarter : Cube.BondSlot4 → Cube.BondSlot4
  backwardQuarter Cube.slot0 = Cube.slot3
  backwardQuarter Cube.slot1 = Cube.slot0
  backwardQuarter Cube.slot2 = Cube.slot1
  backwardQuarter Cube.slot3 = Cube.slot2

  forwardBackward : ∀ slot →
    forwardQuarter (backwardQuarter slot) ≡ slot
  forwardBackward Cube.slot0 = refl
  forwardBackward Cube.slot1 = refl
  forwardBackward Cube.slot2 = refl
  forwardBackward Cube.slot3 = refl

  backwardForward : ∀ slot →
    backwardQuarter (forwardQuarter slot) ≡ slot
  backwardForward Cube.slot0 = refl
  backwardForward Cube.slot1 = refl
  backwardForward Cube.slot2 = refl
  backwardForward Cube.slot3 = refl

halfTurn : SlotPermutation4
halfTurn = composePermutation4 quarterTurn quarterTurn

threeQuarterTurn : SlotPermutation4
threeQuarterTurn = composePermutation4 quarterTurn halfTurn

axisReflection : SlotPermutation4
axisReflection = slotPermutation reflect reflect involution involution
  where
  reflect : Cube.BondSlot4 → Cube.BondSlot4
  reflect Cube.slot0 = Cube.slot0
  reflect Cube.slot1 = Cube.slot3
  reflect Cube.slot2 = Cube.slot2
  reflect Cube.slot3 = Cube.slot1

  involution : ∀ slot → reflect (reflect slot) ≡ slot
  involution Cube.slot0 = refl
  involution Cube.slot1 = refl
  involution Cube.slot2 = refl
  involution Cube.slot3 = refl

edgeReflection : SlotPermutation4
edgeReflection = composePermutation4 quarterTurn axisReflection

oppositeAxisReflection : SlotPermutation4
oppositeAxisReflection = composePermutation4 halfTurn axisReflection

oppositeEdgeReflection : SlotPermutation4
oppositeEdgeReflection = composePermutation4 threeQuarterTurn axisReflection

quarterTurnFourthPower : ∀ slot →
  forward
    (composePermutation4 halfTurn halfTurn) slot
  ≡ slot
quarterTurnFourthPower Cube.slot0 = refl
quarterTurnFourthPower Cube.slot1 = refl
quarterTurnFourthPower Cube.slot2 = refl
quarterTurnFourthPower Cube.slot3 = refl

axisReflectionSquared : ∀ slot →
  forward
    (composePermutation4 axisReflection axisReflection) slot
  ≡ slot
axisReflectionSquared Cube.slot0 = refl
axisReflectionSquared Cube.slot1 = refl
axisReflectionSquared Cube.slot2 = refl
axisReflectionSquared Cube.slot3 = refl

dihedralConjugationRelation : ∀ slot →
  forward
    (composePermutation4 axisReflection
      (composePermutation4 quarterTurn axisReflection)) slot
  ≡ backward quarterTurn slot
dihedralConjugationRelation Cube.slot0 = refl
dihedralConjugationRelation Cube.slot1 = refl
dihedralConjugationRelation Cube.slot2 = refl
dihedralConjugationRelation Cube.slot3 = refl

data NamedD4 : Set where
  identity rotation90 rotation180 rotation270 : NamedD4
  reflectionAxis reflectionEdge reflectionOppositeAxis reflectionOppositeEdge :
    NamedD4

namedPermutation : NamedD4 → SlotPermutation4
namedPermutation identity = identityPermutation4
namedPermutation rotation90 = quarterTurn
namedPermutation rotation180 = halfTurn
namedPermutation rotation270 = threeQuarterTurn
namedPermutation reflectionAxis = axisReflection
namedPermutation reflectionEdge = edgeReflection
namedPermutation reflectionOppositeAxis = oppositeAxisReflection
namedPermutation reflectionOppositeEdge = oppositeEdgeReflection

namedD4Elements : List NamedD4
namedD4Elements =
  identity ∷ rotation90 ∷ rotation180 ∷ rotation270
  ∷ reflectionAxis ∷ reflectionEdge
  ∷ reflectionOppositeAxis ∷ reflectionOppositeEdge ∷ []

namedD4CountExact : length namedD4Elements ≡ 8
namedD4CountExact = refl

namedSubsetAction : NamedD4 → Cube.Subset4 → Cube.Subset4
namedSubsetAction identity subset = subset

namedSubsetAction rotation90 Cube.empty = Cube.empty
namedSubsetAction rotation90 Cube.s0 = Cube.s1
namedSubsetAction rotation90 Cube.s1 = Cube.s2
namedSubsetAction rotation90 Cube.s2 = Cube.s3
namedSubsetAction rotation90 Cube.s3 = Cube.s0
namedSubsetAction rotation90 Cube.s01 = Cube.s12
namedSubsetAction rotation90 Cube.s02 = Cube.s13
namedSubsetAction rotation90 Cube.s03 = Cube.s01
namedSubsetAction rotation90 Cube.s12 = Cube.s23
namedSubsetAction rotation90 Cube.s13 = Cube.s02
namedSubsetAction rotation90 Cube.s23 = Cube.s03
namedSubsetAction rotation90 Cube.s012 = Cube.s123
namedSubsetAction rotation90 Cube.s013 = Cube.s012
namedSubsetAction rotation90 Cube.s023 = Cube.s013
namedSubsetAction rotation90 Cube.s123 = Cube.s023
namedSubsetAction rotation90 Cube.s0123 = Cube.s0123

namedSubsetAction rotation180 Cube.empty = Cube.empty
namedSubsetAction rotation180 Cube.s0 = Cube.s2
namedSubsetAction rotation180 Cube.s1 = Cube.s3
namedSubsetAction rotation180 Cube.s2 = Cube.s0
namedSubsetAction rotation180 Cube.s3 = Cube.s1
namedSubsetAction rotation180 Cube.s01 = Cube.s23
namedSubsetAction rotation180 Cube.s02 = Cube.s02
namedSubsetAction rotation180 Cube.s03 = Cube.s12
namedSubsetAction rotation180 Cube.s12 = Cube.s03
namedSubsetAction rotation180 Cube.s13 = Cube.s13
namedSubsetAction rotation180 Cube.s23 = Cube.s01
namedSubsetAction rotation180 Cube.s012 = Cube.s023
namedSubsetAction rotation180 Cube.s013 = Cube.s123
namedSubsetAction rotation180 Cube.s023 = Cube.s012
namedSubsetAction rotation180 Cube.s123 = Cube.s013
namedSubsetAction rotation180 Cube.s0123 = Cube.s0123

namedSubsetAction rotation270 Cube.empty = Cube.empty
namedSubsetAction rotation270 Cube.s0 = Cube.s3
namedSubsetAction rotation270 Cube.s1 = Cube.s0
namedSubsetAction rotation270 Cube.s2 = Cube.s1
namedSubsetAction rotation270 Cube.s3 = Cube.s2
namedSubsetAction rotation270 Cube.s01 = Cube.s03
namedSubsetAction rotation270 Cube.s02 = Cube.s13
namedSubsetAction rotation270 Cube.s03 = Cube.s23
namedSubsetAction rotation270 Cube.s12 = Cube.s01
namedSubsetAction rotation270 Cube.s13 = Cube.s02
namedSubsetAction rotation270 Cube.s23 = Cube.s12
namedSubsetAction rotation270 Cube.s012 = Cube.s013
namedSubsetAction rotation270 Cube.s013 = Cube.s023
namedSubsetAction rotation270 Cube.s023 = Cube.s123
namedSubsetAction rotation270 Cube.s123 = Cube.s012
namedSubsetAction rotation270 Cube.s0123 = Cube.s0123

namedSubsetAction reflectionAxis Cube.empty = Cube.empty
namedSubsetAction reflectionAxis Cube.s0 = Cube.s0
namedSubsetAction reflectionAxis Cube.s1 = Cube.s3
namedSubsetAction reflectionAxis Cube.s2 = Cube.s2
namedSubsetAction reflectionAxis Cube.s3 = Cube.s1
namedSubsetAction reflectionAxis Cube.s01 = Cube.s03
namedSubsetAction reflectionAxis Cube.s02 = Cube.s02
namedSubsetAction reflectionAxis Cube.s03 = Cube.s01
namedSubsetAction reflectionAxis Cube.s12 = Cube.s23
namedSubsetAction reflectionAxis Cube.s13 = Cube.s13
namedSubsetAction reflectionAxis Cube.s23 = Cube.s12
namedSubsetAction reflectionAxis Cube.s012 = Cube.s023
namedSubsetAction reflectionAxis Cube.s013 = Cube.s013
namedSubsetAction reflectionAxis Cube.s023 = Cube.s012
namedSubsetAction reflectionAxis Cube.s123 = Cube.s123
namedSubsetAction reflectionAxis Cube.s0123 = Cube.s0123

namedSubsetAction reflectionEdge Cube.empty = Cube.empty
namedSubsetAction reflectionEdge Cube.s0 = Cube.s1
namedSubsetAction reflectionEdge Cube.s1 = Cube.s0
namedSubsetAction reflectionEdge Cube.s2 = Cube.s3
namedSubsetAction reflectionEdge Cube.s3 = Cube.s2
namedSubsetAction reflectionEdge Cube.s01 = Cube.s01
namedSubsetAction reflectionEdge Cube.s02 = Cube.s13
namedSubsetAction reflectionEdge Cube.s03 = Cube.s12
namedSubsetAction reflectionEdge Cube.s12 = Cube.s03
namedSubsetAction reflectionEdge Cube.s13 = Cube.s02
namedSubsetAction reflectionEdge Cube.s23 = Cube.s23
namedSubsetAction reflectionEdge Cube.s012 = Cube.s013
namedSubsetAction reflectionEdge Cube.s013 = Cube.s012
namedSubsetAction reflectionEdge Cube.s023 = Cube.s123
namedSubsetAction reflectionEdge Cube.s123 = Cube.s023
namedSubsetAction reflectionEdge Cube.s0123 = Cube.s0123

namedSubsetAction reflectionOppositeAxis Cube.empty = Cube.empty
namedSubsetAction reflectionOppositeAxis Cube.s0 = Cube.s2
namedSubsetAction reflectionOppositeAxis Cube.s1 = Cube.s1
namedSubsetAction reflectionOppositeAxis Cube.s2 = Cube.s0
namedSubsetAction reflectionOppositeAxis Cube.s3 = Cube.s3
namedSubsetAction reflectionOppositeAxis Cube.s01 = Cube.s12
namedSubsetAction reflectionOppositeAxis Cube.s02 = Cube.s02
namedSubsetAction reflectionOppositeAxis Cube.s03 = Cube.s23
namedSubsetAction reflectionOppositeAxis Cube.s12 = Cube.s01
namedSubsetAction reflectionOppositeAxis Cube.s13 = Cube.s13
namedSubsetAction reflectionOppositeAxis Cube.s23 = Cube.s03
namedSubsetAction reflectionOppositeAxis Cube.s012 = Cube.s012
namedSubsetAction reflectionOppositeAxis Cube.s013 = Cube.s123
namedSubsetAction reflectionOppositeAxis Cube.s023 = Cube.s023
namedSubsetAction reflectionOppositeAxis Cube.s123 = Cube.s013
namedSubsetAction reflectionOppositeAxis Cube.s0123 = Cube.s0123

namedSubsetAction reflectionOppositeEdge Cube.empty = Cube.empty
namedSubsetAction reflectionOppositeEdge Cube.s0 = Cube.s3
namedSubsetAction reflectionOppositeEdge Cube.s1 = Cube.s2
namedSubsetAction reflectionOppositeEdge Cube.s2 = Cube.s1
namedSubsetAction reflectionOppositeEdge Cube.s3 = Cube.s0
namedSubsetAction reflectionOppositeEdge Cube.s01 = Cube.s23
namedSubsetAction reflectionOppositeEdge Cube.s02 = Cube.s13
namedSubsetAction reflectionOppositeEdge Cube.s03 = Cube.s03
namedSubsetAction reflectionOppositeEdge Cube.s12 = Cube.s12
namedSubsetAction reflectionOppositeEdge Cube.s13 = Cube.s02
namedSubsetAction reflectionOppositeEdge Cube.s23 = Cube.s01
namedSubsetAction reflectionOppositeEdge Cube.s012 = Cube.s123
namedSubsetAction reflectionOppositeEdge Cube.s013 = Cube.s023
namedSubsetAction reflectionOppositeEdge Cube.s023 = Cube.s013
namedSubsetAction reflectionOppositeEdge Cube.s123 = Cube.s012
namedSubsetAction reflectionOppositeEdge Cube.s0123 = Cube.s0123

sameSubset : Cube.Subset4 → Cube.Subset4 → Bool
sameSubset Cube.empty Cube.empty = true
sameSubset Cube.s0 Cube.s0 = true
sameSubset Cube.s1 Cube.s1 = true
sameSubset Cube.s2 Cube.s2 = true
sameSubset Cube.s3 Cube.s3 = true
sameSubset Cube.s01 Cube.s01 = true
sameSubset Cube.s02 Cube.s02 = true
sameSubset Cube.s03 Cube.s03 = true
sameSubset Cube.s12 Cube.s12 = true
sameSubset Cube.s13 Cube.s13 = true
sameSubset Cube.s23 Cube.s23 = true
sameSubset Cube.s012 Cube.s012 = true
sameSubset Cube.s013 Cube.s013 = true
sameSubset Cube.s023 Cube.s023 = true
sameSubset Cube.s123 Cube.s123 = true
sameSubset Cube.s0123 Cube.s0123 = true
sameSubset _ _ = false

fixedNonemptySubsets : NamedD4 → List Cube.Subset4
fixedNonemptySubsets symmetry =
  filter
    (λ subset → sameSubset (namedSubsetAction symmetry subset) subset)
    Cube.nonemptySubsets4

fixedNonemptyCount : NamedD4 → Nat
fixedNonemptyCount symmetry = length (fixedNonemptySubsets symmetry)

fixedIdentityExact : fixedNonemptyCount identity ≡ 15
fixedIdentityExact = refl

fixedHalfTurnExact : fixedNonemptyCount rotation180 ≡ 3
fixedHalfTurnExact = refl

fixedQuarterTurnExact : fixedNonemptyCount rotation90 ≡ 1
fixedQuarterTurnExact = refl

fixedThreeQuarterTurnExact : fixedNonemptyCount rotation270 ≡ 1
fixedThreeQuarterTurnExact = refl

fixedAxisReflectionExact : fixedNonemptyCount reflectionAxis ≡ 7
fixedAxisReflectionExact = refl

fixedOppositeAxisReflectionExact :
  fixedNonemptyCount reflectionOppositeAxis ≡ 7
fixedOppositeAxisReflectionExact = refl

fixedEdgeReflectionExact : fixedNonemptyCount reflectionEdge ≡ 3
fixedEdgeReflectionExact = refl

fixedOppositeEdgeReflectionExact :
  fixedNonemptyCount reflectionOppositeEdge ≡ 3
fixedOppositeEdgeReflectionExact = refl

data WilsonSubsetOrbit : Set where
  emptyOrbit singletonOrbit adjacentPairOrbit oppositePairOrbit
    tripleOrbit quarticOrbit : WilsonSubsetOrbit

subsetOrbit : Cube.Subset4 → WilsonSubsetOrbit
subsetOrbit Cube.empty = emptyOrbit
subsetOrbit Cube.s0 = singletonOrbit
subsetOrbit Cube.s1 = singletonOrbit
subsetOrbit Cube.s2 = singletonOrbit
subsetOrbit Cube.s3 = singletonOrbit
subsetOrbit Cube.s01 = adjacentPairOrbit
subsetOrbit Cube.s03 = adjacentPairOrbit
subsetOrbit Cube.s12 = adjacentPairOrbit
subsetOrbit Cube.s23 = adjacentPairOrbit
subsetOrbit Cube.s02 = oppositePairOrbit
subsetOrbit Cube.s13 = oppositePairOrbit
subsetOrbit Cube.s012 = tripleOrbit
subsetOrbit Cube.s013 = tripleOrbit
subsetOrbit Cube.s023 = tripleOrbit
subsetOrbit Cube.s123 = tripleOrbit
subsetOrbit Cube.s0123 = quarticOrbit

orbitRepresentative : Cube.Subset4 → Cube.Subset4
orbitRepresentative Cube.empty = Cube.empty
orbitRepresentative Cube.s0 = Cube.s0
orbitRepresentative Cube.s1 = Cube.s0
orbitRepresentative Cube.s2 = Cube.s0
orbitRepresentative Cube.s3 = Cube.s0
orbitRepresentative Cube.s01 = Cube.s01
orbitRepresentative Cube.s03 = Cube.s01
orbitRepresentative Cube.s12 = Cube.s01
orbitRepresentative Cube.s23 = Cube.s01
orbitRepresentative Cube.s02 = Cube.s02
orbitRepresentative Cube.s13 = Cube.s02
orbitRepresentative Cube.s012 = Cube.s012
orbitRepresentative Cube.s013 = Cube.s012
orbitRepresentative Cube.s023 = Cube.s012
orbitRepresentative Cube.s123 = Cube.s012
orbitRepresentative Cube.s0123 = Cube.s0123

orbitTransport : Cube.Subset4 → NamedD4
orbitTransport Cube.empty = identity
orbitTransport Cube.s0 = identity
orbitTransport Cube.s1 = rotation90
orbitTransport Cube.s2 = rotation180
orbitTransport Cube.s3 = rotation270
orbitTransport Cube.s01 = identity
orbitTransport Cube.s12 = rotation90
orbitTransport Cube.s23 = rotation180
orbitTransport Cube.s03 = rotation270
orbitTransport Cube.s02 = identity
orbitTransport Cube.s13 = rotation90
orbitTransport Cube.s012 = identity
orbitTransport Cube.s123 = rotation90
orbitTransport Cube.s023 = rotation180
orbitTransport Cube.s013 = rotation270
orbitTransport Cube.s0123 = identity

subsetIsTransportOfOrbitRepresentative : ∀ subset →
  namedSubsetAction (orbitTransport subset)
    (orbitRepresentative subset)
  ≡ subset
subsetIsTransportOfOrbitRepresentative Cube.empty = refl
subsetIsTransportOfOrbitRepresentative Cube.s0 = refl
subsetIsTransportOfOrbitRepresentative Cube.s1 = refl
subsetIsTransportOfOrbitRepresentative Cube.s2 = refl
subsetIsTransportOfOrbitRepresentative Cube.s3 = refl
subsetIsTransportOfOrbitRepresentative Cube.s01 = refl
subsetIsTransportOfOrbitRepresentative Cube.s02 = refl
subsetIsTransportOfOrbitRepresentative Cube.s03 = refl
subsetIsTransportOfOrbitRepresentative Cube.s12 = refl
subsetIsTransportOfOrbitRepresentative Cube.s13 = refl
subsetIsTransportOfOrbitRepresentative Cube.s23 = refl
subsetIsTransportOfOrbitRepresentative Cube.s012 = refl
subsetIsTransportOfOrbitRepresentative Cube.s013 = refl
subsetIsTransportOfOrbitRepresentative Cube.s023 = refl
subsetIsTransportOfOrbitRepresentative Cube.s123 = refl
subsetIsTransportOfOrbitRepresentative Cube.s0123 = refl

record Character5 : Set where
  constructor character5
  field
    atIdentity atHalfTurn atQuarterTurns atAxisReflections atEdgeReflections : ℚ

open Character5 public

subsetPermutationCharacter : Character5
subsetPermutationCharacter =
  character5 (+ 15 / 1) (+ 3 / 1) (+ 1 / 1) (+ 7 / 1) (+ 3 / 1)

A1Character A2Character B1Character B2Character ECharacter : Character5
A1Character = character5 (+ 1 / 1) (+ 1 / 1) (+ 1 / 1) (+ 1 / 1) (+ 1 / 1)
A2Character = character5 (+ 1 / 1) (+ 1 / 1) (+ 1 / 1) (+ -1 / 1) (+ -1 / 1)
B1Character = character5 (+ 1 / 1) (+ 1 / 1) (+ -1 / 1) (+ 1 / 1) (+ -1 / 1)
B2Character = character5 (+ 1 / 1) (+ 1 / 1) (+ -1 / 1) (+ -1 / 1) (+ 1 / 1)
ECharacter = character5 (+ 2 / 1) (+ -2 / 1) 0ℚ 0ℚ 0ℚ

characterInnerProduct : Character5 → Character5 → ℚ
characterInnerProduct left right =
  ((atIdentity left * atIdentity right)
    + (atHalfTurn left * atHalfTurn right)
    + ((+ 2 / 1) * atQuarterTurns left * atQuarterTurns right)
    + ((+ 2 / 1) * atAxisReflections left * atAxisReflections right)
    + ((+ 2 / 1) * atEdgeReflections left * atEdgeReflections right))
  / (+ 8 / 1)

subsetA1MultiplicityExact :
  characterInnerProduct subsetPermutationCharacter A1Character
  ≡ + 5 / 1
subsetA1MultiplicityExact = ℚRing.solve []

subsetA2MultiplicityExact :
  characterInnerProduct subsetPermutationCharacter A2Character
  ≡ 0ℚ
subsetA2MultiplicityExact = ℚRing.solve []

subsetB1MultiplicityExact :
  characterInnerProduct subsetPermutationCharacter B1Character
  ≡ + 3 / 1
subsetB1MultiplicityExact = ℚRing.solve []

subsetB2MultiplicityExact :
  characterInnerProduct subsetPermutationCharacter B2Character
  ≡ + 1 / 1
subsetB2MultiplicityExact = ℚRing.solve []

subsetEMultiplicityExact :
  characterInnerProduct subsetPermutationCharacter ECharacter
  ≡ + 3 / 1
subsetEMultiplicityExact = ℚRing.solve []

subsetCharacterDimensionCheck :
  (+ 5 / 1) * (+ 1 / 1)
    + (+ 3 / 1) * (+ 1 / 1)
    + (+ 1 / 1) * (+ 1 / 1)
    + (+ 3 / 1) * (+ 2 / 1)
  ≡ + 15 / 1
subsetCharacterDimensionCheck = ℚRing.solve []

dihedralSlotPresentationLevel : ProofLevel
dihedralSlotPresentationLevel = machineChecked

wilsonSubsetOrbitLevel : ProofLevel
wilsonSubsetOrbitLevel = machineChecked

wilsonSubsetCharacterDecompositionLevel : ProofLevel
wilsonSubsetCharacterDecompositionLevel = machineChecked
