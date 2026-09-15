module DASHI.Wikimedia.IbrahimMonster369OEISSeparatingHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.DASHIMathOEIS196883AuditRoadmapExact as Audit
import DASHI.Wikimedia.IbrahimMonster3BOEIS369UnifiedCrossPollinationExact as Cross
import DASHI.Moonshine.Base369ZetaHeisenbergFiftyFourCarrierExact as Zeta54
import DASHI.Moonshine.Monster3BBalancedRegularFibreExact as ThreeB

------------------------------------------------------------------------
-- MONSTER369 / OEIS SEPARATING HYPERFABRIC
--
-- This owner does not add another numerical atlas.  It consumes the existing
-- OEIS/369/Monster receipts and asks the RSA-inspired question in a
-- Monster-native form:
--
--   which retained coordinates can separate the worlds that a declared
--   Monster consumer distinguishes?
--
-- An edge is therefore consumer-indexed.  Hitting all declared edges is only
-- a finite adequacy statement for this atlas; it is not a global minimality
-- theorem and it is never permission to promote an OEIS identity into a
-- Monster action or representation identity.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Coordinate universe.  Numeric/OEIS coordinates and semantic/action
--    coordinates are deliberately different constructors even when they share
--    an integer.
------------------------------------------------------------------------

data Monster369Coordinate : Set where
  ternary3Arithmetic : Monster369Coordinate
  zetaTrit6Carrier : Monster369Coordinate
  nonary9Carrier : Monster369Coordinate
  hypervoxel27Carrier : Monster369Coordinate
  zeta54Carrier : Monster369Coordinate
  multiplicity90Arithmetic : Monster369Coordinate
  heisenberg729Carrier : Monster369Coordinate
  monster3B65610Character : Monster369Coordinate
  balanced196830Bulk : Monster369Coordinate
  monster196883Degree : Monster369Coordinate
  moonshine196884Dimension : Monster369Coordinate
  ogg475971Factor : Monster369Coordinate
  zetaPhaseCoordinate : Monster369Coordinate
  tauModularCoordinate : Monster369Coordinate
  actualWeylActionCoordinate : Monster369Coordinate
  selected3BRestrictionCoordinate : Monster369Coordinate
  twelvePlusSeventyEightCoordinate : Monster369Coordinate

  oeisA000244Coordinate : Monster369Coordinate
  oeisA005052Coordinate : Monster369Coordinate
  oeisA001379Coordinate : Monster369Coordinate
  oeisA309510Coordinate : Monster369Coordinate
  oeisA199014Coordinate : Monster369Coordinate
  sameIntegerCollisionOnly : Monster369Coordinate

------------------------------------------------------------------------
-- 2. Relationship classification requested by the snowball discipline.
------------------------------------------------------------------------

data RelationStrength : Set where
  exactArithmetic : RelationStrength
  oeisNavigation : RelationStrength
  typedCarrierMap : RelationStrength
  representationActionTheorem : RelationStrength
  unpaidCoincidence : RelationStrength

coordinateStrength : Monster369Coordinate → RelationStrength
coordinateStrength ternary3Arithmetic = exactArithmetic
coordinateStrength zetaTrit6Carrier = typedCarrierMap
coordinateStrength nonary9Carrier = typedCarrierMap
coordinateStrength hypervoxel27Carrier = typedCarrierMap
coordinateStrength zeta54Carrier = typedCarrierMap
coordinateStrength multiplicity90Arithmetic = exactArithmetic
coordinateStrength heisenberg729Carrier = typedCarrierMap
coordinateStrength monster3B65610Character = representationActionTheorem
coordinateStrength balanced196830Bulk = representationActionTheorem
coordinateStrength monster196883Degree = representationActionTheorem
coordinateStrength moonshine196884Dimension = representationActionTheorem
coordinateStrength ogg475971Factor = exactArithmetic
coordinateStrength zetaPhaseCoordinate = typedCarrierMap
coordinateStrength tauModularCoordinate = typedCarrierMap
coordinateStrength actualWeylActionCoordinate = representationActionTheorem
coordinateStrength selected3BRestrictionCoordinate = representationActionTheorem
coordinateStrength twelvePlusSeventyEightCoordinate = representationActionTheorem
coordinateStrength oeisA000244Coordinate = oeisNavigation
coordinateStrength oeisA005052Coordinate = oeisNavigation
coordinateStrength oeisA001379Coordinate = oeisNavigation
coordinateStrength oeisA309510Coordinate = oeisNavigation
coordinateStrength oeisA199014Coordinate = oeisNavigation
coordinateStrength sameIntegerCollisionOnly = unpaidCoincidence

-- Deliberately stricter than `coordinateStrength`: character/dimension theorems
-- are representation evidence but do not thereby become literal action maps.
proofBearingForMonsterAction : Monster369Coordinate → Bool
proofBearingForMonsterAction actualWeylActionCoordinate = true
proofBearingForMonsterAction selected3BRestrictionCoordinate = true
proofBearingForMonsterAction twelvePlusSeventyEightCoordinate = true
proofBearingForMonsterAction _ = false

------------------------------------------------------------------------
-- 3. Reuse exact arithmetic/carrier receipts already paid elsewhere.
------------------------------------------------------------------------

a005052Level2Is90 : Cross.a005052 2 ≡ 90
a005052Level2Is90 = refl

a005052Level8Is65610 : Cross.a005052 8 ≡ 65610
a005052Level8Is65610 = Cross.a005052Level8Is65610

a005052Level9Is196830 : Cross.a005052 9 ≡ 196830
a005052Level9Is196830 = Cross.a005052Level9Is196830

phaseToBulkNumericalStep : 3 * Cross.a005052 8 ≡ Cross.a005052 9
phaseToBulkNumericalStep = Cross.a005052PhaseToBulkStep

zeta54CarrierCountIs54 : Zeta54.zeta54SiteCount ≡ 54
zeta54CarrierCountIs54 = Zeta54.zeta54SiteCountIsFiftyFour

sixByNineCarrierCountIs54 : Zeta54.sixByNineSiteCount ≡ 54
sixByNineCarrierCountIs54 = Zeta54.sixByNineSiteCountIsFiftyFour

heisenbergCarrierCountIs729 : Zeta54.heisenbergStateCount ≡ 729
heisenbergCarrierCountIs729 = Zeta54.heisenbergStateCountIsSevenTwentyNine

monsterIdentityEvaluationIs196883 :
  ThreeB.identityEvaluation ThreeB.monster3BResidualRegularCarrier ≡ 196883
monsterIdentityEvaluationIs196883 = Cross.threeBIdentityEvaluationStill196883

moonshineDimensionIs196884 : ThreeB.monster3BConformalDimension ≡ 196884
moonshineDimensionIs196884 = Cross.threeBConformalDimensionStill196884

largestOggTripleProductIs196883 : 47 * 59 * 71 ≡ 196883
largestOggTripleProductIs196883 = Audit.largestThreeFactorProduct

------------------------------------------------------------------------
-- 4. Monster-native consumers and hyperedges.
--
-- Each edge lists three independently useful coordinates for a particular
-- separation obligation.  This is a finite search surface, not a claim that
-- any one coordinate is globally sufficient for the consumer.
------------------------------------------------------------------------

data MonsterConsumer : Set where
  phaseResolutionConsumer : MonsterConsumer
  inversionConsumer : MonsterConsumer
  heisenbergRecognitionConsumer : MonsterConsumer
  threeBRestrictionConsumer : MonsterConsumer
  multiplicityTwelveSeventyEightConsumer : MonsterConsumer

record SeparatingEdge : Set where
  constructor separating-edge
  field
    consumer : MonsterConsumer
    coordinateA : Monster369Coordinate
    coordinateB : Monster369Coordinate
    coordinateC : Monster369Coordinate
    reason : String
open SeparatingEdge public

phaseResolutionEdge : SeparatingEdge
phaseResolutionEdge = separating-edge
  phaseResolutionConsumer
  zetaPhaseCoordinate monster3B65610Character zeta54Carrier
  "phase-sensitive consumer: scalar phase, character multiplicity, or typed zeta-sheet carrier may separate a collision; A005052 alone does not"

inversionEdge : SeparatingEdge
inversionEdge = separating-edge
  inversionConsumer
  zetaPhaseCoordinate tauModularCoordinate actualWeylActionCoordinate
  "inversion consumer: retain an actual involutive/phase/action coordinate rather than a shared numeral"

heisenbergRecognitionEdge : SeparatingEdge
heisenbergRecognitionEdge = separating-edge
  heisenbergRecognitionConsumer
  heisenberg729Carrier zeta54Carrier actualWeylActionCoordinate
  "Heisenberg consumer: 729-state carrier, six-axis zeta chart, or actual Weyl action can expose a collision; cardinality alone is not representation identity"

threeBRestrictionEdge : SeparatingEdge
threeBRestrictionEdge = separating-edge
  threeBRestrictionConsumer
  selected3BRestrictionCoordinate monster3B65610Character monster196883Degree
  "3B restriction consumer: selected restriction/character coordinates are semantic; A001379 is only navigation to the external degree family"

multiplicityTwelveSeventyEightEdge : SeparatingEdge
multiplicityTwelveSeventyEightEdge = separating-edge
  multiplicityTwelveSeventyEightConsumer
  twelvePlusSeventyEightCoordinate selected3BRestrictionCoordinate actualWeylActionCoordinate
  "12+78 consumer: needs same-action multiplicity/restriction data; 90=10*3^2 is only arithmetic provenance"

------------------------------------------------------------------------
-- 5. Hitting predicate.
------------------------------------------------------------------------

SelectedCoordinateFamily : Set
SelectedCoordinateFamily = Monster369Coordinate → Bool

_or_ : Bool → Bool → Bool
true or _ = true
false or b = b

_and_ : Bool → Bool → Bool
true and b = b
false and _ = false

hitsEdge : SelectedCoordinateFamily → SeparatingEdge → Bool
hitsEdge selected edge =
  selected (coordinateA edge) or
  (selected (coordinateB edge) or selected (coordinateC edge))

hitsEveryDeclaredConsumer : SelectedCoordinateFamily → Bool
hitsEveryDeclaredConsumer selected =
  hitsEdge selected phaseResolutionEdge and
  (hitsEdge selected inversionEdge and
  (hitsEdge selected heisenbergRecognitionEdge and
  (hitsEdge selected threeBRestrictionEdge and
   hitsEdge selected multiplicityTwelveSeventyEightEdge)))

canonicalTypedSelection : SelectedCoordinateFamily
canonicalTypedSelection zetaPhaseCoordinate = true
canonicalTypedSelection actualWeylActionCoordinate = true
canonicalTypedSelection selected3BRestrictionCoordinate = true
canonicalTypedSelection twelvePlusSeventyEightCoordinate = true
canonicalTypedSelection _ = false

canonicalTypedSelectionHitsEveryDeclaredConsumer :
  hitsEveryDeclaredConsumer canonicalTypedSelection ≡ true
canonicalTypedSelectionHitsEveryDeclaredConsumer = refl

oeisOnlySelection : SelectedCoordinateFamily
oeisOnlySelection oeisA000244Coordinate = true
oeisOnlySelection oeisA005052Coordinate = true
oeisOnlySelection oeisA001379Coordinate = true
oeisOnlySelection oeisA309510Coordinate = true
oeisOnlySelection oeisA199014Coordinate = true
oeisOnlySelection _ = false

oeisOnlySelectionHitsEveryDeclaredConsumer :
  hitsEveryDeclaredConsumer oeisOnlySelection ≡ false
oeisOnlySelectionHitsEveryDeclaredConsumer = refl

------------------------------------------------------------------------
-- 6. Snowball / WrongType boundaries.
------------------------------------------------------------------------

data OEISIdentityCreatesMonsterAction : Set where
data EqualIntegerCreatesTypedCarrierMap : Set where
data DivisorMembershipCreates369Semantics : Set where
data FiniteHittingSetCreatesGlobalMinimality : Set where

oeisIdentityDoesNotCreateMonsterAction : OEISIdentityCreatesMonsterAction → ⊥
oeisIdentityDoesNotCreateMonsterAction ()

equalIntegerDoesNotCreateCarrierMap : EqualIntegerCreatesTypedCarrierMap → ⊥
equalIntegerDoesNotCreateCarrierMap ()

divisorMembershipDoesNotCreate369Semantics : DivisorMembershipCreates369Semantics → ⊥
divisorMembershipDoesNotCreate369Semantics ()

finiteHittingSetDoesNotCreateGlobalMinimality : FiniteHittingSetCreatesGlobalMinimality → ⊥
finiteHittingSetDoesNotCreateGlobalMinimality ()

record Monster369SeparatingHyperfabricBoundary : Set where
  constructor monster369-separating-hyperfabric-boundary
  field
    reusesExistingOEIS369Atlas : Bool
    typedMonsterCoordinatesRetained : Bool
    monsterNativeConsumerEdgesTyped : Bool
    canonicalTypedSelectionHitsEveryDeclaredConsumer : Bool
    oeisOnlySelectionHitsEveryRepresentationConsumer : Bool
    oeisIdentityCreatesMonsterAction : Bool
    equalIntegerCreatesTypedCarrierMap : Bool
    divisorMembershipCreates369Semantics : Bool
    minimumHittingSetKernelProved : Bool
    consumerCollisionReopensTypedResidual : Bool
    nextResidual : String
open Monster369SeparatingHyperfabricBoundary public

canonicalMonster369SeparatingHyperfabricBoundary : Monster369SeparatingHyperfabricBoundary
canonicalMonster369SeparatingHyperfabricBoundary =
  monster369-separating-hyperfabric-boundary
    true true true true
    false false false false false true
    "Instantiate more literal Monster worlds/consumers against this finite coordinate universe. If a typed selection collides, retain the first semantic coordinate that separates the failed consumer. OEIS may propose candidate coordinates or negative controls, but only typed carrier/action/source receipts can promote them into the Monster proof graph. Do not claim a globally minimal hitting set until an exhaustive finite search and kernel-level minimum proof are separately paid."
