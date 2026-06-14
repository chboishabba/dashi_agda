module DASHI.Physics.Closure.BTCanonicalNeckAnalogue where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Concrete finite Bruhat-Tits neck analogues.
--
-- This module records only the discrete BT neck analogue at the canonical
-- prime lanes p = 2, 3, 7.  For each lane the cross-section is the finite
-- neighbor sphere of a (p + 1)-regular Bruhat-Tits tree, so its cardinality
-- is definitionally p + 1.
--
-- It deliberately does not promote a smooth S2 cross-section, a smooth
-- epsilon-neck theorem, Ricci-flow surgery, or any terminal geometry claim.

data ⊥ : Set where

NotTrue : Bool → Set
NotTrue b =
  b ≡ true → ⊥

falseNotTrue : NotTrue false
falseNotTrue ()

data BTPrimeLane : Set where
  p2Lane :
    BTPrimeLane
  p3Lane :
    BTPrimeLane
  p7Lane :
    BTPrimeLane

canonicalBTPrimeLanes : List BTPrimeLane
canonicalBTPrimeLanes =
  p2Lane
  ∷ p3Lane
  ∷ p7Lane
  ∷ []

primeValue : BTPrimeLane → Nat
primeValue p2Lane =
  2
primeValue p3Lane =
  3
primeValue p7Lane =
  7

crossSectionCardinalityForLane : BTPrimeLane → Nat
crossSectionCardinalityForLane lane =
  suc (primeValue lane)

data BTDiscreteCenter : Set where
  canonicalRootCenter :
    BTPrimeLane →
    BTDiscreteCenter
  depthCenter :
    BTPrimeLane →
    Nat →
    BTDiscreteCenter

data DepthIndexedScaleToken : Set where
  depthScaleToken :
    BTPrimeLane →
    Nat →
    DepthIndexedScaleToken

data NeckRadiusToken : Set where
  radiusOneEdgeAtDepth :
    BTPrimeLane →
    Nat →
    NeckRadiusToken

data CrossSectionAnalogue : Set where
  finiteNeighborSphere :
    BTPrimeLane →
    CrossSectionAnalogue

data PathCylinderAnalogue : Set where
  btGeodesicPathTimesFiniteSphere :
    BTPrimeLane →
    Nat →
    CrossSectionAnalogue →
    PathCylinderAnalogue

data BTNeckAnalogueStatus : Set where
  concreteDiscreteBTNeckAnalogue :
    BTNeckAnalogueStatus
  smoothS2CrossSectionUnavailable :
    BTNeckAnalogueStatus
  epsilonNeckTheoremUnavailable :
    BTNeckAnalogueStatus

canonicalBTNeckAnalogueStatus : List BTNeckAnalogueStatus
canonicalBTNeckAnalogueStatus =
  concreteDiscreteBTNeckAnalogue
  ∷ smoothS2CrossSectionUnavailable
  ∷ epsilonNeckTheoremUnavailable
  ∷ []

data SmoothS2CrossSection : Set where

smoothS2CrossSectionUnavailableHere :
  SmoothS2CrossSection →
  ⊥
smoothS2CrossSectionUnavailableHere ()

data SmoothEpsilonNeckTheorem : Set where

epsilonNeckTheoremUnavailableHere :
  SmoothEpsilonNeckTheorem →
  ⊥
epsilonNeckTheoremUnavailableHere ()

btDiscreteNeckStatement : String
btDiscreteNeckStatement =
  "BT discrete neck analogue: center at depth d, scale token (p,d), cross-section finite neighbor sphere of cardinality p+1, and path-cylinder analogue geodesic path times finite sphere."

smoothBoundaryStatement : String
smoothBoundaryStatement =
  "Smooth S2 cross-section and smooth epsilon-neck theorem are unavailable and not promoted in this finite BT analogue."

record BTCanonicalNeckAnalogue : Set where
  field
    status :
      List BTNeckAnalogueStatus

    statusIsCanonical :
      status ≡ canonicalBTNeckAnalogueStatus

    primeLane :
      BTPrimeLane

    pValue :
      Nat

    pValueIsPrimeLaneValue :
      pValue ≡ primeValue primeLane

    depth :
      Nat

    center :
      BTDiscreteCenter

    centerIsDepthCenter :
      center ≡ depthCenter primeLane depth

    scaleToken :
      DepthIndexedScaleToken

    scaleTokenIsDepthIndexed :
      scaleToken ≡ depthScaleToken primeLane depth

    neckRadius :
      NeckRadiusToken

    neckRadiusIsOneEdgeAtDepth :
      neckRadius ≡ radiusOneEdgeAtDepth primeLane depth

    crossSection :
      CrossSectionAnalogue

    crossSectionIsFiniteNeighborSphere :
      crossSection ≡ finiteNeighborSphere primeLane

    crossSectionCardinality :
      Nat

    crossSectionCardinalityIsPPlusOne :
      crossSectionCardinality ≡ crossSectionCardinalityForLane primeLane

    pathCylinder :
      PathCylinderAnalogue

    pathCylinderIsCanonical :
      pathCylinder
      ≡
      btGeodesicPathTimesFiniteSphere primeLane depth crossSection

    pathCylinderAnalogueConstructed :
      Bool

    pathCylinderAnalogueConstructedIsTrue :
      pathCylinderAnalogueConstructed ≡ true

    smoothS2CrossSectionPromoted :
      Bool

    smoothS2CrossSectionPromotedIsFalse :
      smoothS2CrossSectionPromoted ≡ false

    smoothS2CrossSectionBlocked :
      NotTrue smoothS2CrossSectionPromoted

    epsilonNeckTheoremPromoted :
      Bool

    epsilonNeckTheoremPromotedIsFalse :
      epsilonNeckTheoremPromoted ≡ false

    epsilonNeckTheoremBlocked :
      NotTrue epsilonNeckTheoremPromoted

    clayOrGeometrizationPromoted :
      Bool

    clayOrGeometrizationPromotedIsFalse :
      clayOrGeometrizationPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ btDiscreteNeckStatement

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ smoothBoundaryStatement

open BTCanonicalNeckAnalogue public

canonicalBTNeckAnalogueAt :
  BTPrimeLane →
  Nat →
  BTCanonicalNeckAnalogue
canonicalBTNeckAnalogueAt lane d =
  record
    { status =
        canonicalBTNeckAnalogueStatus
    ; statusIsCanonical =
        refl
    ; primeLane =
        lane
    ; pValue =
        primeValue lane
    ; pValueIsPrimeLaneValue =
        refl
    ; center =
        depthCenter lane d
    ; centerIsDepthCenter =
        refl
    ; depth =
        d
    ; scaleToken =
        depthScaleToken lane d
    ; scaleTokenIsDepthIndexed =
        refl
    ; neckRadius =
        radiusOneEdgeAtDepth lane d
    ; neckRadiusIsOneEdgeAtDepth =
        refl
    ; crossSection =
        finiteNeighborSphere lane
    ; crossSectionIsFiniteNeighborSphere =
        refl
    ; crossSectionCardinality =
        crossSectionCardinalityForLane lane
    ; crossSectionCardinalityIsPPlusOne =
        refl
    ; pathCylinder =
        btGeodesicPathTimesFiniteSphere lane d (finiteNeighborSphere lane)
    ; pathCylinderIsCanonical =
        refl
    ; pathCylinderAnalogueConstructed =
        true
    ; pathCylinderAnalogueConstructedIsTrue =
        refl
    ; smoothS2CrossSectionPromoted =
        false
    ; smoothS2CrossSectionPromotedIsFalse =
        refl
    ; smoothS2CrossSectionBlocked =
        falseNotTrue
    ; epsilonNeckTheoremPromoted =
        false
    ; epsilonNeckTheoremPromotedIsFalse =
        refl
    ; epsilonNeckTheoremBlocked =
        falseNotTrue
    ; clayOrGeometrizationPromoted =
        false
    ; clayOrGeometrizationPromotedIsFalse =
        refl
    ; statement =
        btDiscreteNeckStatement
    ; statementIsCanonical =
        refl
    ; boundaryStatement =
        smoothBoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    }

canonicalP2BTNeckAnalogue :
  BTCanonicalNeckAnalogue
canonicalP2BTNeckAnalogue =
  canonicalBTNeckAnalogueAt p2Lane 2

canonicalP3BTNeckAnalogue :
  BTCanonicalNeckAnalogue
canonicalP3BTNeckAnalogue =
  canonicalBTNeckAnalogueAt p3Lane 3

canonicalP7BTNeckAnalogue :
  BTCanonicalNeckAnalogue
canonicalP7BTNeckAnalogue =
  canonicalBTNeckAnalogueAt p7Lane 7

p2CrossSectionCardinalityIs3 :
  crossSectionCardinality canonicalP2BTNeckAnalogue ≡ 3
p2CrossSectionCardinalityIs3 =
  refl

p3CrossSectionCardinalityIs4 :
  crossSectionCardinality canonicalP3BTNeckAnalogue ≡ 4
p3CrossSectionCardinalityIs4 =
  refl

p7CrossSectionCardinalityIs8 :
  crossSectionCardinality canonicalP7BTNeckAnalogue ≡ 8
p7CrossSectionCardinalityIs8 =
  refl

p2PathCylinderConstructed :
  pathCylinderAnalogueConstructed canonicalP2BTNeckAnalogue ≡ true
p2PathCylinderConstructed =
  refl

p3PathCylinderConstructed :
  pathCylinderAnalogueConstructed canonicalP3BTNeckAnalogue ≡ true
p3PathCylinderConstructed =
  refl

p7PathCylinderConstructed :
  pathCylinderAnalogueConstructed canonicalP7BTNeckAnalogue ≡ true
p7PathCylinderConstructed =
  refl

p2SmoothS2CrossSectionNotPromoted :
  smoothS2CrossSectionPromoted canonicalP2BTNeckAnalogue ≡ false
p2SmoothS2CrossSectionNotPromoted =
  refl

p3SmoothS2CrossSectionNotPromoted :
  smoothS2CrossSectionPromoted canonicalP3BTNeckAnalogue ≡ false
p3SmoothS2CrossSectionNotPromoted =
  refl

p7SmoothS2CrossSectionNotPromoted :
  smoothS2CrossSectionPromoted canonicalP7BTNeckAnalogue ≡ false
p7SmoothS2CrossSectionNotPromoted =
  refl

p2EpsilonNeckTheoremNotPromoted :
  epsilonNeckTheoremPromoted canonicalP2BTNeckAnalogue ≡ false
p2EpsilonNeckTheoremNotPromoted =
  refl

p3EpsilonNeckTheoremNotPromoted :
  epsilonNeckTheoremPromoted canonicalP3BTNeckAnalogue ≡ false
p3EpsilonNeckTheoremNotPromoted =
  refl

p7EpsilonNeckTheoremNotPromoted :
  epsilonNeckTheoremPromoted canonicalP7BTNeckAnalogue ≡ false
p7EpsilonNeckTheoremNotPromoted =
  refl
