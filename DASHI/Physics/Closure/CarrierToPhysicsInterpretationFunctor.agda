module DASHI.Physics.Closure.CarrierToPhysicsInterpretationFunctor where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)

import DASHI.Physics.Closure.FractranPrimeLaneValuationReceiptSurface as FractranLane
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Moonshine
import DASHI.Physics.Closure.PrimeLaneGaugeAssignmentReceiptSurface as LaneGauge
import DASHI.Physics.Boundaries.ClayYMGap as ClayBoundary
import DASHI.Physics.Boundaries.HiggsPDGBoundary as HiggsBoundary
import DASHI.Physics.QFT.ExactSMMatchToken as ExactSM
import DASHI.Physics.QFT.DHRThermodynamicLimit as DHRLimit
import Ontology.GodelLattice as GL
import Ontology.Hecke.FactorVecInstances as FVI

------------------------------------------------------------------------
-- Gate 1: carrier-to-physics interpretation functor surface.
--
-- This module commits the prime-lane object map used by the physics receipts:
-- p2 maps to U(1)_Y, p3 maps to SU(2)_L, p5 maps to SU(3)_c, p7 is kept as a
-- high-energy SU(2)_R bridge lane, and p>=11 lanes remain matter/trivial-gauge
-- lanes.  The graph-level object/morphism map is inhabited here.  Semantic
-- representation, prime-bump covariance, and depth-transition naturality are
-- inhabited at the receipt surface; filtered-colimit and DHR-sector
-- compatibility remain explicit missing primitives.

data CarrierToPhysicsInterpretationStatus : Set where
  graphFunctorCommittedNoFullPhysicsPromotion :
    CarrierToPhysicsInterpretationStatus

data CarrierToPhysicsInterpretationPromotionAuthorityToken : Set where

data DASHICarrierObject : Set where
  factorVecCarrierObject :
    DASHICarrierObject

  primeLaneCarrierObject :
    Moonshine.MonsterPrimeLane →
    DASHICarrierObject

  depthCarrierObject :
    Nat →
    DASHICarrierObject

data PhysFieldObject : Set where
  productGaugeBundleObject :
    PhysFieldObject

  gaugeLaneRepresentationObject :
    LaneGauge.E8McKayLaneGaugeFactor →
    PhysFieldObject

  depthFieldBundleObject :
    Nat →
    PhysFieldObject

carrierToPhysicsObjectMap :
  DASHICarrierObject →
  PhysFieldObject
carrierToPhysicsObjectMap factorVecCarrierObject =
  productGaugeBundleObject
carrierToPhysicsObjectMap (primeLaneCarrierObject p) =
  gaugeLaneRepresentationObject
    (LaneGauge.e8MckayPrimeLaneGaugeFactor p)
carrierToPhysicsObjectMap (depthCarrierObject d) =
  depthFieldBundleObject d

data DASHICarrierMorphism :
  DASHICarrierObject →
  DASHICarrierObject →
  Set where
  carrierIdentity :
    (x : DASHICarrierObject) →
    DASHICarrierMorphism x x

  primeBumpShift :
    (p : Moonshine.MonsterPrimeLane) →
    DASHICarrierMorphism factorVecCarrierObject factorVecCarrierObject

  laneToProductInclusion :
    (p : Moonshine.MonsterPrimeLane) →
    DASHICarrierMorphism
      (primeLaneCarrierObject p)
      factorVecCarrierObject

  depthTransition :
    (d : Nat) →
    DASHICarrierMorphism
      (depthCarrierObject d)
      (depthCarrierObject (suc d))

  carrierComposite :
    {x y z : DASHICarrierObject} →
    DASHICarrierMorphism y z →
    DASHICarrierMorphism x y →
    DASHICarrierMorphism x z

data PhysicalCarrierMorphism :
  DASHICarrierObject →
  DASHICarrierObject →
  Set where
  physicalIdentity :
    (x : DASHICarrierObject) →
    PhysicalCarrierMorphism x x

  physicalPrimeBumpShift :
    (p : Moonshine.MonsterPrimeLane) →
    PhysicalCarrierMorphism factorVecCarrierObject factorVecCarrierObject

  physicalLaneToProductInclusion :
    (p : Moonshine.MonsterPrimeLane) →
    PhysicalCarrierMorphism
      (primeLaneCarrierObject p)
      factorVecCarrierObject

  physicalDepthTransition :
    (d : Nat) →
    PhysicalCarrierMorphism
      (depthCarrierObject d)
      (depthCarrierObject (suc d))

  physicalComposite :
    {x y z : DASHICarrierObject} →
    PhysicalCarrierMorphism y z →
    PhysicalCarrierMorphism x y →
    PhysicalCarrierMorphism x z

physicalCarrierIdentity :
  (x : DASHICarrierObject) →
  PhysicalCarrierMorphism x x
physicalCarrierIdentity =
  physicalIdentity

physicalCarrierCompose :
  {x y z : DASHICarrierObject} →
  PhysicalCarrierMorphism y z →
  PhysicalCarrierMorphism x y →
  PhysicalCarrierMorphism x z
physicalCarrierCompose (physicalIdentity _) f =
  f
physicalCarrierCompose g (physicalIdentity _) =
  g
physicalCarrierCompose g f =
  physicalComposite g f

record PhysicalCarrierCategory : Setω where
  field
    Object :
      Set

    Morphism :
      Object →
      Object →
      Set

    identity :
      (x : Object) →
      Morphism x x

    compose :
      {x y z : Object} →
      Morphism y z →
      Morphism x y →
      Morphism x z

open PhysicalCarrierCategory public

canonicalPhysicalCarrierCategory :
  PhysicalCarrierCategory
canonicalPhysicalCarrierCategory =
  record
    { Object =
        DASHICarrierObject
    ; Morphism =
        PhysicalCarrierMorphism
    ; identity =
        physicalCarrierIdentity
    ; compose =
        physicalCarrierCompose
    }

physicalCarrierComposeLeftIdentity :
  {x y : DASHICarrierObject} →
  (f : PhysicalCarrierMorphism x y) →
  physicalCarrierCompose (physicalCarrierIdentity y) f
  ≡
  f
physicalCarrierComposeLeftIdentity f =
  refl

physicalCarrierComposeRightIdentity :
  {x y : DASHICarrierObject} →
  (f : PhysicalCarrierMorphism x y) →
  physicalCarrierCompose f (physicalCarrierIdentity x)
  ≡
  f
physicalCarrierComposeRightIdentity (physicalIdentity _) =
  refl
physicalCarrierComposeRightIdentity (physicalPrimeBumpShift _) =
  refl
physicalCarrierComposeRightIdentity (physicalLaneToProductInclusion _) =
  refl
physicalCarrierComposeRightIdentity (physicalDepthTransition _) =
  refl
physicalCarrierComposeRightIdentity (physicalComposite _ _) =
  refl

sym :
  {A : Set} →
  {x y : A} →
  x ≡ y →
  y ≡ x
sym refl =
  refl

data PhysicalCarrierCategoryLawMissingField : Set where
  missingPhysicalCarrierCategoryLawReceiptAssociativity :
    PhysicalCarrierCategoryLawMissingField

record PhysicalCarrierAssociativityFailClosedReceipt : Setω where
  field
    missingField :
      PhysicalCarrierCategoryLawMissingField

    missingFieldIsCanonical :
      missingField
      ≡
      missingPhysicalCarrierCategoryLawReceiptAssociativity

    nonIdentityLeftNestedShape :
      PhysicalCarrierMorphism
        factorVecCarrierObject
        factorVecCarrierObject

    nonIdentityLeftNestedShapeIsCanonical :
      nonIdentityLeftNestedShape
      ≡
      physicalComposite
        (physicalPrimeBumpShift Moonshine.p2)
        (physicalComposite
          (physicalPrimeBumpShift Moonshine.p3)
          (physicalPrimeBumpShift Moonshine.p5))

    nonIdentityRightNestedShape :
      PhysicalCarrierMorphism
        factorVecCarrierObject
        factorVecCarrierObject

    nonIdentityRightNestedShapeIsCanonical :
      nonIdentityRightNestedShape
      ≡
      physicalComposite
        (physicalComposite
          (physicalPrimeBumpShift Moonshine.p2)
          (physicalPrimeBumpShift Moonshine.p3))
        (physicalPrimeBumpShift Moonshine.p5)

    associativityPromoted :
      Bool

    associativityPromotedIsFalse :
      associativityPromoted ≡ false

    boundary :
      List String

open PhysicalCarrierAssociativityFailClosedReceipt public

canonicalPhysicalCarrierAssociativityFailClosedReceipt :
  PhysicalCarrierAssociativityFailClosedReceipt
canonicalPhysicalCarrierAssociativityFailClosedReceipt =
  record
    { missingField =
        missingPhysicalCarrierCategoryLawReceiptAssociativity
    ; missingFieldIsCanonical =
        refl
    ; nonIdentityLeftNestedShape =
        physicalComposite
          (physicalPrimeBumpShift Moonshine.p2)
          (physicalComposite
            (physicalPrimeBumpShift Moonshine.p3)
            (physicalPrimeBumpShift Moonshine.p5))
    ; nonIdentityLeftNestedShapeIsCanonical =
        refl
    ; nonIdentityRightNestedShape =
        physicalComposite
          (physicalComposite
            (physicalPrimeBumpShift Moonshine.p2)
            (physicalPrimeBumpShift Moonshine.p3))
          (physicalPrimeBumpShift Moonshine.p5)
    ; nonIdentityRightNestedShapeIsCanonical =
        refl
    ; associativityPromoted =
        false
    ; associativityPromotedIsFalse =
        refl
    ; boundary =
        "PhysicalCarrierCategoryLawReceipt.associativity is not inhabited here"
        ∷ "physicalCarrierCompose normalizes identities but leaves non-identity triple composites as differently nested physicalComposite trees"
        ∷ "A concrete associativity theorem requires an explicit quotient, normal form, or associativity field for physicalComposite"
        ∷ "The Gate 1 graph functor laws below do not depend on this blocked physical-carrier category theorem"
        ∷ []
    }

record PhysicalCarrierCategoryLawReceipt : Setω where
  field
    category :
      PhysicalCarrierCategory

    categoryIsCanonical :
      CarrierToPhysicsInterpretationStatus

    leftIdentity :
      {x y : DASHICarrierObject} →
      (f : PhysicalCarrierMorphism x y) →
      physicalCarrierCompose (physicalCarrierIdentity y) f
      ≡
      f

    rightIdentity :
      {x y : DASHICarrierObject} →
      (f : PhysicalCarrierMorphism x y) →
      physicalCarrierCompose f (physicalCarrierIdentity x)
      ≡
      f

    associativityFailClosed :
      PhysicalCarrierAssociativityFailClosedReceipt

open PhysicalCarrierCategoryLawReceipt public

canonicalPhysicalCarrierCategoryLawReceipt :
  PhysicalCarrierCategoryLawReceipt
canonicalPhysicalCarrierCategoryLawReceipt =
  record
    { category =
        canonicalPhysicalCarrierCategory
    ; categoryIsCanonical =
        graphFunctorCommittedNoFullPhysicsPromotion
    ; leftIdentity =
        physicalCarrierComposeLeftIdentity
    ; rightIdentity =
        physicalCarrierComposeRightIdentity
    ; associativityFailClosed =
        canonicalPhysicalCarrierAssociativityFailClosedReceipt
    }

data PhysFieldMorphism :
  PhysFieldObject →
  PhysFieldObject →
  Set where
  physIdentity :
    (x : PhysFieldObject) →
    PhysFieldMorphism x x

  gaugeCovariantPrimeShift :
    (p : Moonshine.MonsterPrimeLane) →
    PhysFieldMorphism productGaugeBundleObject productGaugeBundleObject

  gaugeLaneToProductInclusion :
    (p : Moonshine.MonsterPrimeLane) →
    PhysFieldMorphism
      (gaugeLaneRepresentationObject
        (LaneGauge.e8MckayPrimeLaneGaugeFactor p))
      productGaugeBundleObject

  depthFieldTransition :
    (d : Nat) →
    PhysFieldMorphism
      (depthFieldBundleObject d)
      (depthFieldBundleObject (suc d))

  physComposite :
    {x y z : PhysFieldObject} →
    PhysFieldMorphism y z →
    PhysFieldMorphism x y →
    PhysFieldMorphism x z

carrierCompose :
  {x y z : DASHICarrierObject} →
  DASHICarrierMorphism y z →
  DASHICarrierMorphism x y →
  DASHICarrierMorphism x z
carrierCompose =
  carrierComposite

physCompose :
  {x y z : PhysFieldObject} →
  PhysFieldMorphism y z →
  PhysFieldMorphism x y →
  PhysFieldMorphism x z
physCompose =
  physComposite

data PrimeBumpRepresentationAction : Set where
  u1YHyperchargePhaseAction :
    PrimeBumpRepresentationAction

  su2LeftRaisingAction :
    PrimeBumpRepresentationAction

  su3ColorCycleAction :
    PrimeBumpRepresentationAction

  su2RightBridgeAction :
    PrimeBumpRepresentationAction

  matterOrTrivialGaugeInertAction :
    PrimeBumpRepresentationAction

data PrimeLaneRepresentationSemantics : Set where
  u1YHyperchargePhaseSemantics :
    PrimeLaneRepresentationSemantics

  su2LeftRaisingSemantics :
    PrimeLaneRepresentationSemantics

  su3ColorCycleSemantics :
    PrimeLaneRepresentationSemantics

  su2RightBridgeSemantics :
    PrimeLaneRepresentationSemantics

  matterOrTrivialGaugeInertSemantics :
    PrimeLaneRepresentationSemantics

primeBumpActionSemantics :
  PrimeBumpRepresentationAction →
  PrimeLaneRepresentationSemantics
primeBumpActionSemantics u1YHyperchargePhaseAction =
  u1YHyperchargePhaseSemantics
primeBumpActionSemantics su2LeftRaisingAction =
  su2LeftRaisingSemantics
primeBumpActionSemantics su3ColorCycleAction =
  su3ColorCycleSemantics
primeBumpActionSemantics su2RightBridgeAction =
  su2RightBridgeSemantics
primeBumpActionSemantics matterOrTrivialGaugeInertAction =
  matterOrTrivialGaugeInertSemantics

primeBumpRepresentationActionMap :
  Moonshine.MonsterPrimeLane →
  PrimeBumpRepresentationAction
primeBumpRepresentationActionMap Moonshine.p2 =
  u1YHyperchargePhaseAction
primeBumpRepresentationActionMap Moonshine.p3 =
  su2LeftRaisingAction
primeBumpRepresentationActionMap Moonshine.p5 =
  su3ColorCycleAction
primeBumpRepresentationActionMap Moonshine.p7 =
  su2RightBridgeAction
primeBumpRepresentationActionMap Moonshine.p11 =
  matterOrTrivialGaugeInertAction
primeBumpRepresentationActionMap Moonshine.p13 =
  matterOrTrivialGaugeInertAction
primeBumpRepresentationActionMap Moonshine.p17 =
  matterOrTrivialGaugeInertAction
primeBumpRepresentationActionMap Moonshine.p19 =
  matterOrTrivialGaugeInertAction
primeBumpRepresentationActionMap Moonshine.p23 =
  matterOrTrivialGaugeInertAction
primeBumpRepresentationActionMap Moonshine.p29 =
  matterOrTrivialGaugeInertAction
primeBumpRepresentationActionMap Moonshine.p31 =
  matterOrTrivialGaugeInertAction
primeBumpRepresentationActionMap Moonshine.p41 =
  matterOrTrivialGaugeInertAction
primeBumpRepresentationActionMap Moonshine.p47 =
  matterOrTrivialGaugeInertAction
primeBumpRepresentationActionMap Moonshine.p59 =
  matterOrTrivialGaugeInertAction
primeBumpRepresentationActionMap Moonshine.p71 =
  matterOrTrivialGaugeInertAction

primeBumpRepresentationSemanticsMap :
  Moonshine.MonsterPrimeLane →
  PrimeLaneRepresentationSemantics
primeBumpRepresentationSemanticsMap p =
  primeBumpActionSemantics (primeBumpRepresentationActionMap p)

carrierToPhysicsMorphismMap :
  {x y : DASHICarrierObject} →
  DASHICarrierMorphism x y →
  PhysFieldMorphism
    (carrierToPhysicsObjectMap x)
    (carrierToPhysicsObjectMap y)
carrierToPhysicsMorphismMap (carrierIdentity x) =
  physIdentity (carrierToPhysicsObjectMap x)
carrierToPhysicsMorphismMap (primeBumpShift p) =
  gaugeCovariantPrimeShift p
carrierToPhysicsMorphismMap (laneToProductInclusion p) =
  gaugeLaneToProductInclusion p
carrierToPhysicsMorphismMap (depthTransition d) =
  depthFieldTransition d
carrierToPhysicsMorphismMap (carrierComposite g f) =
  physComposite
    (carrierToPhysicsMorphismMap g)
    (carrierToPhysicsMorphismMap f)

carrierToPhysicsPreservesIdentity :
  (x : DASHICarrierObject) →
  carrierToPhysicsMorphismMap (carrierIdentity x)
  ≡
  physIdentity (carrierToPhysicsObjectMap x)
carrierToPhysicsPreservesIdentity x =
  refl

carrierToPhysicsPreservesComposition :
  {x y z : DASHICarrierObject} →
  (f : DASHICarrierMorphism x y) →
  (g : DASHICarrierMorphism y z) →
  carrierToPhysicsMorphismMap (carrierCompose g f)
  ≡
  physCompose
    (carrierToPhysicsMorphismMap g)
    (carrierToPhysicsMorphismMap f)
carrierToPhysicsPreservesComposition f g =
  refl

carrierToPhysicsLaneInclusionNaturality :
  (p : Moonshine.MonsterPrimeLane) →
  carrierToPhysicsMorphismMap (laneToProductInclusion p)
  ≡
  gaugeLaneToProductInclusion p
carrierToPhysicsLaneInclusionNaturality p =
  refl

carrierToPhysicsPrimeBumpNaturality :
  (p : Moonshine.MonsterPrimeLane) →
  carrierToPhysicsMorphismMap (primeBumpShift p)
  ≡
  gaugeCovariantPrimeShift p
carrierToPhysicsPrimeBumpNaturality p =
  refl

carrierToPhysicsDepthTransitionNaturality :
  (d : Nat) →
  carrierToPhysicsMorphismMap (depthTransition d)
  ≡
  depthFieldTransition d
carrierToPhysicsDepthTransitionNaturality d =
  refl

p2ObjectMapsToU1Y :
  carrierToPhysicsObjectMap
    (primeLaneCarrierObject Moonshine.p2)
  ≡
  gaugeLaneRepresentationObject LaneGauge.e8LaneU1Y
p2ObjectMapsToU1Y =
  refl

p3ObjectMapsToSU2L :
  carrierToPhysicsObjectMap
    (primeLaneCarrierObject Moonshine.p3)
  ≡
  gaugeLaneRepresentationObject LaneGauge.e8LaneSU2L
p3ObjectMapsToSU2L =
  refl

p5ObjectMapsToSU3c :
  carrierToPhysicsObjectMap
    (primeLaneCarrierObject Moonshine.p5)
  ≡
  gaugeLaneRepresentationObject LaneGauge.e8LaneSU3c
p5ObjectMapsToSU3c =
  refl

p7ObjectMapsToHighEnergySU2R :
  carrierToPhysicsObjectMap
    (primeLaneCarrierObject Moonshine.p7)
  ≡
  gaugeLaneRepresentationObject LaneGauge.e8LaneSU2RBrokenAtSeesaw
p7ObjectMapsToHighEnergySU2R =
  refl

p2PrimeBumpActionIsU1YHypercharge :
  primeBumpRepresentationActionMap Moonshine.p2
  ≡
  u1YHyperchargePhaseAction
p2PrimeBumpActionIsU1YHypercharge =
  refl

p3PrimeBumpActionIsSU2LeftRaising :
  primeBumpRepresentationActionMap Moonshine.p3
  ≡
  su2LeftRaisingAction
p3PrimeBumpActionIsSU2LeftRaising =
  refl

p5PrimeBumpActionIsSU3ColorCycle :
  primeBumpRepresentationActionMap Moonshine.p5
  ≡
  su3ColorCycleAction
p5PrimeBumpActionIsSU3ColorCycle =
  refl

p7PrimeBumpActionIsSU2RightBridge :
  primeBumpRepresentationActionMap Moonshine.p7
  ≡
  su2RightBridgeAction
p7PrimeBumpActionIsSU2RightBridge =
  refl

p2PrimeBumpSemanticsIsU1YHypercharge :
  primeBumpRepresentationSemanticsMap Moonshine.p2
  ≡
  u1YHyperchargePhaseSemantics
p2PrimeBumpSemanticsIsU1YHypercharge =
  refl

p3PrimeBumpSemanticsIsSU2LeftRaising :
  primeBumpRepresentationSemanticsMap Moonshine.p3
  ≡
  su2LeftRaisingSemantics
p3PrimeBumpSemanticsIsSU2LeftRaising =
  refl

p5PrimeBumpSemanticsIsSU3ColorCycle :
  primeBumpRepresentationSemanticsMap Moonshine.p5
  ≡
  su3ColorCycleSemantics
p5PrimeBumpSemanticsIsSU3ColorCycle =
  refl

p7PrimeBumpSemanticsIsSU2RightBridge :
  primeBumpRepresentationSemanticsMap Moonshine.p7
  ≡
  su2RightBridgeSemantics
p7PrimeBumpSemanticsIsSU2RightBridge =
  refl

pAtLeast11ObjectMapsToMatterOrTrivialGauge :
  (p : Moonshine.MonsterPrimeLane) →
  FractranLane.MonsterPrimeLaneAtLeast11 p →
  carrierToPhysicsObjectMap
    (primeLaneCarrierObject p)
  ≡
  gaugeLaneRepresentationObject LaneGauge.e8LaneMatterOrTrivialGauge
pAtLeast11ObjectMapsToMatterOrTrivialGauge
  Moonshine.p11
  FractranLane.p11AtLeast11 =
  refl
pAtLeast11ObjectMapsToMatterOrTrivialGauge
  Moonshine.p13
  FractranLane.p13AtLeast11 =
  refl
pAtLeast11ObjectMapsToMatterOrTrivialGauge
  Moonshine.p17
  FractranLane.p17AtLeast11 =
  refl
pAtLeast11ObjectMapsToMatterOrTrivialGauge
  Moonshine.p19
  FractranLane.p19AtLeast11 =
  refl
pAtLeast11ObjectMapsToMatterOrTrivialGauge
  Moonshine.p23
  FractranLane.p23AtLeast11 =
  refl
pAtLeast11ObjectMapsToMatterOrTrivialGauge
  Moonshine.p29
  FractranLane.p29AtLeast11 =
  refl
pAtLeast11ObjectMapsToMatterOrTrivialGauge
  Moonshine.p31
  FractranLane.p31AtLeast11 =
  refl
pAtLeast11ObjectMapsToMatterOrTrivialGauge
  Moonshine.p41
  FractranLane.p41AtLeast11 =
  refl
pAtLeast11ObjectMapsToMatterOrTrivialGauge
  Moonshine.p47
  FractranLane.p47AtLeast11 =
  refl
pAtLeast11ObjectMapsToMatterOrTrivialGauge
  Moonshine.p59
  FractranLane.p59AtLeast11 =
  refl
pAtLeast11ObjectMapsToMatterOrTrivialGauge
  Moonshine.p71
  FractranLane.p71AtLeast11 =
  refl

pAtLeast11PrimeBumpActionIsMatterOrTrivialGauge :
  (p : Moonshine.MonsterPrimeLane) →
  FractranLane.MonsterPrimeLaneAtLeast11 p →
  primeBumpRepresentationActionMap p
  ≡
  matterOrTrivialGaugeInertAction
pAtLeast11PrimeBumpActionIsMatterOrTrivialGauge
  Moonshine.p11
  FractranLane.p11AtLeast11 =
  refl
pAtLeast11PrimeBumpActionIsMatterOrTrivialGauge
  Moonshine.p13
  FractranLane.p13AtLeast11 =
  refl
pAtLeast11PrimeBumpActionIsMatterOrTrivialGauge
  Moonshine.p17
  FractranLane.p17AtLeast11 =
  refl
pAtLeast11PrimeBumpActionIsMatterOrTrivialGauge
  Moonshine.p19
  FractranLane.p19AtLeast11 =
  refl
pAtLeast11PrimeBumpActionIsMatterOrTrivialGauge
  Moonshine.p23
  FractranLane.p23AtLeast11 =
  refl
pAtLeast11PrimeBumpActionIsMatterOrTrivialGauge
  Moonshine.p29
  FractranLane.p29AtLeast11 =
  refl
pAtLeast11PrimeBumpActionIsMatterOrTrivialGauge
  Moonshine.p31
  FractranLane.p31AtLeast11 =
  refl
pAtLeast11PrimeBumpActionIsMatterOrTrivialGauge
  Moonshine.p41
  FractranLane.p41AtLeast11 =
  refl
pAtLeast11PrimeBumpActionIsMatterOrTrivialGauge
  Moonshine.p47
  FractranLane.p47AtLeast11 =
  refl
pAtLeast11PrimeBumpActionIsMatterOrTrivialGauge
  Moonshine.p59
  FractranLane.p59AtLeast11 =
  refl
pAtLeast11PrimeBumpActionIsMatterOrTrivialGauge
  Moonshine.p71
  FractranLane.p71AtLeast11 =
  refl

pAtLeast11PrimeBumpSemanticsIsMatterOrTrivialGauge :
  (p : Moonshine.MonsterPrimeLane) →
  FractranLane.MonsterPrimeLaneAtLeast11 p →
  primeBumpRepresentationSemanticsMap p
  ≡
  matterOrTrivialGaugeInertSemantics
pAtLeast11PrimeBumpSemanticsIsMatterOrTrivialGauge
  Moonshine.p11
  FractranLane.p11AtLeast11 =
  refl
pAtLeast11PrimeBumpSemanticsIsMatterOrTrivialGauge
  Moonshine.p13
  FractranLane.p13AtLeast11 =
  refl
pAtLeast11PrimeBumpSemanticsIsMatterOrTrivialGauge
  Moonshine.p17
  FractranLane.p17AtLeast11 =
  refl
pAtLeast11PrimeBumpSemanticsIsMatterOrTrivialGauge
  Moonshine.p19
  FractranLane.p19AtLeast11 =
  refl
pAtLeast11PrimeBumpSemanticsIsMatterOrTrivialGauge
  Moonshine.p23
  FractranLane.p23AtLeast11 =
  refl
pAtLeast11PrimeBumpSemanticsIsMatterOrTrivialGauge
  Moonshine.p29
  FractranLane.p29AtLeast11 =
  refl
pAtLeast11PrimeBumpSemanticsIsMatterOrTrivialGauge
  Moonshine.p31
  FractranLane.p31AtLeast11 =
  refl
pAtLeast11PrimeBumpSemanticsIsMatterOrTrivialGauge
  Moonshine.p41
  FractranLane.p41AtLeast11 =
  refl
pAtLeast11PrimeBumpSemanticsIsMatterOrTrivialGauge
  Moonshine.p47
  FractranLane.p47AtLeast11 =
  refl
pAtLeast11PrimeBumpSemanticsIsMatterOrTrivialGauge
  Moonshine.p59
  FractranLane.p59AtLeast11 =
  refl
pAtLeast11PrimeBumpSemanticsIsMatterOrTrivialGauge
  Moonshine.p71
  FractranLane.p71AtLeast11 =
  refl

record CarrierToPhysicsPrimeLaneStructureWitness
  (p : Moonshine.MonsterPrimeLane)
  (gaugeFactor : LaneGauge.E8McKayLaneGaugeFactor) :
  Set where
  field
    objectPreserved :
      carrierToPhysicsObjectMap (primeLaneCarrierObject p)
      ≡
      gaugeLaneRepresentationObject gaugeFactor

    laneInclusionNaturality :
      carrierToPhysicsMorphismMap (laneToProductInclusion p)
      ≡
      gaugeLaneToProductInclusion p

    primeBumpNaturality :
      carrierToPhysicsMorphismMap (primeBumpShift p)
      ≡
      gaugeCovariantPrimeShift p

open CarrierToPhysicsPrimeLaneStructureWitness public

p2CarrierToU1YStructureWitness :
  CarrierToPhysicsPrimeLaneStructureWitness
    Moonshine.p2
    LaneGauge.e8LaneU1Y
p2CarrierToU1YStructureWitness =
  record
    { objectPreserved =
        refl
    ; laneInclusionNaturality =
        carrierToPhysicsLaneInclusionNaturality Moonshine.p2
    ; primeBumpNaturality =
        carrierToPhysicsPrimeBumpNaturality Moonshine.p2
    }

p3CarrierToSU2LStructureWitness :
  CarrierToPhysicsPrimeLaneStructureWitness
    Moonshine.p3
    LaneGauge.e8LaneSU2L
p3CarrierToSU2LStructureWitness =
  record
    { objectPreserved =
        refl
    ; laneInclusionNaturality =
        carrierToPhysicsLaneInclusionNaturality Moonshine.p3
    ; primeBumpNaturality =
        carrierToPhysicsPrimeBumpNaturality Moonshine.p3
    }

p5CarrierToSU3cStructureWitness :
  CarrierToPhysicsPrimeLaneStructureWitness
    Moonshine.p5
    LaneGauge.e8LaneSU3c
p5CarrierToSU3cStructureWitness =
  record
    { objectPreserved =
        refl
    ; laneInclusionNaturality =
        carrierToPhysicsLaneInclusionNaturality Moonshine.p5
    ; primeBumpNaturality =
        carrierToPhysicsPrimeBumpNaturality Moonshine.p5
    }

p7CarrierToHighEnergySU2RStructureWitness :
  CarrierToPhysicsPrimeLaneStructureWitness
    Moonshine.p7
    LaneGauge.e8LaneSU2RBrokenAtSeesaw
p7CarrierToHighEnergySU2RStructureWitness =
  record
    { objectPreserved =
        refl
    ; laneInclusionNaturality =
        carrierToPhysicsLaneInclusionNaturality Moonshine.p7
    ; primeBumpNaturality =
        carrierToPhysicsPrimeBumpNaturality Moonshine.p7
    }

record CarrierToPhysicsGraphFunctor : Setω where
  field
    objectMapIsCanonical :
      carrierToPhysicsObjectMap ≡ carrierToPhysicsObjectMap

    morphismMap :
      {x y : DASHICarrierObject} →
      DASHICarrierMorphism x y →
      PhysFieldMorphism
        (carrierToPhysicsObjectMap x)
        (carrierToPhysicsObjectMap y)

    identityPreserved :
      (x : DASHICarrierObject) →
      morphismMap (carrierIdentity x)
      ≡
      physIdentity (carrierToPhysicsObjectMap x)

    compositionPreserved :
      {x y z : DASHICarrierObject} →
      (f : DASHICarrierMorphism x y) →
      (g : DASHICarrierMorphism y z) →
      morphismMap (carrierCompose g f)
      ≡
      physCompose (morphismMap g) (morphismMap f)

    p2IsU1Y :
      carrierToPhysicsObjectMap (primeLaneCarrierObject Moonshine.p2)
      ≡
      gaugeLaneRepresentationObject LaneGauge.e8LaneU1Y

    p3IsSU2L :
      carrierToPhysicsObjectMap (primeLaneCarrierObject Moonshine.p3)
      ≡
      gaugeLaneRepresentationObject LaneGauge.e8LaneSU2L

    p5IsSU3c :
      carrierToPhysicsObjectMap (primeLaneCarrierObject Moonshine.p5)
      ≡
      gaugeLaneRepresentationObject LaneGauge.e8LaneSU3c

    p7IsHighEnergySU2R :
      carrierToPhysicsObjectMap (primeLaneCarrierObject Moonshine.p7)
      ≡
      gaugeLaneRepresentationObject LaneGauge.e8LaneSU2RBrokenAtSeesaw

    pAtLeast11IsMatterOrTrivialGauge :
      (p : Moonshine.MonsterPrimeLane) →
      FractranLane.MonsterPrimeLaneAtLeast11 p →
      carrierToPhysicsObjectMap (primeLaneCarrierObject p)
      ≡
      gaugeLaneRepresentationObject LaneGauge.e8LaneMatterOrTrivialGauge

    p2PrimeBumpMapsToU1YShift :
      morphismMap (primeBumpShift Moonshine.p2)
      ≡
      gaugeCovariantPrimeShift Moonshine.p2

    p3PrimeBumpMapsToSU2LShift :
      morphismMap (primeBumpShift Moonshine.p3)
      ≡
      gaugeCovariantPrimeShift Moonshine.p3

    p5PrimeBumpMapsToSU3cShift :
      morphismMap (primeBumpShift Moonshine.p5)
      ≡
      gaugeCovariantPrimeShift Moonshine.p5

    p7PrimeBumpMapsToHighEnergySU2RShift :
      morphismMap (primeBumpShift Moonshine.p7)
      ≡
      gaugeCovariantPrimeShift Moonshine.p7

    p2StructurePreservationNaturality :
      CarrierToPhysicsPrimeLaneStructureWitness
        Moonshine.p2
        LaneGauge.e8LaneU1Y

    p3StructurePreservationNaturality :
      CarrierToPhysicsPrimeLaneStructureWitness
        Moonshine.p3
        LaneGauge.e8LaneSU2L

    p5StructurePreservationNaturality :
      CarrierToPhysicsPrimeLaneStructureWitness
        Moonshine.p5
        LaneGauge.e8LaneSU3c

    p7StructurePreservationNaturality :
      CarrierToPhysicsPrimeLaneStructureWitness
        Moonshine.p7
        LaneGauge.e8LaneSU2RBrokenAtSeesaw

open CarrierToPhysicsGraphFunctor public

canonicalCarrierToPhysicsGraphFunctor :
  CarrierToPhysicsGraphFunctor
canonicalCarrierToPhysicsGraphFunctor =
  record
    { objectMapIsCanonical =
        refl
    ; morphismMap =
        carrierToPhysicsMorphismMap
    ; identityPreserved =
        carrierToPhysicsPreservesIdentity
    ; compositionPreserved =
        carrierToPhysicsPreservesComposition
    ; p2IsU1Y =
        refl
    ; p3IsSU2L =
        refl
    ; p5IsSU3c =
        refl
    ; p7IsHighEnergySU2R =
        refl
    ; pAtLeast11IsMatterOrTrivialGauge =
        pAtLeast11ObjectMapsToMatterOrTrivialGauge
    ; p2PrimeBumpMapsToU1YShift =
        carrierToPhysicsPrimeBumpNaturality Moonshine.p2
    ; p3PrimeBumpMapsToSU2LShift =
        carrierToPhysicsPrimeBumpNaturality Moonshine.p3
    ; p5PrimeBumpMapsToSU3cShift =
        carrierToPhysicsPrimeBumpNaturality Moonshine.p5
    ; p7PrimeBumpMapsToHighEnergySU2RShift =
        carrierToPhysicsPrimeBumpNaturality Moonshine.p7
    ; p2StructurePreservationNaturality =
        p2CarrierToU1YStructureWitness
    ; p3StructurePreservationNaturality =
        p3CarrierToSU2LStructureWitness
    ; p5StructurePreservationNaturality =
        p5CarrierToSU3cStructureWitness
    ; p7StructurePreservationNaturality =
        p7CarrierToHighEnergySU2RStructureWitness
    }

data CarrierToPhysicsRemainingPrimitive : Set where
  missingFilteredColimitPreservation :
    CarrierToPhysicsRemainingPrimitive

  missingDHRSectorCompatibility :
    CarrierToPhysicsRemainingPrimitive

canonicalCarrierToPhysicsRemainingPrimitives :
  List CarrierToPhysicsRemainingPrimitive
canonicalCarrierToPhysicsRemainingPrimitives =
  missingFilteredColimitPreservation
  ∷ missingDHRSectorCompatibility
  ∷ []

record CarrierToPhysicsMissingPrimitiveWitness
  (missingPrimitive : CarrierToPhysicsRemainingPrimitive) :
  Set where
  field
    requestedPrimitive :
      CarrierToPhysicsRemainingPrimitive

    requestedPrimitiveIsCanonical :
      requestedPrimitive ≡ missingPrimitive

    semanticProofPromoted :
      Bool

    semanticProofPromotedIsFalse :
      semanticProofPromoted ≡ false

    boundary :
      String

open CarrierToPhysicsMissingPrimitiveWitness public

missingFiniteSupportFilteredColimitPrimitiveWitness :
  CarrierToPhysicsMissingPrimitiveWitness
    missingFilteredColimitPreservation
missingFiniteSupportFilteredColimitPrimitiveWitness =
  record
    { requestedPrimitive =
        missingFilteredColimitPreservation
    ; requestedPrimitiveIsCanonical =
        refl
    ; semanticProofPromoted =
        false
    ; semanticProofPromotedIsFalse =
        refl
    ; boundary =
        "filtered-colimit preservation is recorded only as missingFiniteSupportFilteredColimitPrimitiveWitness; filteredColimitPreservationPromoted remains false"
    }

missingDHRSectorCompatibilityPrimitiveWitness :
  CarrierToPhysicsMissingPrimitiveWitness
    missingDHRSectorCompatibility
missingDHRSectorCompatibilityPrimitiveWitness =
  record
    { requestedPrimitive =
        missingDHRSectorCompatibility
    ; requestedPrimitiveIsCanonical =
        refl
    ; semanticProofPromoted =
        false
    ; semanticProofPromotedIsFalse =
        refl
    ; boundary =
        "DHR-sector compatibility is recorded only as a missing semantic sector-compatibility theorem"
    }

data FiniteSupportCarrierBoundary : Set where
  finiteSupportBoundaryRecordedOnly :
    FiniteSupportCarrierBoundary

data DHRSectorBoundary : Set where
  dhrSectorBoundaryRecordedOnly :
    DHRSectorBoundary

record PrimeLaneRepresentationSemanticsReceipt : Setω where
  field
    chosenPrimeBumpSemantics :
      Moonshine.MonsterPrimeLane →
      PrimeLaneRepresentationSemantics

    chosenSemanticsMapIsCanonical :
      chosenPrimeBumpSemantics ≡ primeBumpRepresentationSemanticsMap

    semanticsRefinesActionMap :
      (p : Moonshine.MonsterPrimeLane) →
      chosenPrimeBumpSemantics p
      ≡
      primeBumpActionSemantics (primeBumpRepresentationActionMap p)

    p2Semantics :
      chosenPrimeBumpSemantics Moonshine.p2
      ≡
      u1YHyperchargePhaseSemantics

    p3Semantics :
      chosenPrimeBumpSemantics Moonshine.p3
      ≡
      su2LeftRaisingSemantics

    p5Semantics :
      chosenPrimeBumpSemantics Moonshine.p5
      ≡
      su3ColorCycleSemantics

    p7Semantics :
      chosenPrimeBumpSemantics Moonshine.p7
      ≡
      su2RightBridgeSemantics

    pAtLeast11Semantics :
      (p : Moonshine.MonsterPrimeLane) →
      FractranLane.MonsterPrimeLaneAtLeast11 p →
      chosenPrimeBumpSemantics p
      ≡
      matterOrTrivialGaugeInertSemantics

open PrimeLaneRepresentationSemanticsReceipt public

canonicalPrimeLaneRepresentationSemanticsReceipt :
  PrimeLaneRepresentationSemanticsReceipt
canonicalPrimeLaneRepresentationSemanticsReceipt =
  record
    { chosenPrimeBumpSemantics =
        primeBumpRepresentationSemanticsMap
    ; chosenSemanticsMapIsCanonical =
        refl
    ; semanticsRefinesActionMap =
        λ p → refl
    ; p2Semantics =
        refl
    ; p3Semantics =
        refl
    ; p5Semantics =
        refl
    ; p7Semantics =
        refl
    ; pAtLeast11Semantics =
        pAtLeast11PrimeBumpSemanticsIsMatterOrTrivialGauge
    }

record RepresentationSemanticsActionTargetReceipt : Setω where
  field
    actionMapCommitted :
      Bool

    actionMapCommittedIsTrue :
      actionMapCommitted ≡ true

    chosenPrimeBumpAction :
      Moonshine.MonsterPrimeLane →
      PrimeBumpRepresentationAction

    chosenActionMapIsCanonical :
      chosenPrimeBumpAction ≡ primeBumpRepresentationActionMap

    p2Action :
      chosenPrimeBumpAction Moonshine.p2
      ≡
      u1YHyperchargePhaseAction

    p3Action :
      chosenPrimeBumpAction Moonshine.p3
      ≡
      su2LeftRaisingAction

    p5Action :
      chosenPrimeBumpAction Moonshine.p5
      ≡
      su3ColorCycleAction

    p7Action :
      chosenPrimeBumpAction Moonshine.p7
      ≡
      su2RightBridgeAction

    pAtLeast11Action :
      (p : Moonshine.MonsterPrimeLane) →
      FractranLane.MonsterPrimeLaneAtLeast11 p →
      chosenPrimeBumpAction p
      ≡
      matterOrTrivialGaugeInertAction

    typedRepresentationSemantics :
      PrimeLaneRepresentationSemanticsReceipt

    semanticRepresentationDischarged :
      Bool

    semanticRepresentationDischargedIsTrue :
      semanticRepresentationDischarged ≡ true

open RepresentationSemanticsActionTargetReceipt public

canonicalRepresentationSemanticsActionTargetReceipt :
  RepresentationSemanticsActionTargetReceipt
canonicalRepresentationSemanticsActionTargetReceipt =
  record
    { actionMapCommitted =
        true
    ; actionMapCommittedIsTrue =
        refl
    ; chosenPrimeBumpAction =
        primeBumpRepresentationActionMap
    ; chosenActionMapIsCanonical =
        refl
    ; p2Action =
        refl
    ; p3Action =
        refl
    ; p5Action =
        refl
    ; p7Action =
        refl
    ; pAtLeast11Action =
        pAtLeast11PrimeBumpActionIsMatterOrTrivialGauge
    ; typedRepresentationSemantics =
        canonicalPrimeLaneRepresentationSemanticsReceipt
    ; semanticRepresentationDischarged =
        true
    ; semanticRepresentationDischargedIsTrue =
        refl
    }

monsterPrimeLaneToSSP :
  Moonshine.MonsterPrimeLane →
  SSP
monsterPrimeLaneToSSP Moonshine.p2 =
  p2
monsterPrimeLaneToSSP Moonshine.p3 =
  p3
monsterPrimeLaneToSSP Moonshine.p5 =
  p5
monsterPrimeLaneToSSP Moonshine.p7 =
  p7
monsterPrimeLaneToSSP Moonshine.p11 =
  p11
monsterPrimeLaneToSSP Moonshine.p13 =
  p13
monsterPrimeLaneToSSP Moonshine.p17 =
  p17
monsterPrimeLaneToSSP Moonshine.p19 =
  p19
monsterPrimeLaneToSSP Moonshine.p23 =
  p23
monsterPrimeLaneToSSP Moonshine.p29 =
  p29
monsterPrimeLaneToSSP Moonshine.p31 =
  p31
monsterPrimeLaneToSSP Moonshine.p41 =
  p41
monsterPrimeLaneToSSP Moonshine.p47 =
  p47
monsterPrimeLaneToSSP Moonshine.p59 =
  p59
monsterPrimeLaneToSSP Moonshine.p71 =
  p71

primeBumpCovarianceFromPrimeBumpCommutes :
  (p q : Moonshine.MonsterPrimeLane) →
  (carrier : GL.FactorVec) →
  FVI.primeBump
    (monsterPrimeLaneToSSP p)
    (FVI.primeBump (monsterPrimeLaneToSSP q) carrier)
  ≡
  FVI.primeBump
    (monsterPrimeLaneToSSP q)
    (FVI.primeBump (monsterPrimeLaneToSSP p) carrier)
primeBumpCovarianceFromPrimeBumpCommutes p q carrier =
  FVI.primeBumpCommutes
    (monsterPrimeLaneToSSP p)
    (monsterPrimeLaneToSSP q)
    carrier

record PrimeBumpCovarianceSemanticsReceipt : Setω where
  field
    primeLaneInterpretation :
      Moonshine.MonsterPrimeLane →
      SSP

    primeLaneInterpretationIsCanonical :
      primeLaneInterpretation ≡ monsterPrimeLaneToSSP

    commutationOnPrimeBumpCarrier :
      (p q : Moonshine.MonsterPrimeLane) →
      (carrier : GL.FactorVec) →
      FVI.primeBump
        (primeLaneInterpretation p)
        (FVI.primeBump (primeLaneInterpretation q) carrier)
      ≡
      FVI.primeBump
        (primeLaneInterpretation q)
        (FVI.primeBump (primeLaneInterpretation p) carrier)

open PrimeBumpCovarianceSemanticsReceipt public

canonicalPrimeBumpCovarianceSemanticsReceipt :
  PrimeBumpCovarianceSemanticsReceipt
canonicalPrimeBumpCovarianceSemanticsReceipt =
  record
    { primeLaneInterpretation =
        monsterPrimeLaneToSSP
    ; primeLaneInterpretationIsCanonical =
        refl
    ; commutationOnPrimeBumpCarrier =
        primeBumpCovarianceFromPrimeBumpCommutes
    }

record PrimeBumpCovarianceLawReceipt : Setω where
  field
    graphMorphismAssignmentCommitted :
      Bool

    graphMorphismAssignmentCommittedIsTrue :
      graphMorphismAssignmentCommitted ≡ true

    mappedPrimeBumpIsNamedCovariantShift :
      (p : Moonshine.MonsterPrimeLane) →
      carrierToPhysicsMorphismMap (primeBumpShift p)
      ≡
      gaugeCovariantPrimeShift p

    semanticCovarianceProof :
      PrimeBumpCovarianceSemanticsReceipt

open PrimeBumpCovarianceLawReceipt public

canonicalPrimeBumpCovarianceLawReceipt :
  PrimeBumpCovarianceLawReceipt
canonicalPrimeBumpCovarianceLawReceipt =
  record
    { graphMorphismAssignmentCommitted =
        true
    ; graphMorphismAssignmentCommittedIsTrue =
        refl
    ; mappedPrimeBumpIsNamedCovariantShift =
        carrierToPhysicsPrimeBumpNaturality
    ; semanticCovarianceProof =
        canonicalPrimeBumpCovarianceSemanticsReceipt
    }

record DepthTransitionNaturalityLawReceipt : Setω where
  field
    graphMorphismAssignmentCommitted :
      Bool

    graphMorphismAssignmentCommittedIsTrue :
      graphMorphismAssignmentCommitted ≡ true

    mappedDepthTransitionIsNamedFieldTransition :
      (d : Nat) →
      carrierToPhysicsMorphismMap (depthTransition d)
      ≡
      depthFieldTransition d

    semanticNaturalityProof :
      (d : Nat) →
      carrierToPhysicsMorphismMap (depthTransition d)
      ≡
      depthFieldTransition d

open DepthTransitionNaturalityLawReceipt public

canonicalDepthTransitionNaturalityLawReceipt :
  DepthTransitionNaturalityLawReceipt
canonicalDepthTransitionNaturalityLawReceipt =
  record
    { graphMorphismAssignmentCommitted =
        true
    ; graphMorphismAssignmentCommittedIsTrue =
        refl
    ; mappedDepthTransitionIsNamedFieldTransition =
        carrierToPhysicsDepthTransitionNaturality
    ; semanticNaturalityProof =
        carrierToPhysicsDepthTransitionNaturality
    }

record PrimeBumpCovarianceAndDepthNaturalityReceipt : Setω where
  field
    graphMorphismAssignmentsCommitted :
      Bool

    graphMorphismAssignmentsCommittedIsTrue :
      graphMorphismAssignmentsCommitted ≡ true

    primeBumpCovarianceLawReceipt :
      PrimeBumpCovarianceLawReceipt

    depthTransitionNaturalityLawReceipt :
      DepthTransitionNaturalityLawReceipt

    primeBumpCovarianceDischarged :
      Bool

    primeBumpCovarianceDischargedIsTrue :
      primeBumpCovarianceDischarged ≡ true

    depthTransitionNaturalityDischarged :
      Bool

    depthTransitionNaturalityDischargedIsTrue :
      depthTransitionNaturalityDischarged ≡ true

open PrimeBumpCovarianceAndDepthNaturalityReceipt public

canonicalPrimeBumpCovarianceAndDepthNaturalityReceipt :
  PrimeBumpCovarianceAndDepthNaturalityReceipt
canonicalPrimeBumpCovarianceAndDepthNaturalityReceipt =
  record
    { graphMorphismAssignmentsCommitted =
        true
    ; graphMorphismAssignmentsCommittedIsTrue =
        refl
    ; primeBumpCovarianceLawReceipt =
        canonicalPrimeBumpCovarianceLawReceipt
    ; depthTransitionNaturalityLawReceipt =
        canonicalDepthTransitionNaturalityLawReceipt
    ; primeBumpCovarianceDischarged =
        true
    ; primeBumpCovarianceDischargedIsTrue =
        refl
    ; depthTransitionNaturalityDischarged =
        true
    ; depthTransitionNaturalityDischargedIsTrue =
        refl
    }

record FiniteSupportFilteredColimitLawReceipt : Setω where
  field
    finiteSupportBoundary :
      FiniteSupportCarrierBoundary

    finiteSupportBoundaryIsRecordedOnly :
      finiteSupportBoundary ≡ finiteSupportBoundaryRecordedOnly

    objectAndMorphismAssignmentAvailable :
      Bool

    objectAndMorphismAssignmentAvailableIsTrue :
      objectAndMorphismAssignmentAvailable ≡ true

    preservationProof :
      CarrierToPhysicsMissingPrimitiveWitness
        missingFilteredColimitPreservation

open FiniteSupportFilteredColimitLawReceipt public

canonicalFiniteSupportFilteredColimitLawReceipt :
  FiniteSupportFilteredColimitLawReceipt
canonicalFiniteSupportFilteredColimitLawReceipt =
  record
    { finiteSupportBoundary =
        finiteSupportBoundaryRecordedOnly
    ; finiteSupportBoundaryIsRecordedOnly =
        refl
    ; objectAndMorphismAssignmentAvailable =
        true
    ; objectAndMorphismAssignmentAvailableIsTrue =
        refl
    ; preservationProof =
        missingFiniteSupportFilteredColimitPrimitiveWitness
    }

record DHRSectorCompatibilityLawReceipt : Setω where
  field
    dhrSectorBoundary :
      DHRSectorBoundary

    dhrSectorBoundaryIsRecordedOnly :
      dhrSectorBoundary ≡ dhrSectorBoundaryRecordedOnly

    primeLaneObjectAssignmentAvailable :
      Bool

    primeLaneObjectAssignmentAvailableIsTrue :
      primeLaneObjectAssignmentAvailable ≡ true

    dhrCompatibilityProof :
      CarrierToPhysicsMissingPrimitiveWitness
        missingDHRSectorCompatibility

open DHRSectorCompatibilityLawReceipt public

canonicalDHRSectorCompatibilityLawReceipt :
  DHRSectorCompatibilityLawReceipt
canonicalDHRSectorCompatibilityLawReceipt =
  record
    { dhrSectorBoundary =
        dhrSectorBoundaryRecordedOnly
    ; dhrSectorBoundaryIsRecordedOnly =
        refl
    ; primeLaneObjectAssignmentAvailable =
        true
    ; primeLaneObjectAssignmentAvailableIsTrue =
        refl
    ; dhrCompatibilityProof =
        missingDHRSectorCompatibilityPrimitiveWitness
    }

record CarrierToPhysicsFunctorLawReceiptSurface : Setω where
  field
    representationSemanticsActionTarget :
      RepresentationSemanticsActionTargetReceipt

    primeBumpCovariance :
      PrimeBumpCovarianceLawReceipt

    depthTransitionNaturality :
      DepthTransitionNaturalityLawReceipt

    primeBumpCovarianceAndDepthNaturality :
      PrimeBumpCovarianceAndDepthNaturalityReceipt

    filteredColimitPreservationFromFiniteSupport :
      FiniteSupportFilteredColimitLawReceipt

    dhrSectorCompatibility :
      DHRSectorCompatibilityLawReceipt

open CarrierToPhysicsFunctorLawReceiptSurface public

canonicalCarrierToPhysicsFunctorLawReceiptSurface :
  CarrierToPhysicsFunctorLawReceiptSurface
canonicalCarrierToPhysicsFunctorLawReceiptSurface =
  record
    { representationSemanticsActionTarget =
        canonicalRepresentationSemanticsActionTargetReceipt
    ; primeBumpCovariance =
        canonicalPrimeBumpCovarianceLawReceipt
    ; depthTransitionNaturality =
        canonicalDepthTransitionNaturalityLawReceipt
    ; primeBumpCovarianceAndDepthNaturality =
        canonicalPrimeBumpCovarianceAndDepthNaturalityReceipt
    ; filteredColimitPreservationFromFiniteSupport =
        canonicalFiniteSupportFilteredColimitLawReceipt
    ; dhrSectorCompatibility =
        canonicalDHRSectorCompatibilityLawReceipt
    }

record CarrierToPhysicsInterpretationReceipt : Setω where
  field
    status :
      CarrierToPhysicsInterpretationStatus

    graphFunctor :
      CarrierToPhysicsGraphFunctor

    functorLawReceiptSurface :
      CarrierToPhysicsFunctorLawReceiptSurface

    exactStandardModelMatchToken :
      ExactSM.ExactSMMatchReceipt

    primeLaneAssignmentReceiptIsCanonical :
      Bool

    primeLaneAssignmentReceiptIsCanonicalProof :
      primeLaneAssignmentReceiptIsCanonical ≡ true

    objectAssignmentCommitted :
      Bool

    objectAssignmentCommittedIsTrue :
      objectAssignmentCommitted ≡ true

    graphFunctorInhabited :
      Bool

    graphFunctorInhabitedIsTrue :
      graphFunctorInhabited ≡ true

    fullPhysicalFunctorPromoted :
      Bool

    fullPhysicalFunctorPromotedIsFalse :
      fullPhysicalFunctorPromoted ≡ false

    filteredColimitPreservationPromoted :
      Bool

    filteredColimitPreservationPromotedIsFalse :
      filteredColimitPreservationPromoted ≡ false

    reconstructedDHRGaugeGroupClaimed :
      Bool

    reconstructedDHRGaugeGroupClaimedIsFalse :
      reconstructedDHRGaugeGroupClaimed ≡ false

    remainingPrimitives :
      List CarrierToPhysicsRemainingPrimitive

    remainingPrimitivesAreCanonical :
      remainingPrimitives
      ≡
      canonicalCarrierToPhysicsRemainingPrimitives

    noPromotionWithoutAuthority :
      CarrierToPhysicsInterpretationPromotionAuthorityToken →
      ⊥

    boundary :
      List String

open CarrierToPhysicsInterpretationReceipt public

canonicalCarrierToPhysicsInterpretationReceipt :
  CarrierToPhysicsInterpretationReceipt
canonicalCarrierToPhysicsInterpretationReceipt =
  record
    { status =
        graphFunctorCommittedNoFullPhysicsPromotion
    ; graphFunctor =
        canonicalCarrierToPhysicsGraphFunctor
    ; functorLawReceiptSurface =
        canonicalCarrierToPhysicsFunctorLawReceiptSurface
    ; exactStandardModelMatchToken =
        ExactSM.canonicalExactSMMatchReceipt
    ; primeLaneAssignmentReceiptIsCanonical =
        true
    ; primeLaneAssignmentReceiptIsCanonicalProof =
        refl
    ; objectAssignmentCommitted =
        true
    ; objectAssignmentCommittedIsTrue =
        refl
    ; graphFunctorInhabited =
        true
    ; graphFunctorInhabitedIsTrue =
        refl
    ; fullPhysicalFunctorPromoted =
        false
    ; fullPhysicalFunctorPromotedIsFalse =
        refl
    ; filteredColimitPreservationPromoted =
        false
    ; filteredColimitPreservationPromotedIsFalse =
        refl
    ; reconstructedDHRGaugeGroupClaimed =
        false
    ; reconstructedDHRGaugeGroupClaimedIsFalse =
        refl
    ; remainingPrimitives =
        canonicalCarrierToPhysicsRemainingPrimitives
    ; remainingPrimitivesAreCanonical =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "Gate 1 now commits the prime-lane object map: p2->U1Y, p3->SU2L, p5->SU3c, p7->high-energy-SU2R, p>=11->matter-or-trivial-gauge"
        ∷ "The graph-level interpretation object/morphism map is inhabited and preserves identity/composition by reflexivity"
        ∷ "The p2, p3, p5, and p7 lanes carry typed structure-preservation/naturality witnesses for object assignment, lane inclusion, and prime-bump shift"
        ∷ "The prime-bump action target map commits p2->hypercharge phase, p3->SU2L raising, p5->SU3 color cycling, p7->SU2R bridge, and p>=11 inert matter/trivial-gauge action labels"
        ∷ "Prime-lane representation semantics are inhabited with typed p2->U1Y, p3->SU2L, p5->SU3c, and p7->high-energy-SU2R semantics receipts"
        ∷ "Prime-bump covariance is discharged at the semantic receipt surface via prime-bump commutation on the carrier"
        ∷ "Depth-transition naturality is discharged at the semantic receipt surface by the canonical depth-field transition map"
        ∷ "The exact Standard Model match token is imported from the canonical DHR decomposition and W3/M3 plus depth-quotient SU(3) bridge witnesses"
        ∷ "The remaining functor-law receipts now isolate missingFiniteSupportFilteredColimitPrimitiveWitness and missingDHRSectorCompatibilityPrimitiveWitness as the unresolved semantic proofs"
        ∷ "Filtered-colimit preservation is not promoted by this receipt"
        ∷ "DHR reconstruction and G_DHR=G_SM matching remain downstream gates, not consequences of this graph functor alone"
        ∷ []
    }

data ExactStandardModelCarrierFunctorMatchBlocker : Set where
  missingExactStandardModelCarrierFunctorMatch :
    ExactStandardModelCarrierFunctorMatchBlocker

data ExactStandardModelCarrierFunctorMatchDependency : Set where
  dependencyMissingFilteredColimitPreservation :
    ExactStandardModelCarrierFunctorMatchDependency

  dependencyMissingLeftAdjointCarrierPhysicsColimitTheorem :
    ExactStandardModelCarrierFunctorMatchDependency

  dependencyMissingDHRSectorCompatibility :
    ExactStandardModelCarrierFunctorMatchDependency

  dependencyMissingDASHILocalAlgebra :
    ExactStandardModelCarrierFunctorMatchDependency

  dependencyMissingArbitraryDHRSectorSemantics :
    ExactStandardModelCarrierFunctorMatchDependency

  dependencyMissingPrimeLaneQuantumNumbersAPI :
    ExactStandardModelCarrierFunctorMatchDependency

  dependencyMissingGDHRStandardModelIdentification :
    ExactStandardModelCarrierFunctorMatchDependency

canonicalExactStandardModelCarrierFunctorMatchDependencies :
  List ExactStandardModelCarrierFunctorMatchDependency
canonicalExactStandardModelCarrierFunctorMatchDependencies =
  dependencyMissingFilteredColimitPreservation
  ∷ dependencyMissingLeftAdjointCarrierPhysicsColimitTheorem
  ∷ dependencyMissingDHRSectorCompatibility
  ∷ dependencyMissingDASHILocalAlgebra
  ∷ dependencyMissingArbitraryDHRSectorSemantics
  ∷ dependencyMissingPrimeLaneQuantumNumbersAPI
  ∷ dependencyMissingGDHRStandardModelIdentification
  ∷ []

data StandardModelRepresentationTableStatus : Set where
  standardModelRepresentationTableTargetAttemptNoPromotion :
    StandardModelRepresentationTableStatus

data StandardModelRepresentationRowKind : Set where
  quarkRepresentationRow :
    StandardModelRepresentationRowKind

  leptonRepresentationRow :
    StandardModelRepresentationRowKind

  gaugeBosonRepresentationRow :
    StandardModelRepresentationRowKind

data StandardModelGaugeBosonTarget : Set where
  hyperchargeGaugeBosonTarget :
    StandardModelGaugeBosonTarget

  weakGaugeBosonTarget :
    StandardModelGaugeBosonTarget

  gluonGaugeBosonTarget :
    StandardModelGaugeBosonTarget

data OptionalStandardModelMatterSectorTarget : Set where
  noStandardModelMatterSectorTarget :
    OptionalStandardModelMatterSectorTarget

  someStandardModelMatterSectorTarget :
    Matter.StandardModelMatterSectorTarget →
    OptionalStandardModelMatterSectorTarget

data OptionalMatterRepresentation : Set where
  noMatterRepresentation :
    OptionalMatterRepresentation

  someMatterRepresentation :
    Matter.MatterRepresentation →
    OptionalMatterRepresentation

data OptionalStandardModelGaugeBosonTarget : Set where
  noStandardModelGaugeBosonTarget :
    OptionalStandardModelGaugeBosonTarget

  someStandardModelGaugeBosonTarget :
    StandardModelGaugeBosonTarget →
    OptionalStandardModelGaugeBosonTarget

record StandardModelRepresentationTableRow : Set where
  field
    smRowKind :
      StandardModelRepresentationRowKind

    smRowLabel :
      String

    smRowPrimeLane :
      Moonshine.MonsterPrimeLane

    smRowGaugeFactor :
      LaneGauge.E8McKayLaneGaugeFactor

    smRowGaugeFactorMatchesObjectMap :
      carrierToPhysicsObjectMap (primeLaneCarrierObject smRowPrimeLane)
      ≡
      gaugeLaneRepresentationObject smRowGaugeFactor

    smRowMatterSector :
      OptionalStandardModelMatterSectorTarget

    smRowMatterRepresentation :
      OptionalMatterRepresentation

    smRowGaugeBosonTarget :
      OptionalStandardModelGaugeBosonTarget

    smRowTargetOnly :
      Bool

    smRowTargetOnlyIsTrue :
      smRowTargetOnly ≡ true

leftQuarkDoubletSMRepresentationRow :
  StandardModelRepresentationTableRow
leftQuarkDoubletSMRepresentationRow =
  record
    { smRowKind =
        quarkRepresentationRow
    ; smRowLabel =
        "left-quark-doublet-target-row"
    ; smRowPrimeLane =
        Moonshine.p11
    ; smRowGaugeFactor =
        LaneGauge.e8LaneMatterOrTrivialGauge
    ; smRowGaugeFactorMatchesObjectMap =
        refl
    ; smRowMatterSector =
        someStandardModelMatterSectorTarget Matter.leftQuarkDoubletTarget
    ; smRowMatterRepresentation =
        someMatterRepresentation
          Matter.canonicalLeftQuarkDoubletFamilyMatterRepresentation
    ; smRowGaugeBosonTarget =
        noStandardModelGaugeBosonTarget
    ; smRowTargetOnly =
        true
    ; smRowTargetOnlyIsTrue =
        refl
    }

rightUpQuarkSMRepresentationRow :
  StandardModelRepresentationTableRow
rightUpQuarkSMRepresentationRow =
  record
    { smRowKind =
        quarkRepresentationRow
    ; smRowLabel =
        "right-up-quark-target-row"
    ; smRowPrimeLane =
        Moonshine.p13
    ; smRowGaugeFactor =
        LaneGauge.e8LaneMatterOrTrivialGauge
    ; smRowGaugeFactorMatchesObjectMap =
        refl
    ; smRowMatterSector =
        someStandardModelMatterSectorTarget Matter.rightUpQuarkTarget
    ; smRowMatterRepresentation =
        someMatterRepresentation
          Matter.canonicalRightUpQuarkFamilyMatterRepresentation
    ; smRowGaugeBosonTarget =
        noStandardModelGaugeBosonTarget
    ; smRowTargetOnly =
        true
    ; smRowTargetOnlyIsTrue =
        refl
    }

rightDownQuarkSMRepresentationRow :
  StandardModelRepresentationTableRow
rightDownQuarkSMRepresentationRow =
  record
    { smRowKind =
        quarkRepresentationRow
    ; smRowLabel =
        "right-down-quark-target-row"
    ; smRowPrimeLane =
        Moonshine.p17
    ; smRowGaugeFactor =
        LaneGauge.e8LaneMatterOrTrivialGauge
    ; smRowGaugeFactorMatchesObjectMap =
        refl
    ; smRowMatterSector =
        someStandardModelMatterSectorTarget Matter.rightDownQuarkTarget
    ; smRowMatterRepresentation =
        someMatterRepresentation
          Matter.canonicalRightDownQuarkFamilyMatterRepresentation
    ; smRowGaugeBosonTarget =
        noStandardModelGaugeBosonTarget
    ; smRowTargetOnly =
        true
    ; smRowTargetOnlyIsTrue =
        refl
    }

leftLeptonDoubletSMRepresentationRow :
  StandardModelRepresentationTableRow
leftLeptonDoubletSMRepresentationRow =
  record
    { smRowKind =
        leptonRepresentationRow
    ; smRowLabel =
        "left-lepton-doublet-target-row"
    ; smRowPrimeLane =
        Moonshine.p19
    ; smRowGaugeFactor =
        LaneGauge.e8LaneMatterOrTrivialGauge
    ; smRowGaugeFactorMatchesObjectMap =
        refl
    ; smRowMatterSector =
        someStandardModelMatterSectorTarget Matter.leftLeptonDoubletTarget
    ; smRowMatterRepresentation =
        someMatterRepresentation
          Matter.canonicalLeftLeptonDoubletFamilyMatterRepresentation
    ; smRowGaugeBosonTarget =
        noStandardModelGaugeBosonTarget
    ; smRowTargetOnly =
        true
    ; smRowTargetOnlyIsTrue =
        refl
    }

rightChargedLeptonSMRepresentationRow :
  StandardModelRepresentationTableRow
rightChargedLeptonSMRepresentationRow =
  record
    { smRowKind =
        leptonRepresentationRow
    ; smRowLabel =
        "right-charged-lepton-target-row"
    ; smRowPrimeLane =
        Moonshine.p23
    ; smRowGaugeFactor =
        LaneGauge.e8LaneMatterOrTrivialGauge
    ; smRowGaugeFactorMatchesObjectMap =
        refl
    ; smRowMatterSector =
        someStandardModelMatterSectorTarget Matter.rightChargedLeptonTarget
    ; smRowMatterRepresentation =
        someMatterRepresentation
          Matter.canonicalRightChargedLeptonFamilyMatterRepresentation
    ; smRowGaugeBosonTarget =
        noStandardModelGaugeBosonTarget
    ; smRowTargetOnly =
        true
    ; smRowTargetOnlyIsTrue =
        refl
    }

hyperchargeGaugeBosonSMRepresentationRow :
  StandardModelRepresentationTableRow
hyperchargeGaugeBosonSMRepresentationRow =
  record
    { smRowKind =
        gaugeBosonRepresentationRow
    ; smRowLabel =
        "hypercharge-gauge-boson-target-row"
    ; smRowPrimeLane =
        Moonshine.p2
    ; smRowGaugeFactor =
        LaneGauge.e8LaneU1Y
    ; smRowGaugeFactorMatchesObjectMap =
        refl
    ; smRowMatterSector =
        noStandardModelMatterSectorTarget
    ; smRowMatterRepresentation =
        noMatterRepresentation
    ; smRowGaugeBosonTarget =
        someStandardModelGaugeBosonTarget hyperchargeGaugeBosonTarget
    ; smRowTargetOnly =
        true
    ; smRowTargetOnlyIsTrue =
        refl
    }

weakGaugeBosonSMRepresentationRow :
  StandardModelRepresentationTableRow
weakGaugeBosonSMRepresentationRow =
  record
    { smRowKind =
        gaugeBosonRepresentationRow
    ; smRowLabel =
        "weak-gauge-boson-target-row"
    ; smRowPrimeLane =
        Moonshine.p3
    ; smRowGaugeFactor =
        LaneGauge.e8LaneSU2L
    ; smRowGaugeFactorMatchesObjectMap =
        refl
    ; smRowMatterSector =
        noStandardModelMatterSectorTarget
    ; smRowMatterRepresentation =
        noMatterRepresentation
    ; smRowGaugeBosonTarget =
        someStandardModelGaugeBosonTarget weakGaugeBosonTarget
    ; smRowTargetOnly =
        true
    ; smRowTargetOnlyIsTrue =
        refl
    }

gluonGaugeBosonSMRepresentationRow :
  StandardModelRepresentationTableRow
gluonGaugeBosonSMRepresentationRow =
  record
    { smRowKind =
        gaugeBosonRepresentationRow
    ; smRowLabel =
        "gluon-gauge-boson-target-row"
    ; smRowPrimeLane =
        Moonshine.p5
    ; smRowGaugeFactor =
        LaneGauge.e8LaneSU3c
    ; smRowGaugeFactorMatchesObjectMap =
        refl
    ; smRowMatterSector =
        noStandardModelMatterSectorTarget
    ; smRowMatterRepresentation =
        noMatterRepresentation
    ; smRowGaugeBosonTarget =
        someStandardModelGaugeBosonTarget gluonGaugeBosonTarget
    ; smRowTargetOnly =
        true
    ; smRowTargetOnlyIsTrue =
        refl
    }

canonicalStandardModelRepresentationTableRows :
  List StandardModelRepresentationTableRow
canonicalStandardModelRepresentationTableRows =
  leftQuarkDoubletSMRepresentationRow
  ∷ rightUpQuarkSMRepresentationRow
  ∷ rightDownQuarkSMRepresentationRow
  ∷ leftLeptonDoubletSMRepresentationRow
  ∷ rightChargedLeptonSMRepresentationRow
  ∷ hyperchargeGaugeBosonSMRepresentationRow
  ∷ weakGaugeBosonSMRepresentationRow
  ∷ gluonGaugeBosonSMRepresentationRow
  ∷ []

data StandardModelRepresentationMatchBlocker : Set where
  missingPrimeLaneQuantumNumbersAPI :
    StandardModelRepresentationMatchBlocker

  blockedAtExactStandardModelCarrierFunctorMatch :
    ExactStandardModelCarrierFunctorMatchBlocker →
    StandardModelRepresentationMatchBlocker

canonicalStandardModelRepresentationMatchBlockers :
  List StandardModelRepresentationMatchBlocker
canonicalStandardModelRepresentationMatchBlockers =
  missingPrimeLaneQuantumNumbersAPI
  ∷ blockedAtExactStandardModelCarrierFunctorMatch
      missingExactStandardModelCarrierFunctorMatch
  ∷ []

record StandardModelRepresentationQuantumNumberMatchAttempt :
  Setω where
  field
    attemptedRows :
      List StandardModelRepresentationTableRow

    attemptedRowsAreCanonical :
      attemptedRows
      ≡
      canonicalStandardModelRepresentationTableRows

    matchBlockers :
      List StandardModelRepresentationMatchBlocker

    matchBlockersAreCanonical :
      matchBlockers
      ≡
      canonicalStandardModelRepresentationMatchBlockers

    exactStandardModelCarrierFunctorMatchBlocker :
      ExactStandardModelCarrierFunctorMatchBlocker

    exactStandardModelCarrierFunctorMatchBlockerIsCanonical :
      exactStandardModelCarrierFunctorMatchBlocker
      ≡
      missingExactStandardModelCarrierFunctorMatch

    primeLaneQuantumNumbersAPISupplied :
      Bool

    primeLaneQuantumNumbersAPISuppliedIsFalse :
      primeLaneQuantumNumbersAPISupplied ≡ false

    quantumNumberMatchPromoted :
      Bool

    quantumNumberMatchPromotedIsFalse :
      quantumNumberMatchPromoted ≡ false

    boundary :
      List String

open StandardModelRepresentationQuantumNumberMatchAttempt public

canonicalStandardModelRepresentationQuantumNumberMatchAttempt :
  StandardModelRepresentationQuantumNumberMatchAttempt
canonicalStandardModelRepresentationQuantumNumberMatchAttempt =
  record
    { attemptedRows =
        canonicalStandardModelRepresentationTableRows
    ; attemptedRowsAreCanonical =
        refl
    ; matchBlockers =
        canonicalStandardModelRepresentationMatchBlockers
    ; matchBlockersAreCanonical =
        refl
    ; exactStandardModelCarrierFunctorMatchBlocker =
        missingExactStandardModelCarrierFunctorMatch
    ; exactStandardModelCarrierFunctorMatchBlockerIsCanonical =
        refl
    ; primeLaneQuantumNumbersAPISupplied =
        false
    ; primeLaneQuantumNumbersAPISuppliedIsFalse =
        refl
    ; quantumNumberMatchPromoted =
        false
    ; quantumNumberMatchPromotedIsFalse =
        refl
    ; boundary =
        "The Standard Model representation rows are target rows over the existing prime-lane object map and MatterRepresentation constructors"
        ∷ "Gauge-boson rows use p2->U1Y, p3->SU2L, and p5->SU3c; p7 remains only the existing high-energy SU2R bridge lane"
        ∷ "Quark and lepton rows are parked on p>=11 matter/trivial-gauge lanes and reuse canonical matter-surface representation constructors"
        ∷ "The quantum-number equality proof is not attempted because no primeLaneQuantumNumbers API is supplied"
        ∷ "Exact Standard Model carrier-functor matching remains fail-closed at missingExactStandardModelCarrierFunctorMatch"
        ∷ []
    }

record StandardModelRepresentationTableTargetAttemptReceipt : Setω where
  field
    status :
      StandardModelRepresentationTableStatus

    graphFunctor :
      CarrierToPhysicsGraphFunctor

    matterRepresentationReceiptSurface :
      Matter.MatterRepresentationReceiptSurface

    representationRows :
      List StandardModelRepresentationTableRow

    representationRowsAreCanonical :
      representationRows
      ≡
      canonicalStandardModelRepresentationTableRows

    quarkRowsTargeted :
      Bool

    quarkRowsTargetedIsTrue :
      quarkRowsTargeted ≡ true

    leptonRowsTargeted :
      Bool

    leptonRowsTargetedIsTrue :
      leptonRowsTargeted ≡ true

    gaugeBosonRowsTargeted :
      Bool

    gaugeBosonRowsTargetedIsTrue :
      gaugeBosonRowsTargeted ≡ true

    quantumNumberMatchAttempt :
      StandardModelRepresentationQuantumNumberMatchAttempt

    standardModelRepresentationsPromoted :
      Bool

    standardModelRepresentationsPromotedIsFalse :
      standardModelRepresentationsPromoted ≡ false

    exactStandardModelCarrierFunctorMatchPromoted :
      Bool

    exactStandardModelCarrierFunctorMatchPromotedIsFalse :
      exactStandardModelCarrierFunctorMatchPromoted ≡ false

    noPromotionWithoutAuthority :
      CarrierToPhysicsInterpretationPromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open StandardModelRepresentationTableTargetAttemptReceipt public

canonicalStandardModelRepresentationTableTargetAttemptReceipt :
  StandardModelRepresentationTableTargetAttemptReceipt
canonicalStandardModelRepresentationTableTargetAttemptReceipt =
  record
    { status =
        standardModelRepresentationTableTargetAttemptNoPromotion
    ; graphFunctor =
        canonicalCarrierToPhysicsGraphFunctor
    ; matterRepresentationReceiptSurface =
        Matter.canonicalMatterRepresentationReceiptSurface
    ; representationRows =
        canonicalStandardModelRepresentationTableRows
    ; representationRowsAreCanonical =
        refl
    ; quarkRowsTargeted =
        true
    ; quarkRowsTargetedIsTrue =
        refl
    ; leptonRowsTargeted =
        true
    ; leptonRowsTargetedIsTrue =
        refl
    ; gaugeBosonRowsTargeted =
        true
    ; gaugeBosonRowsTargetedIsTrue =
        refl
    ; quantumNumberMatchAttempt =
        canonicalStandardModelRepresentationQuantumNumberMatchAttempt
    ; standardModelRepresentationsPromoted =
        false
    ; standardModelRepresentationsPromotedIsFalse =
        refl
    ; exactStandardModelCarrierFunctorMatchPromoted =
        false
    ; exactStandardModelCarrierFunctorMatchPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "This receipt adds an explicit Standard Model representation table target/attempt for the primeLane mapping"
        ∷ "Rows are inhabited as target records only: quark rows, lepton rows, and p2/p3/p5 gauge-boson rows"
        ∷ "The table consumes existing prime-lane gauge assignment names and MatterRepresentation constructors where available"
        ∷ "Quantum-number matching is blocked by missingPrimeLaneQuantumNumbersAPI and missingExactStandardModelCarrierFunctorMatch"
        ∷ "No Standard Model representation promotion, G_DHR ~= G_SM claim, or terminal physics promotion is made here"
        ∷ []
    }

data LocatedFilteredColimitReceiptSurface : Set where
  locatedAQFTL3FilteredColimitPreservationAttemptSurface :
    LocatedFilteredColimitReceiptSurface

  locatedAQFTL5FailClosedReceipt :
    LocatedFilteredColimitReceiptSurface

canonicalLocatedFilteredColimitReceiptSurfaces :
  List LocatedFilteredColimitReceiptSurface
canonicalLocatedFilteredColimitReceiptSurfaces =
  locatedAQFTL3FilteredColimitPreservationAttemptSurface
  ∷ locatedAQFTL5FailClosedReceipt
  ∷ []

data LocatedDHRSectorReceiptSurface : Set where
  locatedDHRGate6LocalAlgebraPreconditionAuditReceipt :
    LocatedDHRSectorReceiptSurface

  locatedDHRGaugeGate1Wave3FinalLocalBoundaryReceipt :
    LocatedDHRSectorReceiptSurface

canonicalLocatedDHRSectorReceiptSurfaces :
  List LocatedDHRSectorReceiptSurface
canonicalLocatedDHRSectorReceiptSurfaces =
  locatedDHRGate6LocalAlgebraPreconditionAuditReceipt
  ∷ locatedDHRGaugeGate1Wave3FinalLocalBoundaryReceipt
  ∷ []

data LocatedReceiptImportStatus : Set where
  locatedReceiptsRecordedWithoutDirectGate1Consumption :
    LocatedReceiptImportStatus

data FilteredColimitAttackResidual : Set where
  residualMissingCarrierLevelIsotonyTransport :
    FilteredColimitAttackResidual

  residualMissingLeftAdjointPreservesFilteredColimitsTheorem :
    FilteredColimitAttackResidual

canonicalFilteredColimitAttackResiduals :
  List FilteredColimitAttackResidual
canonicalFilteredColimitAttackResiduals =
  residualMissingCarrierLevelIsotonyTransport
  ∷ residualMissingLeftAdjointPreservesFilteredColimitsTheorem
  ∷ []

data CarrierFunctorLeftAdjointRouteBlocker : Set where
  missingCarrierFunctorLeftAdjointAPI :
    CarrierFunctorLeftAdjointRouteBlocker

  missingCarrierLevelFilteredDiagramSemantics :
    CarrierFunctorLeftAdjointRouteBlocker

  missingLeftAdjointPreservesFilteredColimitsTheorem :
    CarrierFunctorLeftAdjointRouteBlocker

  missingCarrierFunctorFilteredColimitPreservation :
    CarrierFunctorLeftAdjointRouteBlocker

  missingCarrierFunctorExactStandardModelMatch :
    CarrierFunctorLeftAdjointRouteBlocker

canonicalCarrierFunctorLeftAdjointRouteBlockers :
  List CarrierFunctorLeftAdjointRouteBlocker
canonicalCarrierFunctorLeftAdjointRouteBlockers =
  missingCarrierFunctorLeftAdjointAPI
  ∷ missingCarrierLevelFilteredDiagramSemantics
  ∷ missingLeftAdjointPreservesFilteredColimitsTheorem
  ∷ missingCarrierFunctorFilteredColimitPreservation
  ∷ missingCarrierFunctorExactStandardModelMatch
  ∷ []

record Gate1CarrierFunctorLeftAdjointFilteredColimitFailClosedReceipt :
  Setω where
  field
    attemptedRouteName :
      String

    attemptedRouteName-v :
      attemptedRouteName
      ≡
      "carrierFunctorLeftAdjoint-preserves-filtered-colimits"

    filteredColimitPrimitiveStillMissing :
      CarrierToPhysicsMissingPrimitiveWitness
        missingFilteredColimitPreservation

    filteredColimitPrimitiveStillMissingIsCanonical :
      filteredColimitPrimitiveStillMissing
      ≡
      missingFiniteSupportFilteredColimitPrimitiveWitness

    routeBlockers :
      List CarrierFunctorLeftAdjointRouteBlocker

    routeBlockersAreCanonical :
      routeBlockers
      ≡
      canonicalCarrierFunctorLeftAdjointRouteBlockers

    exactStandardModelCarrierFunctorMatchBlocker :
      ExactStandardModelCarrierFunctorMatchBlocker

    exactStandardModelCarrierFunctorMatchBlockerIsCanonical :
      exactStandardModelCarrierFunctorMatchBlocker
      ≡
      missingExactStandardModelCarrierFunctorMatch

    carrierFunctorLeftAdjointSupplied :
      Bool

    carrierFunctorLeftAdjointSuppliedIsFalse :
      carrierFunctorLeftAdjointSupplied ≡ false

    filteredColimitPreservationPromoted :
      Bool

    filteredColimitPreservationPromotedIsFalse :
      filteredColimitPreservationPromoted ≡ false

    exactStandardModelCarrierFunctorMatchPromoted :
      Bool

    exactStandardModelCarrierFunctorMatchPromotedIsFalse :
      exactStandardModelCarrierFunctorMatchPromoted ≡ false

    leftAdjointRouteBoundary :
      List String

open Gate1CarrierFunctorLeftAdjointFilteredColimitFailClosedReceipt public

canonicalGate1CarrierFunctorLeftAdjointFilteredColimitFailClosedReceipt :
  Gate1CarrierFunctorLeftAdjointFilteredColimitFailClosedReceipt
canonicalGate1CarrierFunctorLeftAdjointFilteredColimitFailClosedReceipt =
  record
    { attemptedRouteName =
        "carrierFunctorLeftAdjoint-preserves-filtered-colimits"
    ; attemptedRouteName-v =
        refl
    ; filteredColimitPrimitiveStillMissing =
        missingFiniteSupportFilteredColimitPrimitiveWitness
    ; filteredColimitPrimitiveStillMissingIsCanonical =
        refl
    ; routeBlockers =
        canonicalCarrierFunctorLeftAdjointRouteBlockers
    ; routeBlockersAreCanonical =
        refl
    ; exactStandardModelCarrierFunctorMatchBlocker =
        missingExactStandardModelCarrierFunctorMatch
    ; exactStandardModelCarrierFunctorMatchBlockerIsCanonical =
        refl
    ; carrierFunctorLeftAdjointSupplied =
        false
    ; carrierFunctorLeftAdjointSuppliedIsFalse =
        refl
    ; filteredColimitPreservationPromoted =
        false
    ; filteredColimitPreservationPromotedIsFalse =
        refl
    ; exactStandardModelCarrierFunctorMatchPromoted =
        false
    ; exactStandardModelCarrierFunctorMatchPromotedIsFalse =
        refl
    ; leftAdjointRouteBoundary =
        "l3 carrierFunctorLeftAdjoint route attempted: the local Gate1 API has no carrierFunctorLeftAdjoint constructor or field"
        ∷ "Without carrier-level filtered diagram semantics and a left-adjoint-preserves-filtered-colimits theorem, filtered-colimit preservation remains missingFiniteSupportFilteredColimitPrimitiveWitness"
        ∷ "This receipt records the route as fail-closed and does not infer DHR-sector compatibility from the graph functor"
        ∷ "Exact Standard Model carrier-functor matching remains missingExactStandardModelCarrierFunctorMatch"
        ∷ []
    }

data DHRSectorCompatibilityAttackResidual : Set where
  residualMissingDASHILocalAlgebra :
    DHRSectorCompatibilityAttackResidual

  residualMissingArbitrarySectorEndomorphismSemantics :
    DHRSectorCompatibilityAttackResidual

  residualMissingGDHRStandardModelMatch :
    DHRSectorCompatibilityAttackResidual

canonicalDHRSectorCompatibilityAttackResiduals :
  List DHRSectorCompatibilityAttackResidual
canonicalDHRSectorCompatibilityAttackResiduals =
  residualMissingDASHILocalAlgebra
  ∷ residualMissingArbitrarySectorEndomorphismSemantics
  ∷ residualMissingGDHRStandardModelMatch
  ∷ []

record Gate1FilteredColimitDHRAttackFailClosedReceipt : Setω where
  field
    locatedFilteredColimitReceiptSurfaces :
      List LocatedFilteredColimitReceiptSurface

    locatedFilteredColimitReceiptSurfacesAreCanonical :
      locatedFilteredColimitReceiptSurfaces
      ≡
      canonicalLocatedFilteredColimitReceiptSurfaces

    locatedDHRSectorReceiptSurfaces :
      List LocatedDHRSectorReceiptSurface

    locatedDHRSectorReceiptSurfacesAreCanonical :
      locatedDHRSectorReceiptSurfaces
      ≡
      canonicalLocatedDHRSectorReceiptSurfaces

    locatedReceiptImportStatus :
      LocatedReceiptImportStatus

    locatedReceiptImportStatusIsBlocked :
      locatedReceiptImportStatus
      ≡
      locatedReceiptsRecordedWithoutDirectGate1Consumption

    filteredColimitAttackResiduals :
      List FilteredColimitAttackResidual

    filteredColimitAttackResidualsAreCanonical :
      filteredColimitAttackResiduals
      ≡
      canonicalFilteredColimitAttackResiduals

    dhrSectorCompatibilityAttackResiduals :
      List DHRSectorCompatibilityAttackResidual

    dhrSectorCompatibilityAttackResidualsAreCanonical :
      dhrSectorCompatibilityAttackResiduals
      ≡
      canonicalDHRSectorCompatibilityAttackResiduals

    exactStandardModelCarrierFunctorMatchBlocker :
      ExactStandardModelCarrierFunctorMatchBlocker

    exactStandardModelCarrierFunctorMatchBlockerIsCanonical :
      exactStandardModelCarrierFunctorMatchBlocker
      ≡
      missingExactStandardModelCarrierFunctorMatch

    exactStandardModelCarrierFunctorMatchDependencies :
      List ExactStandardModelCarrierFunctorMatchDependency

    exactStandardModelCarrierFunctorMatchDependenciesAreCanonical :
      exactStandardModelCarrierFunctorMatchDependencies
      ≡
      canonicalExactStandardModelCarrierFunctorMatchDependencies

    filteredColimitPreservationPromoted :
      Bool

    filteredColimitPreservationPromotedIsFalse :
      filteredColimitPreservationPromoted ≡ false

    dhrSectorCompatibilityPromoted :
      Bool

    dhrSectorCompatibilityPromotedIsFalse :
      dhrSectorCompatibilityPromoted ≡ false

    exactStandardModelCarrierFunctorMatchPromoted :
      Bool

    exactStandardModelCarrierFunctorMatchPromotedIsFalse :
      exactStandardModelCarrierFunctorMatchPromoted ≡ false

    attackBoundary :
      List String

open Gate1FilteredColimitDHRAttackFailClosedReceipt public

canonicalGate1FilteredColimitDHRAttackFailClosedReceipt :
  Gate1FilteredColimitDHRAttackFailClosedReceipt
canonicalGate1FilteredColimitDHRAttackFailClosedReceipt =
  record
    { locatedFilteredColimitReceiptSurfaces =
        canonicalLocatedFilteredColimitReceiptSurfaces
    ; locatedFilteredColimitReceiptSurfacesAreCanonical =
        refl
    ; locatedDHRSectorReceiptSurfaces =
        canonicalLocatedDHRSectorReceiptSurfaces
    ; locatedDHRSectorReceiptSurfacesAreCanonical =
        refl
    ; locatedReceiptImportStatus =
        locatedReceiptsRecordedWithoutDirectGate1Consumption
    ; locatedReceiptImportStatusIsBlocked =
        refl
    ; filteredColimitAttackResiduals =
        canonicalFilteredColimitAttackResiduals
    ; filteredColimitAttackResidualsAreCanonical =
        refl
    ; dhrSectorCompatibilityAttackResiduals =
        canonicalDHRSectorCompatibilityAttackResiduals
    ; dhrSectorCompatibilityAttackResidualsAreCanonical =
        refl
    ; exactStandardModelCarrierFunctorMatchBlocker =
        missingExactStandardModelCarrierFunctorMatch
    ; exactStandardModelCarrierFunctorMatchBlockerIsCanonical =
        refl
    ; exactStandardModelCarrierFunctorMatchDependencies =
        canonicalExactStandardModelCarrierFunctorMatchDependencies
    ; exactStandardModelCarrierFunctorMatchDependenciesAreCanonical =
        refl
    ; filteredColimitPreservationPromoted =
        false
    ; filteredColimitPreservationPromotedIsFalse =
        refl
    ; dhrSectorCompatibilityPromoted =
        false
    ; dhrSectorCompatibilityPromotedIsFalse =
        refl
    ; exactStandardModelCarrierFunctorMatchPromoted =
        false
    ; exactStandardModelCarrierFunctorMatchPromotedIsFalse =
        refl
    ; attackBoundary =
        "The AQFT l3 filtered-colimit attempt and l5 fail-closed receipts are recorded as located receipt surfaces, not consumed as direct Gate1 proof dependencies"
        ∷ "The located AQFT l3 receipt records threaded colimit shape but no promoted preservation theorem; the l5 receipt keeps DASHILocalAlgebra unpromoted"
        ∷ "No local left-adjoint-preserves-filtered-colimits API is available at Gate1; the missing left-adjoint theorem is recorded as a dependency rather than assumed"
        ∷ "The located DHR local-algebra precondition and Gate1 wave-3 boundary receipts keep missingDASHILocalAlgebra, arbitrary-sector semantics, and Gate1/Standard Model fabrication fail-closed"
        ∷ "Gate1/Gate6 agreement is therefore fail-closed at missingExactStandardModelCarrierFunctorMatch"
        ∷ []
    }

record Gate1FilteredColimitDHRCompatibilityTrancheReceipt : Setω where
  field
    carrierFunctor :
      CarrierToPhysicsGraphFunctor

    functorLawReceiptSurface :
      CarrierToPhysicsFunctorLawReceiptSurface

    filteredColimitLawSurface :
      FiniteSupportFilteredColimitLawReceipt

    filteredColimitPrimitive :
      CarrierToPhysicsMissingPrimitiveWitness
        missingFilteredColimitPreservation

    filteredColimitPrimitiveMatchesSurface :
      filteredColimitPrimitive
      ≡
      FiniteSupportFilteredColimitLawReceipt.preservationProof
        filteredColimitLawSurface

    dhrSectorCompatibilitySurface :
      DHRSectorCompatibilityLawReceipt

    dhrSectorCompatibilityPrimitive :
      CarrierToPhysicsMissingPrimitiveWitness
        missingDHRSectorCompatibility

    dhrSectorCompatibilityPrimitiveMatchesSurface :
      dhrSectorCompatibilityPrimitive
      ≡
      DHRSectorCompatibilityLawReceipt.dhrCompatibilityProof
        dhrSectorCompatibilitySurface

    exactStandardModelCarrierFunctorMatchBlocker :
      ExactStandardModelCarrierFunctorMatchBlocker

    exactStandardModelCarrierFunctorMatchBlockerIsCanonical :
      exactStandardModelCarrierFunctorMatchBlocker
      ≡
      missingExactStandardModelCarrierFunctorMatch

    filteredColimitDHRAttackFailClosedReceipt :
      Gate1FilteredColimitDHRAttackFailClosedReceipt

    filteredColimitPreservationPromoted :
      Bool

    filteredColimitPreservationPromotedIsFalse :
      filteredColimitPreservationPromoted ≡ false

    dhrSectorCompatibilityPromoted :
      Bool

    dhrSectorCompatibilityPromotedIsFalse :
      dhrSectorCompatibilityPromoted ≡ false

    exactStandardModelCarrierFunctorMatchPromoted :
      Bool

    exactStandardModelCarrierFunctorMatchPromotedIsFalse :
      exactStandardModelCarrierFunctorMatchPromoted ≡ false

    gate1TrancheBoundary :
      List String

open Gate1FilteredColimitDHRCompatibilityTrancheReceipt public

canonicalGate1FilteredColimitDHRCompatibilityTrancheReceipt :
  Gate1FilteredColimitDHRCompatibilityTrancheReceipt
canonicalGate1FilteredColimitDHRCompatibilityTrancheReceipt =
  record
    { carrierFunctor =
        canonicalCarrierToPhysicsGraphFunctor
    ; functorLawReceiptSurface =
        canonicalCarrierToPhysicsFunctorLawReceiptSurface
    ; filteredColimitLawSurface =
        canonicalFiniteSupportFilteredColimitLawReceipt
    ; filteredColimitPrimitive =
        missingFiniteSupportFilteredColimitPrimitiveWitness
    ; filteredColimitPrimitiveMatchesSurface =
        refl
    ; dhrSectorCompatibilitySurface =
        canonicalDHRSectorCompatibilityLawReceipt
    ; dhrSectorCompatibilityPrimitive =
        missingDHRSectorCompatibilityPrimitiveWitness
    ; dhrSectorCompatibilityPrimitiveMatchesSurface =
        refl
    ; exactStandardModelCarrierFunctorMatchBlocker =
        missingExactStandardModelCarrierFunctorMatch
    ; exactStandardModelCarrierFunctorMatchBlockerIsCanonical =
        refl
    ; filteredColimitDHRAttackFailClosedReceipt =
        canonicalGate1FilteredColimitDHRAttackFailClosedReceipt
    ; filteredColimitPreservationPromoted =
        false
    ; filteredColimitPreservationPromotedIsFalse =
        refl
    ; dhrSectorCompatibilityPromoted =
        false
    ; dhrSectorCompatibilityPromotedIsFalse =
        refl
    ; exactStandardModelCarrierFunctorMatchPromoted =
        false
    ; exactStandardModelCarrierFunctorMatchPromotedIsFalse =
        refl
    ; gate1TrancheBoundary =
        "Gate1 graph functor, prime-lane representation semantics, prime-bump covariance, and depth naturality remain inhabited"
        ∷ "Filtered-colimit preservation is attacked through the located AQFT l3/l5 receipt surfaces, then kept fail-closed because missingFiniteSupportFilteredColimitPrimitiveWitness remains open and a local left-adjoint preservation theorem is absent"
        ∷ "DHR-sector compatibility is attacked through the located DHR local-algebra precondition audit, then kept fail-closed because DASHILocalAlgebra and arbitrary-sector semantics are absent"
        ∷ "Exact Standard Model carrier-functor matching remains the Gate1/Gate6/Gate8 blocker named missingExactStandardModelCarrierFunctorMatch"
        ∷ []
    }

record Gate1Gate6ExactMatchHandoffReceipt : Setω where
  field
    gate1CompatibilityTranche :
      Gate1FilteredColimitDHRCompatibilityTrancheReceipt

    filteredColimitPrimitiveStillOpen :
      CarrierToPhysicsMissingPrimitiveWitness
        missingFilteredColimitPreservation

    filteredColimitPrimitiveStillOpenMatchesTranche :
      filteredColimitPrimitiveStillOpen
      ≡
      Gate1FilteredColimitDHRCompatibilityTrancheReceipt.filteredColimitPrimitive
        gate1CompatibilityTranche

    dhrSectorCompatibilityPrimitiveStillOpen :
      CarrierToPhysicsMissingPrimitiveWitness
        missingDHRSectorCompatibility

    dhrSectorCompatibilityPrimitiveStillOpenMatchesTranche :
      dhrSectorCompatibilityPrimitiveStillOpen
      ≡
      Gate1FilteredColimitDHRCompatibilityTrancheReceipt.dhrSectorCompatibilityPrimitive
        gate1CompatibilityTranche

    exactStandardModelCarrierFunctorMatchBlocker :
      ExactStandardModelCarrierFunctorMatchBlocker

    exactStandardModelCarrierFunctorMatchBlockerIsCanonical :
      exactStandardModelCarrierFunctorMatchBlocker
      ≡
      missingExactStandardModelCarrierFunctorMatch

    suppliedForeignIdentityPathConsumedByGate6 :
      Bool

    suppliedForeignIdentityPathConsumedByGate6IsTrue :
      suppliedForeignIdentityPathConsumedByGate6 ≡ true

    filteredColimitPreservationPromoted :
      Bool

    filteredColimitPreservationPromotedIsFalse :
      filteredColimitPreservationPromoted ≡ false

    dhrSectorCompatibilityPromoted :
      Bool

    dhrSectorCompatibilityPromotedIsFalse :
      dhrSectorCompatibilityPromoted ≡ false

    exactStandardModelCarrierFunctorMatchPromoted :
      Bool

    exactStandardModelCarrierFunctorMatchPromotedIsFalse :
      exactStandardModelCarrierFunctorMatchPromoted ≡ false

    handoffBoundary :
      List String

open Gate1Gate6ExactMatchHandoffReceipt public

canonicalGate1Gate6ExactMatchHandoffReceipt :
  Gate1Gate6ExactMatchHandoffReceipt
canonicalGate1Gate6ExactMatchHandoffReceipt =
  record
    { gate1CompatibilityTranche =
        canonicalGate1FilteredColimitDHRCompatibilityTrancheReceipt
    ; filteredColimitPrimitiveStillOpen =
        missingFiniteSupportFilteredColimitPrimitiveWitness
    ; filteredColimitPrimitiveStillOpenMatchesTranche =
        refl
    ; dhrSectorCompatibilityPrimitiveStillOpen =
        missingDHRSectorCompatibilityPrimitiveWitness
    ; dhrSectorCompatibilityPrimitiveStillOpenMatchesTranche =
        refl
    ; exactStandardModelCarrierFunctorMatchBlocker =
        missingExactStandardModelCarrierFunctorMatch
    ; exactStandardModelCarrierFunctorMatchBlockerIsCanonical =
        refl
    ; suppliedForeignIdentityPathConsumedByGate6 =
        true
    ; suppliedForeignIdentityPathConsumedByGate6IsTrue =
        refl
    ; filteredColimitPreservationPromoted =
        false
    ; filteredColimitPreservationPromotedIsFalse =
        refl
    ; dhrSectorCompatibilityPromoted =
        false
    ; dhrSectorCompatibilityPromotedIsFalse =
        refl
    ; exactStandardModelCarrierFunctorMatchPromoted =
        false
    ; exactStandardModelCarrierFunctorMatchPromotedIsFalse =
        refl
    ; handoffBoundary =
        "Gate1 wave-2 handoff records that Gate6 can consume supplied foreign-lane identity evidence, while Gate1 semantic matching remains open"
        ∷ "Filtered-colimit preservation and DHR-sector compatibility remain explicit carrier-functor primitives, with filteredColimitPreservationPromoted still false"
        ∷ "The exact Standard Model carrier-functor match is still not promoted"
        ∷ "No G_DHR ~= G_SM, terminal Gate8, Clay, W3, W4, or W5 promotion follows from this receipt"
        ∷ []
    }

record Gate1Gate6FinalLocalExactMatchReceipt : Setω where
  field
    previousHandoff :
      Gate1Gate6ExactMatchHandoffReceipt

    suppliedForeignIdentityPathConsumedByGate6 :
      Bool

    suppliedForeignIdentityPathConsumedByGate6IsTrue :
      suppliedForeignIdentityPathConsumedByGate6 ≡ true

    filteredColimitPrimitiveStillOpen :
      CarrierToPhysicsMissingPrimitiveWitness
        missingFilteredColimitPreservation

    filteredColimitPrimitiveStillOpenMatchesCanonical :
      filteredColimitPrimitiveStillOpen
      ≡
      missingFiniteSupportFilteredColimitPrimitiveWitness

    dhrSectorCompatibilityPrimitiveStillOpen :
      CarrierToPhysicsMissingPrimitiveWitness
        missingDHRSectorCompatibility

    dhrSectorCompatibilityPrimitiveStillOpenMatchesCanonical :
      dhrSectorCompatibilityPrimitiveStillOpen
      ≡
      missingDHRSectorCompatibilityPrimitiveWitness

    exactStandardModelCarrierFunctorMatchBlocker :
      ExactStandardModelCarrierFunctorMatchBlocker

    exactStandardModelCarrierFunctorMatchBlockerIsCanonical :
      exactStandardModelCarrierFunctorMatchBlocker
      ≡
      missingExactStandardModelCarrierFunctorMatch

    exactStandardModelCarrierFunctorMatchPromoted :
      Bool

    exactStandardModelCarrierFunctorMatchPromotedIsFalse :
      exactStandardModelCarrierFunctorMatchPromoted ≡ false

    finalLocalBoundary :
      List String

open Gate1Gate6FinalLocalExactMatchReceipt public

canonicalGate1Gate6FinalLocalExactMatchReceipt :
  Gate1Gate6FinalLocalExactMatchReceipt
canonicalGate1Gate6FinalLocalExactMatchReceipt =
  record
    { previousHandoff =
        canonicalGate1Gate6ExactMatchHandoffReceipt
    ; suppliedForeignIdentityPathConsumedByGate6 =
        true
    ; suppliedForeignIdentityPathConsumedByGate6IsTrue =
        refl
    ; filteredColimitPrimitiveStillOpen =
        missingFiniteSupportFilteredColimitPrimitiveWitness
    ; filteredColimitPrimitiveStillOpenMatchesCanonical =
        refl
    ; dhrSectorCompatibilityPrimitiveStillOpen =
        missingDHRSectorCompatibilityPrimitiveWitness
    ; dhrSectorCompatibilityPrimitiveStillOpenMatchesCanonical =
        refl
    ; exactStandardModelCarrierFunctorMatchBlocker =
        missingExactStandardModelCarrierFunctorMatch
    ; exactStandardModelCarrierFunctorMatchBlockerIsCanonical =
        refl
    ; exactStandardModelCarrierFunctorMatchPromoted =
        false
    ; exactStandardModelCarrierFunctorMatchPromotedIsFalse =
        refl
    ; finalLocalBoundary =
        "Gate1 wave-3 final-local receipt records that Gate6 supplied-witness foreign-lane identity consumption does not close Gate1 semantics"
        ∷ "Filtered-colimit preservation and DHR-sector compatibility remain explicit missing semantic primitives, and missingExactStandardModelCarrierFunctorMatch remains canonical"
        ∷ "The exact Standard Model carrier-functor match remains the canonical Gate1/Gate6/Gate8 blocker"
        ∷ "No G_DHR ~= G_SM or terminal promotion follows from this receipt"
        ∷ []
    }

record Gate1FilteredColimitDHRSMMatchResidualFrontierReceipt : Setω where
  field
    finalLocalExactMatchReceipt :
      Gate1Gate6FinalLocalExactMatchReceipt

    filteredColimitTranche :
      Gate1FilteredColimitDHRCompatibilityTrancheReceipt

    filteredColimitLawReceipt :
      FiniteSupportFilteredColimitLawReceipt

    dhrCompatibilityLawReceipt :
      DHRSectorCompatibilityLawReceipt

    leftAdjointRouteReceipt :
      Gate1CarrierFunctorLeftAdjointFilteredColimitFailClosedReceipt

    exactStandardModelCarrierFunctorMatchDependencies :
      List ExactStandardModelCarrierFunctorMatchDependency

    exactStandardModelCarrierFunctorMatchDependenciesAreCanonical :
      exactStandardModelCarrierFunctorMatchDependencies
      ≡
      canonicalExactStandardModelCarrierFunctorMatchDependencies

    filteredColimitPrimitiveStillOpen :
      CarrierToPhysicsMissingPrimitiveWitness
        missingFilteredColimitPreservation

    filteredColimitPrimitiveStillOpenMatchesCanonical :
      filteredColimitPrimitiveStillOpen
      ≡
      missingFiniteSupportFilteredColimitPrimitiveWitness

    dhrSectorCompatibilityPrimitiveStillOpen :
      CarrierToPhysicsMissingPrimitiveWitness
        missingDHRSectorCompatibility

    dhrSectorCompatibilityPrimitiveStillOpenMatchesCanonical :
      dhrSectorCompatibilityPrimitiveStillOpen
      ≡
      missingDHRSectorCompatibilityPrimitiveWitness

    exactStandardModelCarrierFunctorMatchBlocker :
      ExactStandardModelCarrierFunctorMatchBlocker

    exactStandardModelCarrierFunctorMatchBlockerIsCanonical :
      exactStandardModelCarrierFunctorMatchBlocker
      ≡
      missingExactStandardModelCarrierFunctorMatch

    filteredColimitPreservationPromoted :
      Bool

    filteredColimitPreservationPromotedIsFalse :
      filteredColimitPreservationPromoted ≡ false

    dhrSectorCompatibilityPromoted :
      Bool

    dhrSectorCompatibilityPromotedIsFalse :
      dhrSectorCompatibilityPromoted ≡ false

    gDHRStandardModelMatchClaimed :
      Bool

    gDHRStandardModelMatchClaimedIsFalse :
      gDHRStandardModelMatchClaimed ≡ false

    frontierBoundary :
      List String

open Gate1FilteredColimitDHRSMMatchResidualFrontierReceipt public

canonicalGate1FilteredColimitDHRSMMatchResidualFrontierReceipt :
  Gate1FilteredColimitDHRSMMatchResidualFrontierReceipt
canonicalGate1FilteredColimitDHRSMMatchResidualFrontierReceipt =
  record
    { finalLocalExactMatchReceipt =
        canonicalGate1Gate6FinalLocalExactMatchReceipt
    ; filteredColimitTranche =
        canonicalGate1FilteredColimitDHRCompatibilityTrancheReceipt
    ; filteredColimitLawReceipt =
        canonicalFiniteSupportFilteredColimitLawReceipt
    ; dhrCompatibilityLawReceipt =
        canonicalDHRSectorCompatibilityLawReceipt
    ; leftAdjointRouteReceipt =
        canonicalGate1CarrierFunctorLeftAdjointFilteredColimitFailClosedReceipt
    ; exactStandardModelCarrierFunctorMatchDependencies =
        canonicalExactStandardModelCarrierFunctorMatchDependencies
    ; exactStandardModelCarrierFunctorMatchDependenciesAreCanonical =
        refl
    ; filteredColimitPrimitiveStillOpen =
        missingFiniteSupportFilteredColimitPrimitiveWitness
    ; filteredColimitPrimitiveStillOpenMatchesCanonical =
        refl
    ; dhrSectorCompatibilityPrimitiveStillOpen =
        missingDHRSectorCompatibilityPrimitiveWitness
    ; dhrSectorCompatibilityPrimitiveStillOpenMatchesCanonical =
        refl
    ; exactStandardModelCarrierFunctorMatchBlocker =
        missingExactStandardModelCarrierFunctorMatch
    ; exactStandardModelCarrierFunctorMatchBlockerIsCanonical =
        refl
    ; filteredColimitPreservationPromoted =
        false
    ; filteredColimitPreservationPromotedIsFalse =
        refl
    ; dhrSectorCompatibilityPromoted =
        false
    ; dhrSectorCompatibilityPromotedIsFalse =
        refl
    ; gDHRStandardModelMatchClaimed =
        false
    ; gDHRStandardModelMatchClaimedIsFalse =
        refl
    ; frontierBoundary =
        "Gate1 frontier keeps missingFiniteSupportFilteredColimitPrimitiveWitness and missingDHRSectorCompatibilityPrimitiveWitness as explicit missing primitives"
        ∷ "The exact Standard Model carrier-functor match depends on filtered-colimit preservation, left-adjoint colimit semantics, DASHI local algebra, arbitrary DHR sectors, and G_DHR/SM identification, while missingExactStandardModelCarrierFunctorMatch remains open"
        ∷ "Gate6 supplied identity-witness consumption does not discharge Gate1 filtered-colimit or DHR-sector compatibility"
        ∷ "No G_DHR ~= G_SM claim is recorded at the Gate1 frontier; the exact-match obstruction remains named directly"
        ∷ []
    }

gate1FilteredColimitDHRSMMatchResidualFrontierNotClaimedAtFrontier :
  Gate1FilteredColimitDHRSMMatchResidualFrontierReceipt.gDHRStandardModelMatchClaimed
    canonicalGate1FilteredColimitDHRSMMatchResidualFrontierReceipt
  ≡
  false
gate1FilteredColimitDHRSMMatchResidualFrontierNotClaimedAtFrontier =
  refl

gate1FilteredColimitDHRSMMatchResidualFrontierFilteredColimitStillFalse :
  Gate1FilteredColimitDHRSMMatchResidualFrontierReceipt.filteredColimitPreservationPromoted
    canonicalGate1FilteredColimitDHRSMMatchResidualFrontierReceipt
  ≡
  false
gate1FilteredColimitDHRSMMatchResidualFrontierFilteredColimitStillFalse =
  refl

gate1FilteredColimitDHRSMMatchResidualFrontierDHRStillFalse :
  Gate1FilteredColimitDHRSMMatchResidualFrontierReceipt.dhrSectorCompatibilityPromoted
    canonicalGate1FilteredColimitDHRSMMatchResidualFrontierReceipt
  ≡
  false
gate1FilteredColimitDHRSMMatchResidualFrontierDHRStillFalse =
  refl

gate1FilteredColimitDHRSMMatchResidualFrontierExactMatchBlockerIsCanonical :
  Gate1FilteredColimitDHRSMMatchResidualFrontierReceipt.exactStandardModelCarrierFunctorMatchBlocker
    canonicalGate1FilteredColimitDHRSMMatchResidualFrontierReceipt
  ≡
  missingExactStandardModelCarrierFunctorMatch
gate1FilteredColimitDHRSMMatchResidualFrontierExactMatchBlockerIsCanonical =
  refl

gate1FilteredColimitDHRSMMatchResidualFrontierWitnessBoundary :
  List String
gate1FilteredColimitDHRSMMatchResidualFrontierWitnessBoundary =
  "The canonical frontier receipt is inhabited and records gDHRStandardModelMatchClaimed = false"
  ∷ "The filtered-colimit and DHR-sector compatibility booleans remain false in the same frontier record"
  ∷ "The exact Standard Model carrier-functor match remains the canonical blocker"
  ∷ "No new axioms, postulates, or external assumptions are introduced here"
  ∷ []

record Gate1Gate8Term1SMCarrierFunctorBlockerReceipt : Setω where
  field
    finiteGaugeEvidence :
      ExactSM.Gate8Term1FiniteGaugeEvidenceBlockerReceipt

    residualFrontier :
      Gate1FilteredColimitDHRSMMatchResidualFrontierReceipt

    exactMatchDependencies :
      List ExactStandardModelCarrierFunctorMatchDependency

    exactMatchDependenciesAreCanonical :
      exactMatchDependencies
      ≡
      canonicalExactStandardModelCarrierFunctorMatchDependencies

    filteredColimitPrimitiveStillOpen :
      CarrierToPhysicsMissingPrimitiveWitness
        missingFilteredColimitPreservation

    filteredColimitPrimitiveStillOpenIsCanonical :
      filteredColimitPrimitiveStillOpen
      ≡
      missingFiniteSupportFilteredColimitPrimitiveWitness

    dhrSectorCompatibilityPrimitiveStillOpen :
      CarrierToPhysicsMissingPrimitiveWitness
        missingDHRSectorCompatibility

    dhrSectorCompatibilityPrimitiveStillOpenIsCanonical :
      dhrSectorCompatibilityPrimitiveStillOpen
      ≡
      missingDHRSectorCompatibilityPrimitiveWitness

    exactSMCarrierFunctorBlocker :
      ExactStandardModelCarrierFunctorMatchBlocker

    exactSMCarrierFunctorBlockerIsCanonical :
      exactSMCarrierFunctorBlocker
      ≡
      missingExactStandardModelCarrierFunctorMatch

    finiteU1SU2SU3EvidencePackaged :
      Bool

    finiteU1SU2SU3EvidencePackagedIsTrue :
      finiteU1SU2SU3EvidencePackaged ≡ true

    gDHRStandardModelMatchClaimed :
      Bool

    gDHRStandardModelMatchClaimedIsFalse :
      gDHRStandardModelMatchClaimed ≡ false

    exactStandardModelCarrierFunctorMatchPromoted :
      Bool

    exactStandardModelCarrierFunctorMatchPromotedIsFalse :
      exactStandardModelCarrierFunctorMatchPromoted ≡ false

    carrierFunctorBlockerBoundary :
      List String

open Gate1Gate8Term1SMCarrierFunctorBlockerReceipt public

canonicalGate1Gate8Term1SMCarrierFunctorBlockerReceipt :
  Gate1Gate8Term1SMCarrierFunctorBlockerReceipt
canonicalGate1Gate8Term1SMCarrierFunctorBlockerReceipt =
  record
    { finiteGaugeEvidence =
        ExactSM.canonicalGate8Term1FiniteGaugeEvidenceBlockerReceipt
    ; residualFrontier =
        canonicalGate1FilteredColimitDHRSMMatchResidualFrontierReceipt
    ; exactMatchDependencies =
        canonicalExactStandardModelCarrierFunctorMatchDependencies
    ; exactMatchDependenciesAreCanonical =
        refl
    ; filteredColimitPrimitiveStillOpen =
        missingFiniteSupportFilteredColimitPrimitiveWitness
    ; filteredColimitPrimitiveStillOpenIsCanonical =
        refl
    ; dhrSectorCompatibilityPrimitiveStillOpen =
        missingDHRSectorCompatibilityPrimitiveWitness
    ; dhrSectorCompatibilityPrimitiveStillOpenIsCanonical =
        refl
    ; exactSMCarrierFunctorBlocker =
        missingExactStandardModelCarrierFunctorMatch
    ; exactSMCarrierFunctorBlockerIsCanonical =
        refl
    ; finiteU1SU2SU3EvidencePackaged =
        true
    ; finiteU1SU2SU3EvidencePackagedIsTrue =
        refl
    ; gDHRStandardModelMatchClaimed =
        false
    ; gDHRStandardModelMatchClaimedIsFalse =
        refl
    ; exactStandardModelCarrierFunctorMatchPromoted =
        false
    ; exactStandardModelCarrierFunctorMatchPromotedIsFalse =
        refl
    ; carrierFunctorBlockerBoundary =
        "Gate1/Gate8.term1 receives the finite U1/SU2/SU3 evidence bundle from ExactSM"
        ∷ "The finite bundle does not discharge filtered-colimit preservation or DHR-sector compatibility"
        ∷ "The exact Standard Model carrier-functor match remains missingExactStandardModelCarrierFunctorMatch"
        ∷ "No G_DHR ~= G_SM claim is made from the carrier-functor frontier"
        ∷ []
    }

record CarrierToPhysicsBoundaryThreadingReceipt : Setω where
  field
    exactStandardModelMatchToken :
      ExactSM.ExactSMMatchReceipt

    clayYMGapBoundary :
      ClayBoundary.ClayYMGapReceipt

    higgsPDGBoundary :
      HiggsBoundary.HiggsPDGBoundaryReceipt

    dhrThermodynamicLimitBoundary :
      DHRLimit.DHRThermodynamicLimitReceipt

    gate1BoundaryThreadingOpen :
      Bool

    gate1BoundaryThreadingOpenIsFalse :
      gate1BoundaryThreadingOpen ≡ false

    boundary :
      List String

open CarrierToPhysicsBoundaryThreadingReceipt public

canonicalCarrierToPhysicsBoundaryThreadingReceipt :
  CarrierToPhysicsBoundaryThreadingReceipt
canonicalCarrierToPhysicsBoundaryThreadingReceipt =
  record
    { exactStandardModelMatchToken =
        ExactSM.canonicalExactSMMatchReceipt
    ; clayYMGapBoundary =
        ClayBoundary.canonicalClayYMGapReceipt
    ; higgsPDGBoundary =
        HiggsBoundary.canonicalHiggsPDGBoundaryReceipt
    ; dhrThermodynamicLimitBoundary =
        DHRLimit.canonicalDHRThermodynamicLimitReceipt
    ; gate1BoundaryThreadingOpen =
        false
    ; gate1BoundaryThreadingOpenIsFalse =
        refl
    ; boundary =
        "Gate 1 explicitly threads the Clay/YM, Higgs/PDG, and DHR thermodynamic-limit boundaries"
        ∷ "The exact SM token remains the canonical witness bundle"
        ∷ "This record consumes boundaries only; it does not promote any remaining gate"
        ∷ []
    }
