module DASHI.Cognition.Teleodynamics.T5E8CyclicActionBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- DASHI finite-action recognition layer.
--
-- Local Python audit (scripts/check_t5_e8_c10_bridge.py) establishes for the
-- concrete finite models:
--
--   * 240 non-diagonal five-trit states;
--   * the standard doubled-coordinate E8 family has 112 + 128 = 240 roots;
--   * five-position rotation is free: 48 C5 orbits;
--   * for a standard E8 Coxeter element c, c^6 is free: 48 C5 orbits;
--   * adjoining negation gives 24 C10 orbits on each carrier;
--   * a deterministic orbit-representative matching gives a C10-equivariant
--     bijection intertwining both rotation/c^6 and sign reversal.
--
-- This is strictly weaker than E8 geometric recognition.  The same audit gives
-- an explicit counterexample showing equal five-trit Hamming distance can map
-- to different E8 inner products, so the cyclic-action bijection must not be
-- promoted to a root-system isometry.
------------------------------------------------------------------------

record C10EquivariantRecognition (T Root : Set) : Set₁ where
  constructor c10-equivariant-recognition
  field
    encode : T → Root
    decode : Root → T
    encodeDecode : (root : Root) → encode (decode root) ≡ root
    decodeEncode : (state : T) → decode (encode state) ≡ state

    rotateT : T → T
    coxeterSixth : Root → Root
    negateT : T → T
    negateRoot : Root → Root

    rotationIntertwining :
      (state : T) → encode (rotateT state) ≡ coxeterSixth (encode state)
    negationIntertwining :
      (state : T) → encode (negateT state) ≡ negateRoot (encode state)

    constructionProvenance : String

open C10EquivariantRecognition public

record NativeGeometryRecognition
    {T Root Score : Set}
    (recognition : C10EquivariantRecognition T Root)
    (nativeTernaryPairing : T → T → Score)
    (e8RootPairing : Root → Root → Score) : Set₁ where
  constructor native-geometry-recognition
  field
    pairingPreserved :
      (x y : T) →
      nativeTernaryPairing x y
      ≡ e8RootPairing (encode recognition x) (encode recognition y)
    nativeTernaryPairingSpecifiedIndependently : Bool
    nativeTernaryPairingSpecifiedIndependentlyIsTrue :
      nativeTernaryPairingSpecifiedIndependently ≡ true
    geometryJustification : String

open NativeGeometryRecognition public

data C10EquivarianceCreatesE8Geometry : Set where

data CardinalityCreatesC10Equivariance : Set where

c10EquivarianceCannotCreateE8Geometry : C10EquivarianceCreatesE8Geometry → ⊥
c10EquivarianceCannotCreateE8Geometry ()

cardinalityCannotCreateC10Equivariance : CardinalityCreatesC10Equivariance → ⊥
cardinalityCannotCreateC10Equivariance ()

record T5E8CyclicActionBoundary : Set where
  constructor t5-e8-cyclic-action-boundary
  field
    pythonFiniteAuditPaid : Bool
    t5RelativeCount240Checked : Bool
    e8RootCount240Checked : Bool
    coxeterOrder30Checked : Bool
    c5ActionBridgeIdentified : Bool
    c10ActionBridgeIdentified : Bool
    rotationAndNegationIntertwiningChecked : Bool
    hammingDeterminesE8InnerProduct : Bool
    fullE8GeometryRecognized : Bool
    physicalOrPhenomenalPromotion : Bool

open T5E8CyclicActionBoundary public

canonicalT5E8CyclicActionBoundary : T5E8CyclicActionBoundary
canonicalT5E8CyclicActionBoundary =
  t5-e8-cyclic-action-boundary
    true true true true true true true false false false
