module DASHI.Physics.SFGC.NonAbelian.CliffordEvenSubalgebra where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.SFGC.NonAbelian.GradedSFGCSite2D using
  (WeakLane; lane7; lane11; lane13)

------------------------------------------------------------------------
-- Finite quaternion-shaped even subalgebra witness over the selected lanes.
--
-- The file keeps the algebra concrete by using a 4-element basis and an
-- explicit multiplication table.  That makes the intended Clifford-even
-- relations computable by normalization rather than postulate.

data Sign : Set where
  plus minus : Sign

data EvenBasis : Set where
  one e12 e23 e13 : EvenBasis

data SignedEven : Set where
  signed : Sign → EvenBasis → SignedEven

record LaneTriple : Set where
  constructor laneTriple
  field
    first : WeakLane
    second : WeakLane
    third : WeakLane

canonicalLaneTriple : LaneTriple
canonicalLaneTriple = laneTriple lane7 lane11 lane13

plusOne : SignedEven
plusOne = signed plus one

minusOne : SignedEven
minusOne = signed minus one

mul : EvenBasis → EvenBasis → SignedEven
mul one x = signed plus x
mul x one = signed plus x
mul e12 e12 = minusOne
mul e12 e23 = signed plus e13
mul e12 e13 = signed minus e23
mul e23 e12 = signed minus e13
mul e23 e23 = minusOne
mul e23 e13 = signed plus e12
mul e13 e12 = signed plus e23
mul e13 e23 = signed minus e12
mul e13 e13 = minusOne

record CliffordEvenSubalgebraWitness : Set where
  field
    selectedWeakLanes :
      LaneTriple

    selectedWeakLanesIsCanonical :
      selectedWeakLanes ≡ canonicalLaneTriple

    basis-one :
      EvenBasis

    basis-e12 :
      EvenBasis

    basis-e23 :
      EvenBasis

    basis-e13 :
      EvenBasis

    oneIsCanonical :
      basis-one ≡ one

    e12IsCanonical :
      basis-e12 ≡ e12

    e23IsCanonical :
      basis-e23 ≡ e23

    e13IsCanonical :
      basis-e13 ≡ e13

    square-e12 :
      mul basis-e12 basis-e12 ≡ minusOne

    square-e23 :
      mul basis-e23 basis-e23 ≡ minusOne

    square-e13 :
      mul basis-e13 basis-e13 ≡ minusOne

    product-e12-e23 :
      mul basis-e12 basis-e23 ≡ signed plus e13

    product-e23-e12 :
      mul basis-e23 basis-e12 ≡ signed minus e13

    product-e12-e13 :
      mul basis-e12 basis-e13 ≡ signed minus e23

    product-e13-e12 :
      mul basis-e13 basis-e12 ≡ signed plus e23

canonicalCliffordEvenSubalgebraWitness :
  CliffordEvenSubalgebraWitness
canonicalCliffordEvenSubalgebraWitness =
  record
    { selectedWeakLanes =
        canonicalLaneTriple
    ; selectedWeakLanesIsCanonical =
        refl
    ; basis-one =
        one
    ; basis-e12 =
        e12
    ; basis-e23 =
        e23
    ; basis-e13 =
        e13
    ; oneIsCanonical =
        refl
    ; e12IsCanonical =
        refl
    ; e23IsCanonical =
        refl
    ; e13IsCanonical =
        refl
    ; square-e12 =
        refl
    ; square-e23 =
        refl
    ; square-e13 =
        refl
    ; product-e12-e23 =
        refl
    ; product-e23-e12 =
        refl
    ; product-e12-e13 =
        refl
    ; product-e13-e12 =
        refl
    }

open CliffordEvenSubalgebraWitness public
