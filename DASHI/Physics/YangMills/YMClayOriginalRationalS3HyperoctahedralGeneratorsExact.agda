{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayOriginalRationalS3HyperoctahedralGeneratorsExact where

------------------------------------------------------------------------
-- Concrete ORIGINAL RationalUnitQuaternion hyperoctahedral generators.
-- Four rational coordinate sign flips and adjacent coordinate swaps
-- preserve the original unit norm and the three e2/e3/e4 invariants.
--
-- Reuses original rational quaternion and previously defined invariant
-- owners. All norm/invariant identities are rational ring equations,
-- source-written for arbitrary original quaternion coordinates, not
-- checked only at the 1464 cubature nodes.
--
-- Remaining full-degree15 proof: averaging along these generators
-- must be reindexed over ACTUAL complete signed permutation orbits,
-- then the elementary-symmetric basis spanning theorem transported.
-- No postulated Haar or matrix carrier identity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)
open import Data.Rational using (ℚ; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as Original
import DASHI.Physics.YangMills.YMClayRationalS3DegreeThirteenInvariantCertificateExact as Inv

data Generator : Set where
  identity flip0 flip1 flip2 flip3 swap01 swap12 swap23 : Generator

record Coordinates : Set where
  constructor coords
  field
    a b c d : ℚ
open Coordinates public

actRaw : Generator → Coordinates → Coordinates
actRaw identity (coords a b c d) = coords a b c d
actRaw flip0 (coords a b c d) = coords (- a) b c d
actRaw flip1 (coords a b c d) = coords a (- b) c d
actRaw flip2 (coords a b c d) = coords a b (- c) d
actRaw flip3 (coords a b c d) = coords a b c (- d)
actRaw swap01 (coords a b c d) = coords b a c d
actRaw swap12 (coords a b c d) = coords a c b d
actRaw swap23 (coords a b c d) = coords a b d c


square : ℚ → ℚ
square x = x * x

norm : Coordinates → ℚ
norm (coords a b c d) = square a + square b + square c + square d

e2 : Coordinates → ℚ
e2 (coords a b c d) =
  square a * square b + square a * square c + square a * square d
  + square b * square c + square b * square d + square c * square d

e3 : Coordinates → ℚ
e3 (coords a b c d) =
  square a * square b * square c + square a * square b * square d
  + square a * square c * square d + square b * square c * square d

e4 : Coordinates → ℚ
e4 (coords a b c d) =
  square a * square b * square c * square d

normInvariant : ∀ g a b c d → norm (actRaw g (coords a b c d)) ≡ norm (coords a b c d)
normInvariant identity a b c d = refl
normInvariant flip0 a b c d = ℚRing.solve-∀ a b c d
normInvariant flip1 a b c d = ℚRing.solve-∀ a b c d
normInvariant flip2 a b c d = ℚRing.solve-∀ a b c d
normInvariant flip3 a b c d = ℚRing.solve-∀ a b c d
normInvariant swap01 a b c d = ℚRing.solve-∀ a b c d
normInvariant swap12 a b c d = ℚRing.solve-∀ a b c d
normInvariant swap23 a b c d = ℚRing.solve-∀ a b c d

e2Invariant : ∀ g a b c d → e2 (actRaw g (coords a b c d)) ≡ e2 (coords a b c d)
e2Invariant identity a b c d = refl
e2Invariant flip0 a b c d = ℚRing.solve-∀ a b c d
e2Invariant flip1 a b c d = ℚRing.solve-∀ a b c d
e2Invariant flip2 a b c d = ℚRing.solve-∀ a b c d
e2Invariant flip3 a b c d = ℚRing.solve-∀ a b c d
e2Invariant swap01 a b c d = ℚRing.solve-∀ a b c d
e2Invariant swap12 a b c d = ℚRing.solve-∀ a b c d
e2Invariant swap23 a b c d = ℚRing.solve-∀ a b c d

e3Invariant : ∀ g a b c d → e3 (actRaw g (coords a b c d)) ≡ e3 (coords a b c d)
e3Invariant identity a b c d = refl
e3Invariant flip0 a b c d = ℚRing.solve-∀ a b c d
e3Invariant flip1 a b c d = ℚRing.solve-∀ a b c d
e3Invariant flip2 a b c d = ℚRing.solve-∀ a b c d
e3Invariant flip3 a b c d = ℚRing.solve-∀ a b c d
e3Invariant swap01 a b c d = ℚRing.solve-∀ a b c d
e3Invariant swap12 a b c d = ℚRing.solve-∀ a b c d
e3Invariant swap23 a b c d = ℚRing.solve-∀ a b c d

e4Invariant : ∀ g a b c d → e4 (actRaw g (coords a b c d)) ≡ e4 (coords a b c d)
e4Invariant identity a b c d = refl
e4Invariant flip0 a b c d = ℚRing.solve-∀ a b c d
e4Invariant flip1 a b c d = ℚRing.solve-∀ a b c d
e4Invariant flip2 a b c d = ℚRing.solve-∀ a b c d
e4Invariant flip3 a b c d = ℚRing.solve-∀ a b c d
e4Invariant swap01 a b c d = ℚRing.solve-∀ a b c d
e4Invariant swap12 a b c d = ℚRing.solve-∀ a b c d
e4Invariant swap23 a b c d = ℚRing.solve-∀ a b c d


originalCoordinates : Original.RationalUnitQuaternion → Coordinates
originalCoordinates q =
  coords (Original.realPart q) (Original.imagI q)
         (Original.imagJ q) (Original.imagK q)

originalAct : Generator → Original.RationalUnitQuaternion →
              Original.RationalUnitQuaternion
originalAct g q =
  let moved = actRaw g (originalCoordinates q)
  in Original.rationalUnitQuaternion
       (a moved) (b moved) (c moved) (d moved)
       (trans
         (normInvariant g
           (Original.realPart q) (Original.imagI q)
           (Original.imagJ q) (Original.imagK q))
         (Original.unitNormExact q))

originalE2Invariant : ∀ g q →
  Inv.invariant2 (originalAct g q) ≡ Inv.invariant2 q
originalE2Invariant g q =
  e2Invariant g (Original.realPart q) (Original.imagI q)
    (Original.imagJ q) (Original.imagK q)

originalE3Invariant : ∀ g q →
  Inv.invariant3 (originalAct g q) ≡ Inv.invariant3 q
originalE3Invariant g q =
  e3Invariant g (Original.realPart q) (Original.imagI q)
    (Original.imagJ q) (Original.imagK q)

originalE4Invariant : ∀ g q →
  Inv.invariant4 (originalAct g q) ≡ Inv.invariant4 q
originalE4Invariant g q =
  e4Invariant g (Original.realPart q) (Original.imagI q)
    (Original.imagJ q) (Original.imagK q)
