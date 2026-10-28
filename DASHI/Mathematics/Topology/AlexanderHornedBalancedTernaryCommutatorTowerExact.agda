module DASHI.Mathematics.Topology.AlexanderHornedBalancedTernaryCommutatorTowerExact where

------------------------------------------------------------------------
-- GENUINE THREE-CHILD ABSTRACT REFEMENT, NOT HATCHER'S BINARY GEOMETRY.
-- Three root sectors remain external. A stage-n address has n trits,
-- so its free group has 3*3^n generators rather than Hatcher's 3*2^n.
--
-- The selected ternary refinement is
--   x_w -> [x_(w,-),x_(w,0)] [x_(w,0),x_(w,+)].
-- Its freely reduced child word is a b A c B C, length six.
-- Disjoint child blocks and the resulting normal-form boundaries
-- give an ordinary free-group injection (paper proof + Python test).
-- The abstract direct-limit group is then perfect and nontrivial.
--
-- This DOES NOT construct an Alexander wild ball or infer a
-- 3-child punctured-torus/pair-of-pants attachment geometry.
-- Its SU2 noise exponent would have different gate count.
--
-- ORIGINAL SOURCES: Hatcher AT Example 2B.2 is the BINARY
-- commutator source; free-group normal forms are classical.
-- EXISTING OWNERS: AlexanderHornedC3FiniteStageExact C3 rotation;
-- BalancedTernary; existing codec and ternary-pants PR #1254.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.BalancedTernary as BT
import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as Horn

record TernaryAddress : Set where
  constructor ternary-address
  field
    sector : C3.C3
    newestFirst : List BT.Trit

open TernaryAddress public

child : BT.Trit → TernaryAddress → TernaryAddress
child t (ternary-address c xs) = ternary-address c (t ∷ xs)

rotate : TernaryAddress → TernaryAddress
rotate (ternary-address c xs) =
  ternary-address (Horn.rotateSector c) xs

rotateCubed : ∀ a → rotate (rotate (rotate a)) ≡ a
rotateCubed (ternary-address c xs) =
  cong (λ c' → ternary-address c' xs) (Horn.rotateSectorCubed c)

rotateChild : ∀ t a → rotate (child t a) ≡ child t (rotate a)
rotateChild t (ternary-address c xs) = refl

data TernaryWord : Set where
  identityWord : TernaryWord
  meridian : TernaryAddress → TernaryWord
  inverse : TernaryWord → TernaryWord
  multiply : TernaryWord → TernaryWord → TernaryWord

commutator : TernaryWord → TernaryWord → TernaryWord
commutator a b =
  multiply (multiply (multiply a b) (inverse a)) (inverse b)

refineMeridian : TernaryAddress → TernaryWord
refineMeridian a =
  multiply
    (commutator (meridian (child BT.neg a))
                (meridian (child BT.zero a)))
    (commutator (meridian (child BT.zero a))
                (meridian (child BT.pos a)))

refineWord : TernaryWord → TernaryWord
refineWord identityWord = identityWord
refineWord (meridian a) = refineMeridian a
refineWord (inverse x) = inverse (refineWord x)
refineWord (multiply x y) = multiply (refineWord x) (refineWord y)

rotateWord : TernaryWord → TernaryWord
rotateWord identityWord = identityWord
rotateWord (meridian a) = meridian (rotate a)
rotateWord (inverse x) = inverse (rotateWord x)
rotateWord (multiply x y) = multiply (rotateWord x) (rotateWord y)

rotateWordCubed : ∀ w →
  rotateWord (rotateWord (rotateWord w)) ≡ w
rotateWordCubed identityWord = refl
rotateWordCubed (meridian a) = cong meridian (rotateCubed a)
rotateWordCubed (inverse w) = cong inverse (rotateWordCubed w)
rotateWordCubed (multiply a b) =
  cong₂ multiply (rotateWordCubed a) (rotateWordCubed b)

rotationRefinementCommutes : ∀ w →
  rotateWord (refineWord w) ≡ refineWord (rotateWord w)
rotationRefinementCommutes identityWord = refl
rotationRefinementCommutes (meridian (ternary-address c xs)) = refl
rotationRefinementCommutes (inverse w) =
  cong inverse (rotationRefinementCommutes w)
rotationRefinementCommutes (multiply a b) =
  cong₂ multiply
    (rotationRefinementCommutes a)
    (rotationRefinementCommutes b)

refineN : Nat → TernaryWord → TernaryWord
refineN zero w = w
refineN (suc n) w = refineWord (refineN n w)

rotationCommutesAllTernaryStages : ∀ n w →
  rotateWord (refineN n w) ≡ refineN n (rotateWord w)
rotationCommutesAllTernaryStages zero w = refl
rotationCommutesAllTernaryStages (suc n) w =
  trans
    (rotationRefinementCommutes (refineN n w))
    (cong refineWord (rotationCommutesAllTernaryStages n w))

-- The following two abstract statements are NOT passed as Agda
-- postulates: they require separate normal-form and colimit objects.
-- The script alexander_horned_balanced_ternary_commutator_tower.py
-- supplies the exact normal-form argument and destructive tests.
-- In particular this ternary source is NOT identified with
-- Hatcher's actual geometric pi1 or the original 2I target map.
