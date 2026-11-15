module DASHI.Moonshine.Y443Monster3BTwelveDisjointExact where

------------------------------------------------------------------------
-- Exact cross-lane falsifier: the 12 nodes of the Y443 Coxeter diagram
-- are NOT the 6+6 standard Heisenberg/Weyl generators by name or count.
--
-- In DASHI's existing F3^6 Schrödinger model, the standard axis0
-- translation is order three and is NOT order two. Every Y443 node
-- must satisfy its involution relation x^2=1.
--
-- This does not rule out a NONTRIVIAL homomorphism or a different
-- involution model inside the Monster/normalizer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y

zeroState : H.X6
zeroState = H.x6 zer zer zer zer zer zer

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

negCannotEqualZero : neg ≡ zer → ⊥
negCannotEqualZero ()

axis0DoubleTranslationIsNotIdentity :
  H.translate H.axis0 (H.translate H.axis0 zeroState)
  ≡ zeroState → ⊥
axis0DoubleTranslationIsNotIdentity equality =
  negCannotEqualZero (cong H.x0 equality)

axis0TripleTranslationIsIdentity :
  H.translate H.axis0
    (H.translate H.axis0 (H.translate H.axis0 zeroState))
  ≡ zeroState
axis0TripleTranslationIsIdentity = refl

axis0TripleTranslationEverywhere :
  (state : H.X6) →
  H.translate H.axis0
    (H.translate H.axis0 (H.translate H.axis0 state))
  ≡ state
axis0TripleTranslationEverywhere (H.x6 zer b c d e f) = refl
axis0TripleTranslationEverywhere (H.x6 pos b c d e f) = refl
axis0TripleTranslationEverywhere (H.x6 neg b c d e f) = refl

-- Alongside the type-level disjointness in Y443CoxeterPresentationExact,
-- this is a computational obstruction to identifying the source generator
-- ACTIONS as involutions on the SAME six-trit carrier.
