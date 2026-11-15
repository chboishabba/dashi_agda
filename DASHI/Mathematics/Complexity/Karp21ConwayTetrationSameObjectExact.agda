module DASHI.Mathematics.Complexity.Karp21ConwayTetrationSameObjectExact where

------------------------------------------------------------------------
-- K01/K04: the genuine arbitrary-list Conway interpreter agrees on the
-- three-term positive-rank-2 fragment with DASHI's ORIGINAL triadic
-- recursive fibre tetration owner, not a replacement definition.
-- The zero middle-argument case is excluded by the positive domain.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.Karp21ConwayTotalChainExact as Chain
import DASHI.Cognition.RecursiveFibreTower as Fibre

powerSame : (a n : Nat) →
  Chain.power a n ≡ Fibre.pow a n
powerSame a zero = refl
powerSame a (suc n)
  rewrite powerSame a n = refl

iterateFibre :
  (a height : Nat) →
  Chain.iterate (Chain.power a) height 1
    ≡ Fibre.tetration a height
iterateFibre a zero = refl
iterateFibre a (suc height) =
  trans
    (cong (Chain.power a) (iterateFibre a height))
    (powerSame a (Fibre.tetration a height))

iterateShift :
  (f : Nat → Nat) (n seed : Nat) →
  Chain.iterate f n (f seed) ≡
    f (Chain.iterate f n seed)
iterateShift f zero seed = refl
iterateShift f (suc n) seed
  rewrite iterateShift f n seed = refl

conwayThreeIsOriginalTetration :
  (a height : Nat) →
  Chain.evaluate (a ∷ suc height ∷ 2 ∷ [])
    ≡ Fibre.tetration a (suc height)
conwayThreeIsOriginalTetration a height =
  trans
    (cong
      (Chain.iterate (Chain.power a) height)
      (sym (Chain.startOneInvariant a)))
    (trans
      (iterateShift (Chain.power a) height 1)
      (trans
        (cong (Chain.power a) (iterateFibre a height))
        (powerSame a (Fibre.tetration a height))))

triadicTwentySeven :
  Chain.evaluate (3 ∷ 2 ∷ 2 ∷ [])
    ≡ Fibre.tetration 3 2
triadicTwentySeven = conwayThreeIsOriginalTetration 3 1
