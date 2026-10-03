module DASHI.ComputerScience.TekumPositiveSourceSuccessorAnchorExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Integer.Base as ℤ using (+_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.Algebra.BalancedTernaryRankReconstructionExact as Rank
import DASHI.ComputerScience.TekumBalancedSuccessorExact as Succ
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumPositiveAnchorInjectiveExact as Positive
import DASHI.ComputerScience.TekumSourceAnchorCenterExact as Center
import DASHI.ComputerScience.TekumWidthAdmissibilityExact as Width

------------------------------------------------------------------------
-- POSITIVE SOURCE SUCCESSOR -> ADJACENT CORRECTED ANCHOR RANK
--
-- Proposition 4 is a statement about the source integer code.  For positive
-- finite words the corrected Definition-7 anchor has exact rank
--
--   source magnitude + alternating-midpoint magnitude.
--
-- Hence adjacent positive source magnitudes have adjacent anchor ranks.  This
-- owner pays that bridge independently of the parser/carry field split.
------------------------------------------------------------------------

successorNatCode :
  ∀ {n} {word : Vec Trit.Trit n} →
  Succ.HasSuccessor word →
  Positional.natCode (Succ.successorWord word)
  ≡ suc (Positional.natCode word)
successorNatCode {word = Trit.neg Data.Vec.∷ xs} Succ.negativeHead = refl
successorNatCode {word = Trit.zer Data.Vec.∷ xs} Succ.zeroHead = refl
successorNatCode {word = Trit.pos Data.Vec.∷ xs} (Succ.positiveCarry carry)
  rewrite successorNatCode carry =
  solve 1
    (λ n → con 3 :* (con 1 :+ n) := con 1 :+ (con 2 :+ (con 3 :* n)))
    refl (Positional.natCode xs)

successorRankStep :
  ∀ {n} {word : Vec Trit.Trit n} →
  Succ.HasSuccessor word →
  Data.Fin.Base.toℕ (Rank.rankWord (Succ.successorWord word))
  ≡ suc (Data.Fin.Base.toℕ (Rank.rankWord word))
successorRankStep {word = word} carry =
  trans
    (Rank.rankToNatCode (Succ.successorWord word))
    (trans
      (successorNatCode carry)
      (cong suc (sym (Rank.rankToNatCode word))))

positiveSourceStepRaisesAnchorRank :
  ∀ {n m}
  (even : Width.EvenWidth n)
  (left right : Vec Trit.Trit n) →
  BT.toInteger (BT.eval left) ≡ + (suc m) →
  BT.toInteger (BT.eval right) ≡ + (suc (suc m)) →
  Data.Fin.Base.toℕ (Rank.rankWord (Fixed.concreteAnchor right))
  ≡ suc (Data.Fin.Base.toℕ (Rank.rankWord (Fixed.concreteAnchor left)))
positiveSourceStepRaisesAnchorRank {m = m} even left right leftValue rightValue =
  trans
    (Positive.positiveConcreteAnchorRank even right rightValue)
    (trans
      arithmetic
      (cong suc (sym (Positive.positiveConcreteAnchorRank even left leftValue))))
  where
  c = Center.sourceCenterMagnitudeAt even

  arithmetic : suc (suc m) + c ≡ suc (suc m + c)
  arithmetic = refl

positiveSourceSuccessorAnchorsAreAdjacent :
  ∀ {n m}
  (even : Width.EvenWidth n)
  (left right : Vec Trit.Trit n) →
  BT.toInteger (BT.eval left) ≡ + (suc m) →
  BT.toInteger (BT.eval right) ≡ + (suc (suc m)) →
  Succ.HasSuccessor (Fixed.concreteAnchor left) →
  Succ.successorWord (Fixed.concreteAnchor left)
  ≡ Fixed.concreteAnchor right
positiveSourceSuccessorAnchorsAreAdjacent even left right leftValue rightValue carry =
  Positional.natCodeInjective natCodeEq
  where
  leftAnchor = Fixed.concreteAnchor left
  rightAnchor = Fixed.concreteAnchor right

  rankEq :
    Data.Fin.Base.toℕ (Rank.rankWord (Succ.successorWord leftAnchor))
    ≡ Data.Fin.Base.toℕ (Rank.rankWord rightAnchor)
  rankEq =
    trans
      (successorRankStep carry)
      (sym (positiveSourceStepRaisesAnchorRank even left right leftValue rightValue))

  natCodeEq :
    Positional.natCode (Succ.successorWord leftAnchor)
    ≡ Positional.natCode rightAnchor
  natCodeEq =
    trans
      (sym (Rank.rankToNatCode (Succ.successorWord leftAnchor)))
      (trans rankEq (Rank.rankToNatCode rightAnchor))
