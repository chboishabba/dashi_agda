module DASHI.Analysis.BishopConvergentDoubleTailExact where

------------------------------------------------------------------------
-- DOUBLE-SUBSEQUENCE TAIL OF A CONVERGENT BISHOP SEQUENCE VANISHES
--
-- DASHI CONTRIBUTION
--
-- If x_n -> L then
--
--   x_(2n) - x_n -> 0.
--
-- This is the exact tail shape consumed by the finite Cauchy-wing bound.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

double : Nat → Nat
double zero = zero
double (suc n) = suc (suc (double n))

doubleStrict : ∀ n → double n Nat.< double (suc n)
doubleStrict n = Nat.s≤s (NatP.n≤1+n (double n))

doubleSubsequence :
  (sequence : Nat → BishopReal.ℝ) →
  (λ index → sequence (double index))
  BishopSequence.SubsequenceOf
  sequence
doubleSubsequence sequence =
  BishopSequence.subseq*
    ( double
    , (λ index → BishopP.≃-refl)
    , doubleStrict
    )

doubleSubsequenceConverges :
  ∀ {sequence : Nat → BishopReal.ℝ}
    {limit : BishopReal.ℝ} →
  BishopSequence._ConvergesTo_ sequence limit →
  BishopSequence._ConvergesTo_
    (λ index → sequence (double index))
    limit
doubleSubsequenceConverges {sequence} {limit} converges =
  BishopSequence.xₙ→x∧x≃y⇒xₙ→y
    (BishopSequence.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
      (doubleSubsequence sequence)
      (limit , converges))
    BishopP.≃-refl

doubleTailConvergesZero :
  ∀ {sequence : Nat → BishopReal.ℝ}
    {limit : BishopReal.ℝ} →
  BishopSequence._ConvergesTo_ sequence limit →
  BishopSequence._ConvergesTo_
    (λ index →
      BishopReal._-_
        (sequence (double index))
        (sequence index))
    BishopReal.0ℝ
doubleTailConvergesZero {sequence} {limit} converges =
  BishopSequence.xₙ→x∧x≃y⇒xₙ→y
    (BishopSequence.xₙ+yₙ→x₀+y₀
      (limit , doubleSubsequenceConverges converges)
      (BishopReal.- limit ,
        BishopSequence.-xₙ→-x₀ (limit , converges)))
    (BishopP.+-inverseʳ limit)
