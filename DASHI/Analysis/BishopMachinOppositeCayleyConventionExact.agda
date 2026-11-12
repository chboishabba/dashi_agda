{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopMachinOppositeCayleyConventionExact where

------------------------------------------------------------------------
-- Exact source-consistent convention bridge for the user-supplied
-- inverse Cayley phase, not a new proof of Bishop atan equality.
--
-- Original DASHI phase:   C+(t)=(1+it)/(1-it), phase product = +i.
-- Opposite convention:    C-(t)=(1-it)/(1+it), phase product = -i.
-- For REAL t, C-(t) = conjugate C+(t).
--
-- Reuse the exact original Q[i] source group, no floating arithmetic,
-- imaginary atan, logarithm, new complex carrier or branch choice.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
  using (sym; trans; cong; cong₂)
open import Data.Rational.Base using (0ℚ; 1ℚ; -_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD
import DASHI.Foundations.BishopMachinExistingCayleyReuseExact as Original

oppositeFivePhase opposite239Phase : CD.RationalComplex
oppositeFivePhase = CD.conjugateC Original.fivePhase
opposite239Phase = CD.conjugateC Original.twoHundredThirtyNinePhase

oppositeFivePhaseSquared : CD.RationalComplex
oppositeFivePhaseSquared =
  CD._*c_ oppositeFivePhase oppositeFivePhase

oppositeFivePhaseFourth : CD.RationalComplex
oppositeFivePhaseFourth =
  CD._*c_ oppositeFivePhaseSquared oppositeFivePhaseSquared

-- The exact inverse-convention phase is a product, not a definition
-- by conj of the desired final answer.
oppositeMachinQuarterPhase : CD.RationalComplex
oppositeMachinQuarterPhase =
  CD._*c_
    oppositeFivePhaseFourth
    (CD.conjugateC opposite239Phase)

rationalComplexMultiplicationCommutative :
  (left right : CD.RationalComplex) →
  CD._*c_ left right ≡ CD._*c_ right left
rationalComplexMultiplicationCommutative
    (CD.complex a b) (CD.complex c d) =
  CD.complexExt Ring.solve-∀ Ring.solve-∀

oppositeSquareIsConjugate :
  oppositeFivePhaseSquared
  ≡ CD.conjugateC Original.fivePhaseSquared
oppositeSquareIsConjugate =
  sym (CD.complexConjugateReversesProduct
    Original.fivePhase Original.fivePhase)

oppositeFourthIsConjugate :
  oppositeFivePhaseFourth
  ≡ CD.conjugateC Original.fivePhaseFourth
oppositeFourthIsConjugate =
  trans
    (cong₂ CD._*c_
      oppositeSquareIsConjugate
      oppositeSquareIsConjugate)
    (sym (CD.complexConjugateReversesProduct
      Original.fivePhaseSquared Original.fivePhaseSquared))

opposite239DoubleConjugate :
  CD.conjugateC opposite239Phase
  ≡ Original.twoHundredThirtyNinePhase
opposite239DoubleConjugate =
  CD.complexConjugateInvolutive
    Original.twoHundredThirtyNinePhase

-- Composition of the two ORIGINAL selected half-angles, with
-- the corrected sign. The order reversal under conjugation is
-- cancelled ONLY by commutativity in the original Q[i] subalgebra.
oppositeQuarterIsConjugateOriginal :
  oppositeMachinQuarterPhase
  ≡ CD.conjugateC Original.machinQuarterCayleyPhase
oppositeQuarterIsConjugateOriginal =
  trans
    (cong₂ CD._*c_
      oppositeFourthIsConjugate
      refl)
    (trans
      (rationalComplexMultiplicationCommutative
        (CD.conjugateC Original.fivePhaseFourth)
        (CD.conjugateC opposite239Phase))
      (sym (CD.complexConjugateReversesProduct
        Original.fivePhaseFourth
        (CD.conjugateC Original.twoHundredThirtyNinePhase))))

oppositeMachinQuarterIsMinusImaginaryUnit :
  oppositeMachinQuarterPhase ≡ CD.complex 0ℚ (- 1ℚ)
oppositeMachinQuarterIsMinusImaginaryUnit =
  trans
    oppositeQuarterIsConjugateOriginal
    (cong CD.conjugateC
      Original.originalComplexMachinQuarterCayleyIsImaginaryUnit)

-- Reversing the selected Cayley convention does not prove
-- exp_C(±2i atan_B(t)) ≈ C±(t): those remain ORIGINAL Bishop
-- analytic same-object evaluation obligations.
