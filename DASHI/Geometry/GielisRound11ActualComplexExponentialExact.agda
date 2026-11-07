{-# OPTIONS --safe #-}
module DASHI.Geometry.GielisRound11ActualComplexExponentialExact where

------------------------------------------------------------------------
-- Original Round11 Bishop sine/cosine actually IS the imaginary-axis
-- value of the existing BishopSetoidComplexExact.expC, by the already
-- proven BishopExponentialPositiveOrderExact.bishopExpZero.
--
-- This is the SAME actual source object, not a new complex exp series
-- or a conditional sine/cosine alias. Both coordinates are proved
-- on vendored Bishop ℝ via original multiplicative congruence.
--
-- The selected pi is the already-constructed Machin Bishop real;
-- identifying it with the sine first positive zero/period remains
-- a DIFFERENT analytic proposition (not asserted here).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import Real as Bishop
import RealProperties as BishopP
import DASHI.Analysis.BishopSetoidComplexExact as Complex
import DASHI.Analysis.BishopRound11FactorDerivativeInterchangeExact as Round11
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Trig
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpZero
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Geometry.GielisBishopImaginaryExponentialReducerExact as Gielis

actualRound11ComplexTranscendentals :
  Round11.Round11FactorInterchangeProblem →
  Complex.BishopSetoidComplexTranscendentals
actualRound11ComplexTranscendentals P = record
  { Complex.dataSet = Round11.dataSet P
  ; Complex.trigIdentification = Round11.termIdentification P
  ; Complex.pi = Machin.bishopMachinPi
  }

actualImaginaryAxisArgument : Bishop.ℝ → Complex.BishopComplex
actualImaginaryAxisArgument angle =
  Complex.complex Bishop.0ℝ angle

actualRound11ExpCIsTrigPair :
  ∀ P angle →
  Complex._≈C_
    (Complex.expC
      (actualRound11ComplexTranscendentals P)
      (actualImaginaryAxisArgument angle))
    (Gielis.imaginaryAxisTrigExp (Round11.dataSet P) angle)
actualRound11ExpCIsTrigPair P angle =
  Complex.complex-equivalent
    (BishopP.≃-trans
      (BishopP.*-cong
        ExpZero.bishopExpZero
        BishopP.≃-refl)
      (BishopP.*-identityˡ
        (Trig.bishopCos (Round11.dataSet P) angle)))
    (BishopP.≃-trans
      (BishopP.*-cong
        ExpZero.bishopExpZero
        BishopP.≃-refl)
      (BishopP.*-identityˡ
        (Trig.bishopSin (Round11.dataSet P) angle)))

-- Explicit chosen pi object; NOT a claim that this constructive Machin
-- value has been identified with the first sine zero.
actualSelectedPi :
  ∀ P → Complex.pi (actualRound11ComplexTranscendentals P)
  ≡ Machin.bishopMachinPi
actualSelectedPi P = refl
