{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopMachinTwoPointCayleyCompositionExact where

------------------------------------------------------------------------
-- K05-PI: THE TWO *ACTUAL* BISHOP ATAN EVALUATIONS IMPLY THE
-- ORIGINAL MACHIN FIRST POSITIVE SINE ZERO, WITHOUT ANY EXTRA
-- IMAGINARY EXPONENTIAL MULTIPLICATIVITY ASSUMPTION.
--
-- Reuse, do not duplicate:
--   BishopMachinArctanConstructionExact: source atan at 1/5, 1/239.
--   BishopMachinQuarterAngleBranchExact: theta_M=4 atan(1/5)-atan(1/239).
--   BishopRound11SignedFactorialDegreeBinomialExact: ALL x,y exp product.
--   BishopMachinExistingCayleyReuseExact: C(1/5)^4 conj(C(1/239)) = i.
--   BishopMachinRationalCayleyToOriginalComplexExact: Q[i] -> Bishop C.
--   BishopMachinCayleyNativeProductFirstZeroExact: sign/first-zero consumer.
--
-- Only the TWO source-specific analytic equalities
--   exp_C(2i atan_B(1/5)) ~ C(1/5),
--   exp_C(2i atan_B(1/239)) ~ C(1/239)
-- remain inputs to this module. All other composition, conjugation,
-- angle algebra, and sine-zero logic below is literal proof transport.
-- The proof never selects a classical atan, new complex type, or
-- classical pi; no postulates or by-definition synthetic zeta.
--
-- Source-written, exact-head Agda-2.9 kernel check outstanding.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Analysis.BishopMachinRationalCayleyToOriginalComplexExact as Bridge
import DASHI.Analysis.BishopMachinCayleyHalfPhaseToFirstZeroExact as FirstFromCayley
import DASHI.Analysis.BishopMachinCayleyNativeProductFirstZeroExact as Native
import DASHI.Analysis.BishopMachinFirstPositiveSineZeroFromNativePhaseExact as First
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD
import DASHI.Foundations.BishopMachinExistingCayleyReuseExact as Cayley
import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Foundations.BishopMachinQuarterAngleBranchExact as Quarter
import DASHI.Analysis.BishopMachinQuarterPhaseQuadruplicationAlgebraExact as Quad
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as Parity
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp

atanFive atan239 : R.ℝ
atanFive = Atan.bishopAtanOneFifth
atan239 = Atan.bishopAtanOneTwoHundredThirtyNinth

double quadruple octuple : R.ℝ → R.ℝ
double x = R._+_ x x
quadruple x = double (double x)
octuple x = double (quadruple x)

expImag :
  Round11.Round11BishopCutset → R.ℝ → C.BishopComplex
expImag inputs x =
  C.expC
    (Route.round11MachinTranscendentals inputs)
    (C.pureImaginary x)

-- Precisely the TWO original Bishop-power-series evaluations we
-- must produce from the source arctan/log composition theorem.
OriginalAtanFiveCayleyEvaluation :
  Round11.Round11BishopCutset → Set
OriginalAtanFiveCayleyEvaluation inputs =
  C._≈C_
    (expImag inputs (double atanFive))
    (Bridge.embedOriginalComplex Cayley.fivePhase)

OriginalAtan239CayleyEvaluation :
  Round11.Round11BishopCutset → Set
OriginalAtan239CayleyEvaluation inputs =
  C._≈C_
    (expImag inputs (double atan239))
    (Bridge.embedOriginalComplex Cayley.twoHundredThirtyNinePhase)

nativeExpImagProduct :
  (inputs : Round11.Round11BishopCutset) →
  (x y : R.ℝ) →
  C._≈C_
    (expImag inputs (R._+_ x y))
    (C._*C_ (expImag inputs x) (expImag inputs y))
nativeExpImagProduct inputs x y =
  Native.originalNativeImaginaryExpProduct inputs x y

-- This uses *actual original Round11 parity*, not a separate
-- supposed inverse-exponential law. The sine is odd, cosine even;
-- exp_B(0) is the literal same factor on both sides.
nativeExpImagNegateIsConjugate :
  (inputs : Round11.Round11BishopCutset) →
  (x : R.ℝ) →
  C._≈C_
    (expImag inputs (R.-_ x))
    (C.conjugate (expImag inputs x))
nativeExpImagNegateIsConjugate inputs x =
  let
    dataSet = Round11.elementarySeries inputs
    expZero = Exp.bishopExp R.0ℝ
  in
  C.complex-equivalent
    (RP.*-cong RP.≃-refl
      (Parity.bishopCosNeg
        (Round11.round11ParityInputs inputs) x))
    (RP.≃-trans
      (RP.*-cong RP.≃-refl
        (Parity.bishopSinNeg
          (Round11.round11ParityInputs inputs) x))
      (RP.≃-symm
        (RP.neg-distribʳ-*
          expZero (E.bishopSin dataSet x))))

-- Native double composition; complex associativity is never assumed.
nativeDoubleExp :
  (inputs : Round11.Round11BishopCutset) →
  (x : R.ℝ) →
  C._≈C_
    (expImag inputs (double x))
    (C._*C_ (expImag inputs x) (expImag inputs x))
nativeDoubleExp inputs x = nativeExpImagProduct inputs x x

-- The previously selected rational multiplication is transported
-- through original C._*C_ by the *existing* ring morphism.
nativeFivePhaseSquared :
  (inputs : Round11.Round11BishopCutset) →
  OriginalAtanFiveCayleyEvaluation inputs →
  C._≈C_
    (expImag inputs (double (double atanFive)))
    (Bridge.embedOriginalComplex Cayley.fivePhaseSquared)
nativeFivePhaseSquared inputs fiveEvaluation =
  C.≈C-trans
    (nativeDoubleExp inputs (double atanFive))
    (C.≈C-trans
      (C.mulCongruent fiveEvaluation fiveEvaluation)
      (C.≈C-sym
        (Bridge.embedOriginalComplexMultiply
          Cayley.fivePhase Cayley.fivePhase)))

nativeFivePhaseFourth :
  (inputs : Round11.Round11BishopCutset) →
  OriginalAtanFiveCayleyEvaluation inputs →
  C._≈C_
    (expImag inputs (octuple atanFive))
    (Bridge.embedOriginalComplex Cayley.fivePhaseFourth)
nativeFivePhaseFourth inputs fiveEvaluation =
  C.≈C-trans
    (nativeDoubleExp inputs (quadruple atanFive))
    (C.≈C-trans
      (C.mulCongruent
        (nativeFivePhaseSquared inputs fiveEvaluation)
        (nativeFivePhaseSquared inputs fiveEvaluation))
      (C.≈C-sym
        (Bridge.embedOriginalComplexMultiply
          Cayley.fivePhaseSquared Cayley.fivePhaseSquared)))

native239ConjugatePhase :
  (inputs : Round11.Round11BishopCutset) →
  OriginalAtan239CayleyEvaluation inputs →
  C._≈C_
    (expImag inputs (R.-_ (double atan239)))
    (Bridge.embedOriginalComplex
      (CD.conjugateC Cayley.twoHundredThirtyNinePhase))
native239ConjugatePhase inputs local239 =
  C.≈C-trans
    (nativeExpImagNegateIsConjugate inputs (double atan239))
    (C.≈C-trans
      (C.conjugateCongruent local239)
      (C.≈C-sym
        (Bridge.embedOriginalComplexConjugate
          Cayley.twoHundredThirtyNinePhase)))

-- The literal selected source Machin quarter is theta_M=4a-b.
-- Therefore 2 theta_M=8a-2b. No symbolic pi or quotient transport.
originalDoubleQuarterIsCayleyAngleSum :
  R._≃_
    Quad.twiceQuarter
    (R._+_ (octuple atanFive) (R.-_ (double atan239)))
originalDoubleQuarterIsCayleyAngleSum =
  let open RP.ℝ-Solver in
  solve 2
    (λ a b →
      (((Κ (+ 4 / 1) ⊗ a) ⊖ b)
        ⊕ ((Κ (+ 4 / 1) ⊗ a) ⊖ b))
      ⊜
      (((((a ⊕ a) ⊕ (a ⊕ a))
          ⊕ ((a ⊕ a) ⊕ (a ⊕ a))))
        ⊕ (⊝ (b ⊕ b))))
    RP.≃-refl atanFive atan239

-- K05.PI's combined half-phase analytic input has been *derived*
-- from exactly the two original source arctangent evaluations.
-- The remaining product, conjugation, and 8a-2b arithmetic are
-- fully discharged in the selected Bishop complex.
nativeCombinedCayleyFromTwoOriginalAtanValues :
  (inputs : Round11.Round11BishopCutset) →
  OriginalAtanFiveCayleyEvaluation inputs →
  OriginalAtan239CayleyEvaluation inputs →
  FirstFromCayley.OriginalMachinCayleySameObjectEvaluation inputs
nativeCombinedCayleyFromTwoOriginalAtanValues
    inputs fiveEvaluation twoHundredThirtyNineEvaluation =
  C.≈C-trans
    (C.expCongruent
      (Route.round11MachinTranscendentals inputs)
      (C.complex-equivalent
        RP.≃-refl
        originalDoubleQuarterIsCayleyAngleSum))
    (C.≈C-trans
      (nativeExpImagProduct
        inputs (octuple atanFive) (R.-_ (double atan239)))
      (C.≈C-trans
        (C.mulCongruent
          (nativeFivePhaseFourth inputs fiveEvaluation)
          (native239ConjugatePhase
            inputs twoHundredThirtyNineEvaluation))
        (C.≈C-sym
          (Bridge.embedOriginalComplexMultiply
            Cayley.fivePhaseFourth
            (CD.conjugateC Cayley.twoHundredThirtyNinePhase)))))

-- The theorem consumers now do not require either the original
-- imaginary exponential product OR a free Machin quarter equality.
-- The two precise pointwise source analytic identities are the
-- *only* remaining mathematical K05-PI inputs.
originalMachinFirstPositiveSineZeroFromTwoAtanCayleyValues :
  (inputs : Round11.Round11BishopCutset) →
  OriginalAtanFiveCayleyEvaluation inputs →
  OriginalAtan239CayleyEvaluation inputs →
  First.SourceMachinFirstPositiveSineZero inputs
originalMachinFirstPositiveSineZeroFromTwoAtanCayleyValues
    inputs fiveEvaluation twoHundredThirtyNineEvaluation =
  Native.originalNativeFirstPositiveSineZeroFromCayley
    inputs
    (nativeCombinedCayleyFromTwoOriginalAtanValues
      inputs fiveEvaluation twoHundredThirtyNineEvaluation)
