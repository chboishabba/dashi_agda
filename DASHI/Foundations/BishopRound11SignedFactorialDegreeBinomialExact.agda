{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopRound11SignedFactorialDegreeBinomialExact where

------------------------------------------------------------------------
-- K05 TERMINAL: ACTUAL ALL-N ROUND11 MIXED SIGNED FACTORIAL
-- BINOMIAL COEFFICIENTS, ON ORIGINAL BISHOP REAL/CPLX CARRIERS.
--
-- The only mathematical input is the ORIGINAL all-degree Bishop
-- exp(x+y) finite Cauchy theorem. No trig addition, complex
-- exponential multiplication, or separate coefficient law is
-- postulated here.
--
-- Original cosine/sine:
--   c_n(x) = (-1)^n x^(2n)/(2n)!
--   s_n(x) = (-1)^n x^(2n+1)/(2n+1)!
--
-- For every n, the two genuine selected source identities:
--  C_n(c(x),c(y)) - C_(n-1)(s(x),s(y)) = c_n(x+y)
--  C_n(c(x),s(y)) + C_n(s(x),c(y))     = s_n(x+y).
-- Here C_(-1) = 0. Unlike the false uncorrected grouped
-- coefficient formula, the odd/odd index is shifted by one.
--
-- The source graph pays this by:
--  * original Round11 term = (-1)^n expTerm(x,2n or 2n+1);
--  * Nat bounded Fin even/odd reindex of ORIGINAL exp Cauchy;
--  * same pinned stdlib exponential factorial/binomial theorem;
--  * all-N signed Cauchy coefficient factoring on the true Fin set;
--  * original n=0 signed factorial source cases;
--  * original Bishop setoid real ring solver and sign successor.
--
-- The final original imaginary product and sine/cosine additions
-- are obtained via the ALREADY-PROVED original complex Cauchy
-- convergence and odd/odd boundary vanishing; not an assumed
-- trigonometric law.
--
-- Historical provenance: Newton, Cauchy, Machin, Bishop/Bridges;
-- Murray (2022), pinned Csimma Bishop Agda; DASHI original
-- Round11 sine/cosine and native Cauchy owners.
--
-- WARNING: --safe source written; Agda-2.9 elaboration and
-- transitive original TOE proof receipts must still be obtained.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_×_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as RP

import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Cutset
import DASHI.Analysis.BishopConcreteSineCosineFiniteTermDerivativeExact as Derivative
import DASHI.Analysis.BishopRound11NativeComplexRectangleExact as Native
import DASHI.Analysis.BishopSetoidComplexExact as Complex
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route

import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopRound11FiniteParityDegreeZeroExact as Base
import DASHI.Foundations.BishopRound11SignedFactorialExponentEncodingExact as Encoding
import DASHI.Foundations.BishopUnsignedFactorialCauchyParitySplitExact as Unsigned
import DASHI.Foundations.BishopSignTwistedFiniteCauchyCoefficientExact as Twist
import DASHI.Foundations.BishopGroupedCauchyParityTelescopeExact as Telescope

signedCosCosDegree :
  (inputs : Cutset.Round11BishopCutset) →
  (x y : R.ℝ) →
  (n : Nat) →
  R._≃_
    (Native.round11CosCosDegree inputs x y n)
    (R._*_
      (Terms.alternatingSign n)
      (Row.cauchyCoefficient
        (Unsigned.evenExp x) (Unsigned.evenExp y) n))
signedCosCosDegree inputs x y n =
  RP.≃-trans
    (Twist.rowCauchyCoefficientRespectsTerms
      (Terms.cosineSignedTerm x)
      (Terms.cosineSignedTerm y)
      (Twist.twist (Unsigned.evenExp x))
      (Twist.twist (Unsigned.evenExp y))
      (Encoding.cosineTermIsSignedExponentialEvenCoefficient x)
      (Encoding.cosineTermIsSignedExponentialEvenCoefficient y)
      n)
    (Twist.twistedCauchyCoefficient
      (Unsigned.evenExp x) (Unsigned.evenExp y) n)

signedSinSinDegree :
  (inputs : Cutset.Round11BishopCutset) →
  (x y : R.ℝ) →
  (n : Nat) →
  R._≃_
    (Native.round11SinSinDegree inputs x y n)
    (R._*_
      (Terms.alternatingSign n)
      (Row.cauchyCoefficient
        (Unsigned.oddExp x) (Unsigned.oddExp y) n))
signedSinSinDegree inputs x y n =
  RP.≃-trans
    (Twist.rowCauchyCoefficientRespectsTerms
      (Terms.sineSignedTerm x)
      (Terms.sineSignedTerm y)
      (Twist.twist (Unsigned.oddExp x))
      (Twist.twist (Unsigned.oddExp y))
      (Encoding.sineTermIsSignedExponentialOddCoefficient x)
      (Encoding.sineTermIsSignedExponentialOddCoefficient y)
      n)
    (Twist.twistedCauchyCoefficient
      (Unsigned.oddExp x) (Unsigned.oddExp y) n)

signedCosSinDegree :
  (inputs : Cutset.Round11BishopCutset) →
  (x y : R.ℝ) →
  (n : Nat) →
  R._≃_
    (Native.round11CosSinDegree inputs x y n)
    (R._*_
      (Terms.alternatingSign n)
      (Row.cauchyCoefficient
        (Unsigned.evenExp x) (Unsigned.oddExp y) n))
signedCosSinDegree inputs x y n =
  RP.≃-trans
    (Twist.rowCauchyCoefficientRespectsTerms
      (Terms.cosineSignedTerm x)
      (Terms.sineSignedTerm y)
      (Twist.twist (Unsigned.evenExp x))
      (Twist.twist (Unsigned.oddExp y))
      (Encoding.cosineTermIsSignedExponentialEvenCoefficient x)
      (Encoding.sineTermIsSignedExponentialOddCoefficient y)
      n)
    (Twist.twistedCauchyCoefficient
      (Unsigned.evenExp x) (Unsigned.oddExp y) n)

signedSinCosDegree :
  (inputs : Cutset.Round11BishopCutset) →
  (x y : R.ℝ) →
  (n : Nat) →
  R._≃_
    (Native.round11SinCosDegree inputs x y n)
    (R._*_
      (Terms.alternatingSign n)
      (Row.cauchyCoefficient
        (Unsigned.oddExp x) (Unsigned.evenExp y) n))
signedSinCosDegree inputs x y n =
  RP.≃-trans
    (Twist.rowCauchyCoefficientRespectsTerms
      (Terms.sineSignedTerm x)
      (Terms.cosineSignedTerm y)
      (Twist.twist (Unsigned.oddExp x))
      (Twist.twist (Unsigned.evenExp y))
      (Encoding.sineTermIsSignedExponentialOddCoefficient x)
      (Encoding.cosineTermIsSignedExponentialEvenCoefficient y)
      n)
    (Twist.twistedCauchyCoefficient
      (Unsigned.oddExp x) (Unsigned.evenExp y) n)

originalEvenSignedFactorialDegree :
  (inputs : Cutset.Round11BishopCutset) →
  (x y : R.ℝ) →
  (n : Nat) →
  R._≃_
    (R._-_
      (Native.round11CosCosDegree inputs x y n)
      (Telescope.previousCoefficient
        (Native.round11SinSinDegree inputs x y) n))
    (Native.round11OriginalCosineSourceDegree inputs x y n)
originalEvenSignedFactorialDegree inputs x y zero =
  Base.originalEvenFactorialBinomialDegreeZero inputs x y
originalEvenSignedFactorialDegree inputs x y (suc m) =
  let
    n = suc m
    signOld = Terms.alternatingSign m
    evenPart = Row.cauchyCoefficient
      (Unsigned.evenExp x) (Unsigned.evenExp y) n
    oddPart = Row.cauchyCoefficient
      (Unsigned.oddExp x) (Unsigned.oddExp y) m
    source = R._+_ x y
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.+-cong
      (signedCosCosDegree inputs x y n)
      (RP.-‿cong (signedSinSinDegree inputs x y m)))
    (RP.≃-trans
      (RP.+-congˡ
        (R.-_ (R._*_ signOld oddPart))
        (RP.*-congʳ
          (Derivative.alternatingSignSuccessor m)))
      (RP.≃-trans
        (solve 3
          (λ s e o →
            ((⊝ s) ⊗ e) ⊖ (s ⊗ o)
            ⊜ (⊝ s) ⊗ (e ⊕ o))
          RP.≃-refl signOld evenPart oddPart)
        (RP.≃-trans
          (RP.*-congʳ
            (RP.≃-symm (Derivative.alternatingSignSuccessor m)))
          (RP.≃-trans
            (RP.*-congˡ
              (Unsigned.unsignedEvenExponentialCoefficientSuccessor
                x y m))
            (RP.≃-symm
              (Encoding.cosineTermIsSignedExponentialEvenCoefficient
                source n))))))

originalOddSignedFactorialDegree :
  (inputs : Cutset.Round11BishopCutset) →
  (x y : R.ℝ) →
  (n : Nat) →
  R._≃_
    (R._+_
      (Native.round11CosSinDegree inputs x y n)
      (Native.round11SinCosDegree inputs x y n))
    (Native.round11OriginalSineSourceDegree inputs x y n)
originalOddSignedFactorialDegree inputs x y n =
  let
    sign = Terms.alternatingSign n
    cosSinPart = Row.cauchyCoefficient
      (Unsigned.evenExp x) (Unsigned.oddExp y) n
    sinCosPart = Row.cauchyCoefficient
      (Unsigned.oddExp x) (Unsigned.evenExp y) n
    source = R._+_ x y
  in
  RP.≃-trans
    (RP.+-cong
      (signedCosSinDegree inputs x y n)
      (signedSinCosDegree inputs x y n))
    (RP.≃-trans
      (RP.≃-symm
        (RP.*-distribˡ-+ sign cosSinPart sinCosPart))
      (RP.≃-trans
        (RP.*-congˡ
          (Unsigned.unsignedOddExponentialCoefficient x y n))
        (RP.≃-symm
          (Encoding.sineTermIsSignedExponentialOddCoefficient
            source n))))

originalImaginaryExponentialMultiplicative :
  (inputs : Cutset.Round11BishopCutset) →
  (x y : R.ℝ) →
  let T = Route.round11MachinTranscendentals inputs
  in
  Complex._≈C_
    (Complex._*C_
      (Complex.expC T (Complex.pureImaginary x))
      (Complex.expC T (Complex.pureImaginary y)))
    (Complex.expC T (Complex.pureImaginary (R._+_ x y)))
originalImaginaryExponentialMultiplicative inputs x y =
  Native.round11ProductFromOriginalFactorialDegreeSplits
    inputs x y
    (originalEvenSignedFactorialDegree inputs x y)
    (originalOddSignedFactorialDegree inputs x y)

originalSineCosineAdditionFromNativeFactorials :
  (inputs : Cutset.Round11BishopCutset) →
  (x y : R.ℝ) →
  let T = Route.round11MachinTranscendentals inputs
  in
  Complex.BishopSineAdditionAt T x y
  ×
  Complex.BishopCosineAdditionAt T x y
originalSineCosineAdditionFromNativeFactorials inputs x y =
  Complex.imaginaryExponentialProductGivesAddition
    (Route.round11MachinTranscendentals inputs)
    x y
    (Complex.≈C-sym
      (originalImaginaryExponentialMultiplicative inputs x y))
