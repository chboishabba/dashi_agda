{-# OPTIONS --safe #-}
module DASHI.Quantum.TSVF2017ComplexEnvironmentRobustnessExact where

-- PRIMARY THEOREM / EXACT 2017 QUANTUM MAX-CUT
--
-- Aharonov, Cohen, Landsberger, Entropy 19(3):111 (2017), Eq.22--25:
-- an already selected BES branch and many independent environment records
-- may give a large right/wrong retrodictive probability ratio.
--
-- ORIGINAL source owners, not replaced:
--   DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact
--   DASHI.Quantum.TSVFComplexGammaProductBornExact
--   DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore
--   DASHI.Quantum.TSVF
--   DASHI.Physics.Foundations.BidirectionallyAdmissibleHistoryFibreExact
--
-- This new exact finite-complex theorem:
-- (1) uses an ACTUAL Hermitian two-level rational-complex inner product;
-- (2) forms an ACTUAL k-fold independent environment overlap amplitude,
--     not a guessed decaying overlap parameter;
-- (3) uses real complex lists gamma_R,gamma_W and multiplies amplitudes;
-- (4) proves the Born wrong amplitude norm factors into the disturbed
--     complex gamma product norm and the k-fold environment overlap norm;
-- (5) proves the two alternative Born weights obey the CORRECT
--     right-to-wrong odds cross-product equation, without dividing by zero;
-- (6) proves both Born masses nonnegative from existing rational square
--     nonnegativity; the normalized binary ratio requires strictly
--     positive *selected total*, made explicit rather than assumed for
--     all possible postselections;
-- (7) gives a phase-sensitive no-go for reading the unsquared complex
--     gamma quotient as a real positive probability ratio.
--
-- The physical same-source 2017 pointer dynamics, true environment
-- disturbance product, actual unitary field Hilbert source, their exact
-- Eq.25 shorthand conventions, continuum limit and P07 Lorentz/OS clock
-- remain UNCONSTRUCTED. This is a finite complex-algebraic model, not
-- the Clay Yang-Mills theorem or empirical macroscopic time reversal.
--
-- No local postulates, holes or termination overrides.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as C
import DASHI.Quantum.TSVFComplexGammaProductBornExact as Gamma
import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Order

------------------------------------------------------------------------
-- Real finite 2D complex vector carrier, not just a scalar "overlap" label.
------------------------------------------------------------------------

record ComplexPointerRecord : Set where
  constructor pointerRecord
  field
    first second : C.RationalComplex

open ComplexPointerRecord public

hermitianPair :
  ComplexPointerRecord → ComplexPointerRecord → C.RationalComplex
hermitianPair left right =
  C._+c_
    (C._*c_ (C.conjugateC (first left)) (first right))
    (C._*c_ (C.conjugateC (second left)) (second right))

-- Every environmental site contributes a genuine Hermitian scalar.
-- The k-fold product corresponds to a tensor product of k identical
-- independent two-level environments.
complexPower : C.RationalComplex → Nat → C.RationalComplex
complexPower alpha zero = C.oneC
complexPower alpha (suc k) = C._*c_ alpha (complexPower alpha k)

rationalPower : ℚ → Nat → ℚ
rationalPower alpha zero = 1ℚ
rationalPower alpha (suc k) = alpha * rationalPower alpha k

complexPowerBornIsBornPower :
  (alpha : C.RationalComplex) (k : Nat) →
  C.complexNormSq (complexPower alpha k)
  ≡ rationalPower (C.complexNormSq alpha) k
complexPowerBornIsBornPower alpha zero = solve []
complexPowerBornIsBornPower alpha (suc k) =
  trans
    (C.complexNormMultiplicative alpha (complexPower alpha k))
    (cong (λ q → C.complexNormSq alpha * q)
      (complexPowerBornIsBornPower alpha k))

environmentOverlapAmplitude :
  (right wrong : ComplexPointerRecord) →
  Nat → C.RationalComplex
environmentOverlapAmplitude right wrong k =
  complexPower (hermitianPair right wrong) k

environmentBornOverlap :
  (right wrong : ComplexPointerRecord) →
  Nat → ℚ
environmentBornOverlap right wrong k =
  C.complexNormSq (environmentOverlapAmplitude right wrong k)

environmentOverlapIsProductRate :
  (right wrong : ComplexPointerRecord) (k : Nat) →
  environmentBornOverlap right wrong k
  ≡ rationalPower (C.complexNormSq (hermitianPair right wrong)) k
environmentOverlapIsProductRate right wrong k =
  complexPowerBornIsBornPower (hermitianPair right wrong) k

------------------------------------------------------------------------
-- Real physical amplitude algebra for two *postselected* channels.
-- The site records and the gamma lists are actual complex numbers.
-- A real physical source must still prove that these are THE states
-- obtained from the selected TSVF propagation/measurement dynamics.
------------------------------------------------------------------------

rightAmplitude :
  List C.RationalComplex → C.RationalComplex
rightAmplitude = Gamma.complexGammaProduct

wrongAmplitude :
  List C.RationalComplex →
  ComplexPointerRecord → ComplexPointerRecord →
  Nat → C.RationalComplex
wrongAmplitude gammas right wrong k =
  C._*c_ (Gamma.complexGammaProduct gammas)
    (environmentOverlapAmplitude right wrong k)

rightBorn :
  List C.RationalComplex → ℚ
rightBorn gammas = C.complexNormSq (rightAmplitude gammas)

wrongBorn :
  List C.RationalComplex →
  ComplexPointerRecord → ComplexPointerRecord →
  Nat → ℚ
wrongBorn gammas right wrong k =
  C.complexNormSq (wrongAmplitude gammas right wrong k)

rightBornIsComplexGammaWeight :
  (gammas : List C.RationalComplex) →
  rightBorn gammas ≡ Gamma.complexGammaBornWeight gammas
rightBornIsComplexGammaWeight =
  Gamma.complexGammaBornWeightIsNormOfProduct

wrongBornExact2017Factorization :
  (gammas : List C.RationalComplex)
  (right wrong : ComplexPointerRecord) (k : Nat) →
  wrongBorn gammas right wrong k
  ≡
  Gamma.complexGammaBornWeight gammas
    * environmentBornOverlap right wrong k
wrongBornExact2017Factorization gammas right wrong k =
  trans
    (C.complexNormMultiplicative
      (Gamma.complexGammaProduct gammas)
      (environmentOverlapAmplitude right wrong k))
    (cong (λ x → x * environmentBornOverlap right wrong k)
      (Gamma.complexGammaBornWeightIsNormOfProduct gammas))

-- Literal complex amplitude factors are squared ONCE, at the Born
-- probability step. Exact cross multiplication is valid even if a
-- wrong amplitude is zero, unlike a naive denominator-based ratio.
rightWrongBornRatioCross :
  (rightGammas wrongGammas : List C.RationalComplex)
  (right wrong : ComplexPointerRecord) (k : Nat) →
  rightBorn rightGammas
    * (Gamma.complexGammaBornWeight wrongGammas
        * environmentBornOverlap right wrong k)
  ≡
  wrongBorn wrongGammas right wrong k
    * Gamma.complexGammaBornWeight rightGammas
rightWrongBornRatioCross rightGammas wrongGammas right wrong k
  rewrite rightBornIsComplexGammaWeight rightGammas
        | wrongBornExact2017Factorization wrongGammas right wrong k =
  ℚₚ.*-comm
    (Gamma.complexGammaBornWeight rightGammas)
    (Gamma.complexGammaBornWeight wrongGammas
      * environmentBornOverlap right wrong k)

------------------------------------------------------------------------
-- Nonnegativity is DERIVED from the ORIGINAL rational real square law.
------------------------------------------------------------------------

complexBornNonnegative :
  (amplitude : C.RationalComplex) →
  0ℚ ≤ C.complexNormSq amplitude
complexBornNonnegative (C.complex a b) =
  Order.addNonnegative
    (Order.squareNonnegative a)
    (Order.squareNonnegative b)

rightBornNonnegative :
  (gammas : List C.RationalComplex) →
  0ℚ ≤ rightBorn gammas
rightBornNonnegative gammas =
  complexBornNonnegative (rightAmplitude gammas)

wrongBornNonnegative :
  (gammas : List C.RationalComplex)
  (right wrong : ComplexPointerRecord) (k : Nat) →
  0ℚ ≤ wrongBorn gammas right wrong k
wrongBornNonnegative gammas right wrong k =
  complexBornNonnegative (wrongAmplitude gammas right wrong k)

totalBorn :
  List C.RationalComplex → List C.RationalComplex →
  ComplexPointerRecord → ComplexPointerRecord → Nat → ℚ
totalBorn rightGammas wrongGammas right wrong k =
  rightBorn rightGammas + wrongBorn wrongGammas right wrong k

totalBornNonnegative :
  (rightGammas wrongGammas : List C.RationalComplex)
  (right wrong : ComplexPointerRecord) (k : Nat) →
  0ℚ ≤ totalBorn rightGammas wrongGammas right wrong k
totalBornNonnegative rightGammas wrongGammas right wrong k =
  Order.addNonnegative
    (rightBornNonnegative rightGammas)
    (wrongBornNonnegative wrongGammas right wrong k)

-- Physical ABL fractions are only admissible if this total is STRICTLY
-- positive. Never call two orthogonal postselected branches a probability.
record PositiveSelected2017Total
    (rightGammas wrongGammas : List C.RationalComplex)
    (right wrong : ComplexPointerRecord) (k : Nat) : Set where
  field
    totalStrictlyPositive :
      0ℚ < totalBorn rightGammas wrongGammas right wrong k

-- Native probability-numerator normalization, not a postulated equality.
selectedNumeratorsSumToSameTotal :
  (rightGammas wrongGammas : List C.RationalComplex)
  (right wrong : ComplexPointerRecord) (k : Nat) →
  rightBorn rightGammas + wrongBorn wrongGammas right wrong k
    ≡ totalBorn rightGammas wrongGammas right wrong k
selectedNumeratorsSumToSameTotal rightGammas wrongGammas right wrong k = refl

------------------------------------------------------------------------
-- Sharp source ambiguity: 2017 Eq.23/24 names complex overlap gamma,
-- while printed Eq.25 displays unsquared gamma products in a
-- *probability* ratio. Absent an implicit Born-weight convention,
-- literal unsquared complex gamma ratios are not universally probabilities.
--
-- i/1 is a counterexample: amplitude ratio i, Born-weight ratio 1.
------------------------------------------------------------------------

imaginaryGamma : C.RationalComplex
imaginaryGamma = C.complex 0ℚ 1ℚ

imaginaryGammaBornIsOne :
  C.complexNormSq imaginaryGamma ≡ 1ℚ
imaginaryGammaBornIsOne = solve []

unitGammaBornIsOne :
  C.complexNormSq C.oneC ≡ 1ℚ
unitGammaBornIsOne = solve []

imaginaryAndUnitGammaHaveSameBornWeight :
  C.complexNormSq imaginaryGamma ≡ C.complexNormSq C.oneC
imaginaryAndUnitGammaHaveSameBornWeight =
  trans imaginaryGammaBornIsOne (sym unitGammaBornIsOne)

imaginaryGammaIsNotUnitComplex :
  imaginaryGamma ≡ C.oneC → ⊥
imaginaryGammaIsNotUnitComplex ()

-- This counterexample is about interpreting the *printed* amplitude
-- ratio literally as a probability, not a claim the authors assumed
-- arbitrary phases in the actual physical branch model.
