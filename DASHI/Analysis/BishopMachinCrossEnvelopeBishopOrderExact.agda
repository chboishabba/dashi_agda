module DASHI.Analysis.BishopMachinCrossEnvelopeBishopOrderExact where

------------------------------------------------------------------------
-- K04b-DENOM: FIRST POSITIVE-DENOMINATOR / SAME-BISHOP-ORDER WELD.
--
-- Reuse the exact all-Nat cross-multiplied Machin remainder envelope,
-- the source-owned positive-Nat fraction-order theorem, and the
-- vendored Bishop rational embedding/order. No alternative real carrier.
--
-- This result is the canonical NORMALIZED cross-product certificate.
-- The still-open leaf is the literal equality of the two ORIGINAL
-- multi-denominator remainder fractions to this normal form before
-- common-denominator cancellation. Do not confuse them.
--
-- Machin 1706; Bishop/Bridges 1985; Murray 2022 arXiv:2205.08354.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_; _^_)
import Data.Nat.Properties as NatP
open import Data.Nat.Base as Nat using (_≤_; NonZero)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Integer.Solver renaming (module +-*-Solver to ℤSolver)
open ℤSolver using () renaming
  ( solve to Zsolve
  ; _:+_ to _⊕_
  ; _:*_ to _⊗_
  ; con to ZK
  ; _:=_ to _⊜_
  )
open +-*-Solver using (solve; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; cong)
open import Data.Rational.Unnormalised as Q using (ℚᵘ; _/_; _≤_; _≃_; _+_; *≡*)
open import Data.Integer.Base using (+_)

import Real as R
import RealProperties as RP
import Sequence as Seq
import Data.Rational.Unnormalised.Properties as QP

import DASHI.Analysis.BishopMachinGeometricEnvelopeNatExact as Cross
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Stage
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as Fractions

normalizedNumerator normalizedDenominator : Nat → Nat
normalizedNumerator n =
  3824 * Cross.pow57121 n + 20 * Cross.pow25 n
normalizedDenominator n =
  suc (2 * n) * (4780 * Cross.pow57121 n)

normalizedNumeratorBelowDenominator : (n : Nat) →
  normalizedNumerator n ≤ normalizedDenominator n
normalizedNumeratorBelowDenominator n =
  Cross.machinGeometricEnvelopeCrossMultiplied n

-- Explicit use of the SAME unnormalised rational backend employed
-- by the Bishop library. Both denominators are the canonical 1.
-- The remaining multi-denominator cancellation is separate.
normalizedRationalOrder : (n : Nat) →
  (+ normalizedNumerator n / 1)
    Q.≤ (+ normalizedDenominator n / 1)
normalizedRationalOrder n =
  Fractions.natFractionLe
    (NatP.*-mono-≤
      (normalizedNumeratorBelowDenominator n)
      NatP.≤-refl)

normalizedBishopOrder : (n : Nat) →
  R._≤_
    (R._⋆ (+ normalizedNumerator n / 1))
    (R._⋆ (+ normalizedDenominator n / 1))
normalizedBishopOrder n =
  RP.p≤q⇒p⋆≤q⋆
    (+ normalizedNumerator n / 1)
    (+ normalizedDenominator n / 1)
    (normalizedRationalOrder n)

------------------------------------------------------------------------
-- K04b-DENOM: ORIGINAL THREE-FACTOR COMMON-DENOMINATOR CERTIFICATE.
--
-- The omitted source magnitudes are
-- 16 / [(2n+1) 5 25^n] + 4 / [(2n+1) 239 57121^n].
-- Their shared integer denominator is exactly
--
-- D_n = (2n+1) * 5 * 239 * 25^n * 57121^n,
--
-- with numerator 16*239*57121^n + 4*5*25^n.
-- The target 4/25^n, after clearing D_n*25^n, becomes
--
--   numerator * 25^n <= 4 * D_n .
--
-- This theorem proves that literal denominator-cleared arithmetic
-- directly from the original all-index Nat cross certificate.
-- Proving the two rational-addition/source-term setoid equalities
-- and positivity of each composite unnormalised denominator is
-- a separate and explicitly tracked final K04b transport leaf.
------------------------------------------------------------------------

sourceCommonDenominator : Nat → Nat
sourceCommonDenominator n =
  (((suc (2 * n) * 5) * 239) * Cross.pow25 n) *
    Cross.pow57121 n

sourceCommonDenominatorFactor :
  (odd p q : Nat) →
  (odd * (4780 * q)) * p ≡
  4 * (((odd * 5) * 239 * p) * q)
sourceCommonDenominatorFactor =
  solve 3
    (λ odd p q →
      ((odd :* (con 4780 :* q)) :* p)
      := (con 4 :*
          ((((odd :* con 5) :* con 239) :* p) :* q)))
    refl

sourceCommonDenominatorCleared : (n : Nat) →
  (normalizedNumerator n * Cross.pow25 n)
  ≤ (4 * sourceCommonDenominator n)
sourceCommonDenominatorCleared n =
  subst
    (λ bound → normalizedNumerator n * Cross.pow25 n ≤ bound)
    (sourceCommonDenominatorFactor
      (suc (2 * n))
      (Cross.pow25 n)
      (Cross.pow57121 n))
    (NatP.*-mono-≤
      (normalizedNumeratorBelowDenominator n)
      NatP.≤-refl)


------------------------------------------------------------------------
-- K04b-DENOM: POSITIVE ORIGINAL VARIABLE DENOMINATORS.
-- These are constructive NonZero witnesses, NOT informal claims
-- that positive powers/products are nonzero.
------------------------------------------------------------------------

pow25NonZero : (n : Nat) → Nat.NonZero (Cross.pow25 n)
pow25NonZero n = NatP.m^n≢0 25 n

pow57121NonZero : (n : Nat) → Nat.NonZero (Cross.pow57121 n)
pow57121NonZero n = NatP.m^n≢0 57121 n

oddFiveNonZero : (n : Nat) →
  Nat.NonZero (suc (2 * n) * 5)
oddFiveNonZero n = NatP.m*n≢0 (suc (2 * n)) 5

odd239NonZero : (n : Nat) →
  Nat.NonZero (suc (2 * n) * 239)
odd239NonZero n = NatP.m*n≢0 (suc (2 * n)) 239

sourceFiveDenominator : Nat → Nat
sourceFiveDenominator n =
  (suc (2 * n) * 5) * Cross.pow25 n

source239Denominator : Nat → Nat
source239Denominator n =
  (suc (2 * n) * 239) * Cross.pow57121 n

sourceFiveDenominatorNonZero : (n : Nat) →
  Nat.NonZero (sourceFiveDenominator n)
sourceFiveDenominatorNonZero n =
  NatP.m*n≢0 (suc (2 * n) * 5) (Cross.pow25 n)
    {{oddFiveNonZero n}} {{pow25NonZero n}}

source239DenominatorNonZero : (n : Nat) →
  Nat.NonZero (source239Denominator n)
source239DenominatorNonZero n =
  NatP.m*n≢0 (suc (2 * n) * 239) (Cross.pow57121 n)
    {{odd239NonZero n}} {{pow57121NonZero n}}

sourceOddFive239NonZero : (n : Nat) →
  Nat.NonZero ((suc (2 * n) * 5) * 239)
sourceOddFive239NonZero n =
  NatP.m*n≢0 (suc (2 * n) * 5) 239
    {{oddFiveNonZero n}}

sourceCommonDenominatorNonZero : (n : Nat) →
  Nat.NonZero (sourceCommonDenominator n)
sourceCommonDenominatorNonZero n =
  NatP.m*n≢0
    (((suc (2 * n) * 5) * 239) * Cross.pow25 n)
    (Cross.pow57121 n)
    {{NatP.m*n≢0
        ((suc (2 * n) * 5) * 239)
        (Cross.pow25 n)
        {{sourceOddFive239NonZero n}}
        {{pow25NonZero n}}}}
    {{pow57121NonZero n}}

------------------------------------------------------------------------
-- LITERAL UNNORMALISED RATIONAL EXPRESSIONS:
--
-- source e_n = 16 / [(2n+1)5 25^n]
--            + 4 / [(2n+1)239 57121^n]
-- common e_n = (3824 57121^n + 20 25^n) /
--            [(2n+1)5 239 25^n 57121^n]
--
-- Both rational constructors use actual variable NonZero witnesses.
------------------------------------------------------------------------

sourceOmittedRationalEnvelope : Nat → Q.ℚᵘ
sourceOmittedRationalEnvelope n =
  let
    instance
      fiveNZ = sourceFiveDenominatorNonZero n
      otherNZ = source239DenominatorNonZero n
  in
  (+ 16 / sourceFiveDenominator n)
  Q.+ (+ 4 / source239Denominator n)

sourceCommonRationalEnvelope : Nat → Q.ℚᵘ
sourceCommonRationalEnvelope n =
  let
    instance
      commonNZ = sourceCommonDenominatorNonZero n
  in
  + normalizedNumerator n / sourceCommonDenominator n

sourceGeometricRationalEnvelope : Nat → Q.ℚᵘ
sourceGeometricRationalEnvelope n =
  let
    instance
      powerNZ = pow25NonZero n
  in
  + 4 / Cross.pow25 n

-- This is the *original source denominator* cross comparison, not
-- the artificial denominator-one normalization.
sourceCommonRationalBelowGeometric : (n : Nat) →
  Q._≤_
    (sourceCommonRationalEnvelope n)
    (sourceGeometricRationalEnvelope n)
sourceCommonRationalBelowGeometric n =
  let
    instance
      commonNZ = sourceCommonDenominatorNonZero n
      powerNZ = pow25NonZero n
  in
  Fractions.natFractionLe
    (sourceCommonDenominatorCleared n)

sourceCommonBishopBelowGeometric : (n : Nat) →
  R._≤_
    (R._⋆ (sourceCommonRationalEnvelope n))
    (R._⋆ (sourceGeometricRationalEnvelope n))
sourceCommonBishopBelowGeometric n =
  RP.p≤q⇒p⋆≤q⋆
    (sourceCommonRationalEnvelope n)
    (sourceGeometricRationalEnvelope n)
    (sourceCommonRationalBelowGeometric n)


------------------------------------------------------------------------
-- FULL UNNORMALISED SOURCE RATIONAL ADDITION WELD.
--
-- The numerator and denominator of Q._+_ are the original
-- unnormalised integer cross products; the solver proves their
-- equality without cancellation of a variable denominator.
-- Hence this is a same-object result, not merely the factorized
-- Nat inequality.
------------------------------------------------------------------------

sourceOmittedRationalIsCommonRational : (n : Nat) →
  Q._≃_
    (sourceOmittedRationalEnvelope n)
    (sourceCommonRationalEnvelope n)
sourceOmittedRationalIsCommonRational n =
  Q.*≡*
    (Zsolve 3
      (λ odd p q →
        ((ZK (+ 16) ⊗ ((odd ⊗ ZK (+ 239)) ⊗ q))
          ⊕ (ZK (+ 4) ⊗ ((odd ⊗ ZK (+ 5)) ⊗ p)))
          ⊗ ((((odd ⊗ ZK (+ 5)) ⊗ ZK (+ 239)) ⊗ p) ⊗ q)
        ⊜
        ((ZK (+ 3824) ⊗ q) ⊕ (ZK (+ 20) ⊗ p))
          ⊗ (((odd ⊗ ZK (+ 5)) ⊗ p)
               ⊗ ((odd ⊗ ZK (+ 239)) ⊗ q)))
      refl
      (+ suc (2 * n))
      (+ Cross.pow25 n)
      (+ Cross.pow57121 n))

sourceOmittedRationalBelowGeometric : (n : Nat) →
  Q._≤_
    (sourceOmittedRationalEnvelope n)
    (sourceGeometricRationalEnvelope n)
sourceOmittedRationalBelowGeometric n =
  QP.≤-respˡ-≃
    (sourceOmittedRationalIsCommonRational n)
    (sourceCommonRationalBelowGeometric n)

sourceOmittedBishopBelowGeometric : (n : Nat) →
  R._≤_
    (R._⋆ (sourceOmittedRationalEnvelope n))
    (R._⋆ (sourceGeometricRationalEnvelope n))
sourceOmittedBishopBelowGeometric n =
  RP.p≤q⇒p⋆≤q⋆
    (sourceOmittedRationalEnvelope n)
    (sourceGeometricRationalEnvelope n)
    (sourceOmittedRationalBelowGeometric n)


------------------------------------------------------------------------
-- K04b: THE LITERAL ORIGINAL FIRST-OMITTED MAGNITUDE AS A RATIONAL
-- POWER ON THE SAME VENDORED BISHOP REAL.
--
-- Previously the denominator bound lived only in rational arithmetic.
-- Here the source's actual |x^(2n+1)| positive-power magnitude is
-- identified with its ORIGINAL qPow term, without assuming that
-- rational powers have already been put in 5*25^n normal form.
------------------------------------------------------------------------

omittedPowerRational : Q.ℚᵘ → Nat → Q.ℚᵘ
omittedPowerRational base n =
  Machin.inverseOddRational n Q.*
    Stage.qPow base (Estimates.oddExponent n)

magnitudeIsEmbeddedOmittedPower :
  (base : Q.ℚᵘ) →
  R.NonNegative (R._⋆ base) →
  (n : Nat) →
  R._≃_
    (Machin.atanMagnitudeTerm (R._⋆ base) n)
    (R._⋆ (omittedPowerRational base n))
magnitudeIsEmbeddedOmittedPower base baseNonnegative n =
  RP.≃-trans
    (RP.*-congˡ
      (RP.nonNegx⇒∣x∣≃x
        (Seq.nonNegx⇒nonNegxⁿ
          (Estimates.oddExponent n) baseNonnegative)))
    (RP.≃-symm
      (RP.≃-trans
        (RP.⋆-distrib-*
          (Machin.inverseOddRational n)
          (Stage.qPow base (Estimates.oddExponent n)))
        (RP.*-cong
          RP.≃-refl
          (Stage.qPowEmbeds base (Estimates.oddExponent n)))))

fiveMagnitudeIsEmbeddedOmittedPower : (n : Nat) →
  R._≃_
    (Machin.atanMagnitudeTerm Machin.bishopOneFifth n)
    (R._⋆ (omittedPowerRational Machin.oneFifth n))
fiveMagnitudeIsEmbeddedOmittedPower n =
  magnitudeIsEmbeddedOmittedPower
    Machin.oneFifth Machin.oneFifthNonnegative n

twoHundredThirtyNineMagnitudeIsEmbeddedOmittedPower : (n : Nat) →
  R._≃_
    (Machin.atanMagnitudeTerm
      Machin.bishopOneTwoHundredThirtyNinth n)
    (R._⋆ (omittedPowerRational
      Machin.oneTwoHundredThirtyNinth n))
twoHundredThirtyNineMagnitudeIsEmbeddedOmittedPower n =
  magnitudeIsEmbeddedOmittedPower
    Machin.oneTwoHundredThirtyNinth
    Machin.oneTwoHundredThirtyNinthNonnegative n

sourceWeightedOmittedPowerRational : Nat → Q.ℚᵘ
sourceWeightedOmittedPowerRational n =
  (Machin.sixteen Q.* omittedPowerRational Machin.oneFifth n)
  Q.+
  (Machin.four Q.* omittedPowerRational
    Machin.oneTwoHundredThirtyNinth n)

sourceWeightedOmittedIsEmbeddedPowerRational : (n : Nat) →
  R._≃_
    (R._+_
      (R._*_
        (R._⋆ Machin.sixteen)
        (Machin.atanMagnitudeTerm Machin.bishopOneFifth n))
      (R._*_
        (R._⋆ Machin.four)
        (Machin.atanMagnitudeTerm
          Machin.bishopOneTwoHundredThirtyNinth n)))
    (R._⋆ (sourceWeightedOmittedPowerRational n))
sourceWeightedOmittedIsEmbeddedPowerRational n =
  RP.≃-trans
    (RP.+-cong
      (RP.*-cong RP.≃-refl
        (fiveMagnitudeIsEmbeddedOmittedPower n))
      (RP.*-cong RP.≃-refl
        (twoHundredThirtyNineMagnitudeIsEmbeddedOmittedPower n)))
    (RP.≃-symm
      (RP.≃-trans
        (RP.⋆-distrib-+
          (Machin.sixteen Q.*
            omittedPowerRational Machin.oneFifth n)
          (Machin.four Q.*
            omittedPowerRational
              Machin.oneTwoHundredThirtyNinth n))
        (RP.+-cong
          (RP.⋆-distrib-*
            Machin.sixteen
            (omittedPowerRational Machin.oneFifth n))
          (RP.⋆-distrib-*
            Machin.four
            (omittedPowerRational
              Machin.oneTwoHundredThirtyNinth n)))))


------------------------------------------------------------------------
-- Exact Nat odd-exponent base normalization, all indices.
-- This is the polynomial exponent bridge behind the remaining
-- original qPow rational equivalence; it uses the existing
-- signed-factorial odd-index owner, not a parallel index definition.
------------------------------------------------------------------------

oddNaturalPowerFactor :
  (base n : Nat) →
  base ^ Estimates.oddExponent n ≡
  base * ((base * base) ^ n)
oddNaturalPowerFactor base zero = refl
oddNaturalPowerFactor base (suc n) =
  trans
    (cong (λ power → base * (base * power))
      (oddNaturalPowerFactor base n))
    (solve 2
      (λ b p →
        b :* (b :* (b :* p))
        := b :* ((b :* b) :* p))
      refl base ((base * base) ^ n))

fiveOddNaturalPowerFactor : (n : Nat) →
  5 ^ Estimates.oddExponent n ≡ 5 * Cross.pow25 n
fiveOddNaturalPowerFactor = oddNaturalPowerFactor 5

twoHundredThirtyNineOddNaturalPowerFactor : (n : Nat) →
  239 ^ Estimates.oddExponent n ≡
  239 * Cross.pow57121 n
twoHundredThirtyNineOddNaturalPowerFactor =
  oddNaturalPowerFactor 239


------------------------------------------------------------------------
-- K04b: LITERAL RATIONAL ODD-POWER NORMALISATION (ALL Nat INDICES).
-- The existing qPow operator is the actual qMachinStage embedding owner.
-- Use its recursion and the original unnormalised rational setoid.
------------------------------------------------------------------------

reciprocalNatPower :
  (base : Nat) → .{{_ : Nat.NonZero base}} → Nat → Q.ℚᵘ
reciprocalNatPower base n =
  let
    instance
      powerNZ = NatP.m^n≢0 base n
  in
  + 1 / (base ^ n)

rationalReciprocalPower :
  (base : Nat) → .{{_ : Nat.NonZero base}} →
  (n : Nat) →
  Q._≃_
    (Stage.qPow (+ 1 / base) n)
    (reciprocalNatPower base n)
rationalReciprocalPower base zero = QP.≃-refl
rationalReciprocalPower base (suc n) =
  QP.≃-trans
    (QP.*-cong
      (rationalReciprocalPower base n)
      QP.≃-refl)
    (Q.*≡*
      (cong +_ (NatP.*-comm base (base ^ n))))

fiveOddPowerRational : (n : Nat) →
  Q._≃_
    (Stage.qPow Machin.oneFifth (Estimates.oddExponent n))
    (+ 1 / (5 * Cross.pow25 n))
fiveOddPowerRational n =
  let
    instance
      fivePowerNZ = NatP.m*n≢0 5 (Cross.pow25 n)
        {{_}} {{pow25NonZero n}}
  in
  QP.≃-trans
    (rationalReciprocalPower 5 (Estimates.oddExponent n))
    (QP.≃-reflexive
      (QP./-cong refl (fiveOddNaturalPowerFactor n)))

twoHundredThirtyNineOddPowerRational : (n : Nat) →
  Q._≃_
    (Stage.qPow Machin.oneTwoHundredThirtyNinth
      (Estimates.oddExponent n))
    (+ 1 / (239 * Cross.pow57121 n))
twoHundredThirtyNineOddPowerRational n =
  let
    instance
      powerNZ = NatP.m*n≢0 239 (Cross.pow57121 n)
        {{_}} {{pow57121NonZero n}}
  in
  QP.≃-trans
    (rationalReciprocalPower 239 (Estimates.oddExponent n))
    (QP.≃-reflexive
      (QP./-cong refl
        (twoHundredThirtyNineOddNaturalPowerFactor n)))

fiveOmittedPowerIsOriginalFraction : (n : Nat) →
  Q._≃_
    (omittedPowerRational Machin.oneFifth n)
    (+ 1 / sourceFiveDenominator n)
fiveOmittedPowerIsOriginalFraction n =
  let
    instance
      fivePowerNZ = NatP.m*n≢0 5 (Cross.pow25 n)
        {{_}} {{pow25NonZero n}}
      denominatorNZ = sourceFiveDenominatorNonZero n
  in
  QP.≃-trans
    (QP.*-cong QP.≃-refl (fiveOddPowerRational n))
    (Q.*≡*
      (cong +_
        (NatP.*-assoc
          (Estimates.oddExponent n)
          5
          (Cross.pow25 n))))

twoHundredThirtyNineOmittedPowerIsOriginalFraction : (n : Nat) →
  Q._≃_
    (omittedPowerRational Machin.oneTwoHundredThirtyNinth n)
    (+ 1 / source239Denominator n)
twoHundredThirtyNineOmittedPowerIsOriginalFraction n =
  let
    instance
      powerNZ = NatP.m*n≢0 239 (Cross.pow57121 n)
        {{_}} {{pow57121NonZero n}}
      denominatorNZ = source239DenominatorNonZero n
  in
  QP.≃-trans
    (QP.*-cong QP.≃-refl
      (twoHundredThirtyNineOddPowerRational n))
    (Q.*≡*
      (cong +_
        (NatP.*-assoc
          (Estimates.oddExponent n)
          239
          (Cross.pow57121 n))))

sourceWeightedPowerEqualsOriginalFraction : (n : Nat) →
  Q._≃_
    (sourceWeightedOmittedPowerRational n)
    (sourceOmittedRationalEnvelope n)
sourceWeightedPowerEqualsOriginalFraction n =
  let
    instance
      fiveNZ = sourceFiveDenominatorNonZero n
      otherNZ = source239DenominatorNonZero n
  in
  QP.+-cong
    (QP.≃-trans
      (QP.*-cong
        QP.≃-refl
        (fiveOmittedPowerIsOriginalFraction n))
      (Q.*≡* refl))
    (QP.≃-trans
      (QP.*-cong
        QP.≃-refl
        (twoHundredThirtyNineOmittedPowerIsOriginalFraction n))
      (Q.*≡* refl))

sourceWeightedOmittedIsEmbeddedOriginalFraction : (n : Nat) →
  R._≃_
    (R._+_
      (R._*_
        (R._⋆ Machin.sixteen)
        (Machin.atanMagnitudeTerm Machin.bishopOneFifth n))
      (R._*_
        (R._⋆ Machin.four)
        (Machin.atanMagnitudeTerm
          Machin.bishopOneTwoHundredThirtyNinth n)))
    (R._⋆ (sourceOmittedRationalEnvelope n))
sourceWeightedOmittedIsEmbeddedOriginalFraction n =
  RP.≃-trans
    (sourceWeightedOmittedIsEmbeddedPowerRational n)
    (RP.⋆-cong (sourceWeightedPowerEqualsOriginalFraction n))

sourceOriginalOmittedBishopBelowGeometric : (n : Nat) →
  R._≤_
    (R._+_
      (R._*_
        (R._⋆ Machin.sixteen)
        (Machin.atanMagnitudeTerm Machin.bishopOneFifth n))
      (R._*_
        (R._⋆ Machin.four)
        (Machin.atanMagnitudeTerm
          Machin.bishopOneTwoHundredThirtyNinth n)))
    (R._⋆ (sourceGeometricRationalEnvelope n))
sourceOriginalOmittedBishopBelowGeometric n =
  RP.≤-respˡ-≃
    (sourceWeightedOmittedIsEmbeddedOriginalFraction n)
    (sourceOmittedBishopBelowGeometric n)
