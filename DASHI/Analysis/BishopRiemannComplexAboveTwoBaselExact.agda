module DASHI.Analysis.BishopRiemannComplexAboveTwoBaselExact where

------------------------------------------------------------------------
-- K04d: ORIGINAL COMPLEX DIRICHLET SERIES, ALL NONINTEGER SIGMA > 2.
--
-- The actual Round11 Bishop expC(-s*L_n) obeys the original
-- Basel comparison at EVERY positive successor n and EVERY imaginary
-- coordinate, conditional only on:
--    (i)  the native source exp_B(L_n)=n+1 inverse;
--    (ii) actual SAME-OBJECT Round11 Pythagorean at each source angle.
--
-- These are explicit genuinely missing theorems, not free comparison
-- assumptions. The proof uses the original exponential Cauchy product,
-- real sigma>2 factorization, negative exponential strict order,
-- exact complex coordinates, Bishop absolute multiplication and the
-- preexisting native nonnegative-square reflection for sin/cos bounds.
--
-- The zero-th Dirichlet term (n=0, log 1=0) is a finite exceptional
-- head; the original eventual Basel comparison accepts start=1.
-- This is the ORIGINAL variable-s Dirichlet term family, not the
-- artificial integer-exponent family independent of s.
--
-- Historical authors: Riemann, Dirichlet, Bishop/Bridges;
-- Murray 2022, pinned Viktor Csimma Bishop. DASHI composition.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base as Nat using (_≤_; _≥_; NonZero; z≤n)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)
open import Data.Integer.Base using (+_)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as A
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as D
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Analysis.BishopDirichletUniformBaselTailsExact as UniformTails
import DASHI.Analysis.BishopRound11TrigModulusFromPythagoreanExact as Modulus
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpPositive
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as ExpCong
import DASHI.Foundations.BishopRound11TrigAtZeroExact as Origin
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as TrigCong
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as NegativeExp
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

sourceLogPositiveIndex : Nat → R.ℝ
sourceLogPositiveIndex n =
  D.sourceCanonicalNatLogCandidate (suc n)

sourceDirichletAngle :
  A.BishopComplex → Nat → R.ℝ
sourceDirichletAngle s n =
  R._*_ (R.- (A.im s)) (sourceLogPositiveIndex n)

sourceDirichletRealExp :
  A.BishopComplex → Nat → R.ℝ
sourceDirichletRealExp s n =
  Exp.bishopExp
    (R._*_ (R.- (A.re s)) (sourceLogPositiveIndex n))

sourceSelectedPythagorean :
  Round11.Round11BishopCutset →
  A.BishopComplex → Nat → Set
sourceSelectedPythagorean inputs s n =
  let
    theta = sourceDirichletAngle s n
    dataSet = Round11.elementarySeries inputs
    c = E.bishopCos dataSet theta
    t = E.bishopSin dataSet theta
  in
  R._≃_ (R._+_ (R._*_ c c) (R._*_ t t)) R.1ℝ

sourceRealExponentNonnegative :
  (s : A.BishopComplex) (n : Nat) →
  R._<_ D.sourceTwoReal (A.re s) →
  R._≃_
    (Exp.bishopExp (sourceLogPositiveIndex n))
    (NatReal.natReal (suc (suc n))) →
  R.NonNegative (sourceDirichletRealExp s n)
sourceRealExponentNonnegative s n aboveTwo inverseLaw =
  let
    sigma = A.re s
    logPoint = sourceLogPositiveIndex n
    expTwo = Exp.bishopExp
      (R._*_ (R.- D.sourceTwoReal) logPoint)
    expTwoEqualsBasel =
      D.negativeTwoNatLogExponentialIsBasel
        D.sourceCanonicalNatLogCandidate (suc n)
        inverseLaw
    expTwoNonnegative : R.NonNegative expTwo
    expTwoNonnegative =
      RP.0≤x⇒nonNegx
        (RP.≤-respʳ-≃
          (RP.≃-symm expTwoEqualsBasel)
          (RP.nonNegx⇒0≤x (Basel.baselTermNonnegative (suc n))))
    extraPositive =
      NegativeExp.negativeExpPositive
        (D.sourceAboveTwoExtraFactorPositive
          sigma logPoint aboveTwo
          (D.sourceCanonicalNatLogSuccessorPositive n))
    extraNonnegative =
      RP.0≤x⇒nonNegx (RP.<⇒≤ extraPositive)
    productNonnegative =
      RP.nonNegx,y⇒nonNegx*y
        expTwoNonnegative extraNonnegative
  in
  RP.0≤x⇒nonNegx
    (RP.≤-respʳ-≃
      (RP.≃-symm
        (D.sourceRealExponentAboveTwoFactor sigma logPoint))
      (RP.nonNegx⇒0≤x productNonnegative))

sourceRealExpBelowBasel :
  (s : A.BishopComplex) (n : Nat) →
  R._<_ D.sourceTwoReal (A.re s) →
  R._≃_
    (Exp.bishopExp (sourceLogPositiveIndex n))
    (NatReal.natReal (suc (suc n))) →
  R._≤_ (sourceDirichletRealExp s n) (Basel.baselTerm (suc n))
sourceRealExpBelowBasel s n aboveTwo inverseLaw =
  D.sourceRealExponentAboveTwoBasel
    D.sourceCanonicalNatLogCandidate (suc n)
    (A.re s) aboveTwo
    (D.sourceCanonicalNatLogSuccessorPositive n)
    inverseLaw

absoluteProductBelowBasel :
  (exponential phase : R.ℝ) (index : Nat) →
  R.NonNegative exponential →
  R._≤_ exponential (Basel.baselTerm index) →
  R._≤_ (R.∣ phase ∣) R.1ℝ →
  R._≤_
    (R.∣ R._*_ exponential phase ∣)
    (Basel.baselTerm index)
absoluteProductBelowBasel exponential phase index nonnegative scalarBound phaseBound =
  RP.≤-respˡ-≃
    (RP.≃-symm (RP.∣x*y∣≃∣x∣*∣y∣ exponential phase))
    (RP.≤-respʳ-≃
      (RP.*-identityʳ (Basel.baselTerm index))
      (RP.*-mono-≤
        (RP.nonNeg∣x∣ exponential)
        (RP.nonNeg∣x∣ phase)
        (RP.≤-respˡ-≃
          (RP.≃-symm (RP.nonNegx⇒∣x∣≃x nonnegative))
          scalarBound)
        phaseBound))

sourceComplexAboveTwoCoordinateBounds :
  (inputs : Round11.Round11BishopCutset)
  (s : A.BishopComplex) (n : Nat) →
  R._<_ D.sourceTwoReal (A.re s) →
  R._≃_
    (Exp.bishopExp (sourceLogPositiveIndex n))
    (NatReal.natReal (suc (suc n))) →
  sourceSelectedPythagorean inputs s n →
  let
    terms = D.bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs)
      D.sourceCanonicalNatLogCandidate
  in
  (R._≤_
    (R.∣ A.re (terms s (suc n)) ∣)
    (Basel.baselTerm (suc n)))
  ×
  (R._≤_
    (R.∣ A.im (terms s (suc n)) ∣)
    (Basel.baselTerm (suc n)))
sourceComplexAboveTwoCoordinateBounds
    inputs s n aboveTwo inverseLaw pythagorean =
  let
    e = sourceDirichletRealExp s n
    theta = sourceDirichletAngle s n
    c = E.bishopCos (Round11.elementarySeries inputs) theta
    t = E.bishopSin (Round11.elementarySeries inputs) theta
    eNonnegative =
      sourceRealExponentNonnegative s n aboveTwo inverseLaw
    eBound = sourceRealExpBelowBasel s n aboveTwo inverseLaw
    phaseBound =
      Modulus.round11ModulusFromPythagorean
        inputs theta pythagorean
  in
  absoluteProductBelowBasel
    e c (suc n) eNonnegative eBound (proj₁ phaseBound)
  ,
  absoluteProductBelowBasel
    e t (suc n) eNonnegative eBound (proj₂ phaseBound)

-- Eventual all-complex-half-plane Basel domination, source n>=1.
-- No need to pretend that the genuine log(1)=0 head decays:
-- convergence owner explicitly accepts a finite start index.
sourceComplexAboveTwoMajorant :
  (inputs : Round11.Round11BishopCutset)
  (s : A.BishopComplex) →
  R._<_ D.sourceTwoReal (A.re s) →
  ((n : Nat) →
    R._≃_
      (Exp.bishopExp (D.sourceCanonicalNatLogCandidate n))
      (NatReal.natReal (suc n))) →
  ((n : Nat) → sourceSelectedPythagorean inputs s n) →
  Dirichlet.BishopDirichletBaselMajorantAt
    (D.bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs)
      D.sourceCanonicalNatLogCandidate)
    s
sourceComplexAboveTwoMajorant
    inputs s aboveTwo inverseLaw pythagorean = record
  { Dirichlet.dominationStart = suc zero
  ; Dirichlet.realDomination = λ
      { zero ()
      ; (suc n) _ →
          proj₁ (sourceComplexAboveTwoCoordinateBounds
            inputs s n aboveTwo (inverseLaw (suc n))
            (pythagorean n))
      }
  ; Dirichlet.imagDomination = λ
      { zero ()
      ; (suc n) _ →
          proj₂ (sourceComplexAboveTwoCoordinateBounds
            inputs s n aboveTwo (inverseLaw (suc n))
            (pythagorean n))
      }
  }

sourceComplexAboveTwoConverges :
  (inputs : Round11.Round11BishopCutset)
  (s : A.BishopComplex) →
  (aboveTwo : R._<_ D.sourceTwoReal (A.re s)) →
  (inverseLaw : (n : Nat) →
    R._≃_
      (Exp.bishopExp (D.sourceCanonicalNatLogCandidate n))
      (NatReal.natReal (suc n))) →
  (pythagorean : (n : Nat) →
    sourceSelectedPythagorean inputs s n) →
  let
    terms = D.bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs)
      D.sourceCanonicalNatLogCandidate
    bound = sourceComplexAboveTwoMajorant
      inputs s aboveTwo inverseLaw pythagorean
  in
  (Seq._ConvergesTo_
    (λ count → A.re (Dirichlet.dirichletPartial terms s count))
    (A.re (Dirichlet.dirichletValue terms s bound)))
  ×
  (Seq._ConvergesTo_
    (λ count → A.im (Dirichlet.dirichletPartial terms s count))
    (A.im (Dirichlet.dirichletValue terms s bound)))
sourceComplexAboveTwoConverges inputs s aboveTwo inverseLaw pythagorean =
  Dirichlet.dirichletPartialConverges
    (D.bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs)
      D.sourceCanonicalNatLogCandidate)
    s
    (sourceComplexAboveTwoMajorant
      inputs s aboveTwo inverseLaw pythagorean)


------------------------------------------------------------------------
-- FINITE SOURCE HEAD n=0: L(1)=0, exp_C(-s*0)=(1,0).
-- Thus the original Basel comparison holds at every index, and
-- the region-wide common-cutoff compiler needs no exceptional tail.
------------------------------------------------------------------------

zeroLogScalarExponent : (value : R.ℝ) →
  R._≃_
    (R._*_ (R.- value) (D.sourceCanonicalNatLogCandidate zero))
    R.0ℝ
zeroLogScalarExponent value =
  let open RP.ℝ-Solver
  in solve 1
    (λ u → (⊝ u) ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
    RP.≃-refl value

sourceComplexZeroRealIsOne :
  (inputs : Round11.Round11BishopCutset)
  (s : A.BishopComplex) →
  let terms = D.bishopDirichletExponentialTerm
       (Route.round11MachinTranscendentals inputs)
       D.sourceCanonicalNatLogCandidate
  in
  R._≃_ (A.re (terms s zero)) R.1ℝ
sourceComplexZeroRealIsOne inputs s =
  RP.≃-trans
    (RP.*-cong
      (RP.≃-trans
        (ExpCong.bishopExpCongruent
          (zeroLogScalarExponent (A.re s)))
        ExpPositive.bishopExpZero)
      (RP.≃-trans
        (TrigCong.bishopCosCongruent
          (Round11.round11ConcreteTermIdentification inputs)
          (zeroLogScalarExponent (A.im s)))
        (Origin.round11CosineAtZero inputs)))
    (RP.*-identityˡ R.1ℝ)

sourceComplexZeroImagIsZero :
  (inputs : Round11.Round11BishopCutset)
  (s : A.BishopComplex) →
  let terms = D.bishopDirichletExponentialTerm
       (Route.round11MachinTranscendentals inputs)
       D.sourceCanonicalNatLogCandidate
  in
  R._≃_ (A.im (terms s zero)) R.0ℝ
sourceComplexZeroImagIsZero inputs s =
  RP.≃-trans
    (RP.*-cong
      (RP.≃-trans
        (ExpCong.bishopExpCongruent
          (zeroLogScalarExponent (A.re s)))
        ExpPositive.bishopExpZero)
      (RP.≃-trans
        (TrigCong.bishopSinCongruent
          (Round11.round11ConcreteTermIdentification inputs)
          (zeroLogScalarExponent (A.im s)))
        (Origin.round11SineAtZero inputs)))
    (let open RP.ℝ-Solver
     in solve 0
       (Κ 1ℚᵘ ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
       RP.≃-refl)

sourceComplexZeroBaselBound :
  (inputs : Round11.Round11BishopCutset)
  (s : A.BishopComplex) →
  let terms = D.bishopDirichletExponentialTerm
       (Route.round11MachinTranscendentals inputs)
       D.sourceCanonicalNatLogCandidate
  in
  (R._≤_ (R.∣ A.re (terms s zero) ∣) (Basel.baselTerm zero))
  ×
  (R._≤_ (R.∣ A.im (terms s zero) ∣) (Basel.baselTerm zero))
sourceComplexZeroBaselBound inputs s =
  RP.≤-respˡ-≃
    (RP.≃-symm
      (RP.∣-∣-cong (sourceComplexZeroRealIsOne inputs s)))
    (RP.≤-reflexive (Basel.absoluteBaselTerm zero))
  ,
  RP.≤-respˡ-≃
    (RP.≃-symm
      (RP.∣-∣-cong (sourceComplexZeroImagIsZero inputs s)))
    (Dirichlet.zeroAbsBelowBasel zero)

-- All-index variable-complex-s majorant. The Pythagorean at each
-- literal source phase and canonical exp/log inverse remain explicit.
sourceComplexAboveTwoMajorantAllIndices :
  (inputs : Round11.Round11BishopCutset)
  (s : A.BishopComplex) →
  R._<_ D.sourceTwoReal (A.re s) →
  ((n : Nat) →
    R._≃_
      (Exp.bishopExp (D.sourceCanonicalNatLogCandidate n))
      (NatReal.natReal (suc n))) →
  ((n : Nat) → sourceSelectedPythagorean inputs s n) →
  Dirichlet.BishopDirichletBaselMajorantAt
    (D.bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs)
      D.sourceCanonicalNatLogCandidate)
    s
sourceComplexAboveTwoMajorantAllIndices
    inputs s aboveTwo inverseLaw pythagorean = record
  { Dirichlet.dominationStart = zero
  ; Dirichlet.realDomination = λ
      { zero _ → proj₁ (sourceComplexZeroBaselBound inputs s)
      ; (suc n) _ →
          proj₁ (sourceComplexAboveTwoCoordinateBounds
            inputs s n aboveTwo (inverseLaw (suc n))
            (pythagorean n))
      }
  ; Dirichlet.imagDomination = λ
      { zero _ → proj₂ (sourceComplexZeroBaselBound inputs s)
      ; (suc n) _ →
          proj₂ (sourceComplexAboveTwoCoordinateBounds
            inputs s n aboveTwo (inverseLaw (suc n))
            (pythagorean n))
      }
  }


------------------------------------------------------------------------
-- REGION-WIDE UNIFORMITY ON THE ACTUAL BISHOP HALF-PLANE Re(s)>2.
--
-- Combine the genuine all-index complex coefficient comparison with
-- the preexisting common-cutoff Bishop Dirichlet compiler.
--
-- Only the ORIGINAL canonical exp/log inverse and same-object
-- all-angle signed-factorial Pythagorean remain as analytic inputs.
-- In particular, no generic function-valued majorant field is supplied
-- and the value is the literal original expC(-s*L_n) Dirichlet sum.
------------------------------------------------------------------------

sourceAboveTwoRegion : A.BishopComplex → Set
sourceAboveTwoRegion s =
  R._<_ D.sourceTwoReal (A.re s)

sourceAllAnglesPythagorean :
  Round11.Round11BishopCutset → Set
sourceAllAnglesPythagorean inputs =
  (theta : R.ℝ) →
  let
    dataSet = Round11.elementarySeries inputs
    c = E.bishopCos dataSet theta
    t = E.bishopSin dataSet theta
  in
  R._≃_ (R._+_ (R._*_ c c) (R._*_ t t)) R.1ℝ

sourceRegionWideBaselCertificate :
  (inputs : Round11.Round11BishopCutset) →
  ((n : Nat) →
    R._≃_
      (Exp.bishopExp (D.sourceCanonicalNatLogCandidate n))
      (NatReal.natReal (suc n))) →
  sourceAllAnglesPythagorean inputs →
  UniformTails.RegionBaselDomination
    (D.bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs)
      D.sourceCanonicalNatLogCandidate)
    sourceAboveTwoRegion
sourceRegionWideBaselCertificate
    inputs inverseLaw pythagorean = record
  { UniformTails.realEverywhere = λ s aboveTwo n →
      let
        bound = sourceComplexAboveTwoMajorantAllIndices
          inputs s aboveTwo inverseLaw
          (λ index → pythagorean (sourceDirichletAngle s index))
      in
      Dirichlet.realDomination bound n Nat.z≤n
  ; UniformTails.imagEverywhere = λ s aboveTwo n →
      let
        bound = sourceComplexAboveTwoMajorantAllIndices
          inputs s aboveTwo inverseLaw
          (λ index → pythagorean (sourceDirichletAngle s index))
      in
      Dirichlet.imagDomination bound n Nat.z≤n
  }

sourceRegionUniformDirichletValue :
  (inputs : Round11.Round11BishopCutset)
  (inverseLaw : (n : Nat) →
    R._≃_
      (Exp.bishopExp (D.sourceCanonicalNatLogCandidate n))
      (NatReal.natReal (suc n)))
  (pythagorean : sourceAllAnglesPythagorean inputs)
  (s : A.BishopComplex) →
  sourceAboveTwoRegion s →
  A.BishopComplex
sourceRegionUniformDirichletValue
    inputs inverseLaw pythagorean s aboveTwo =
  UniformTails.regionDirichletValue
    (D.bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs)
      D.sourceCanonicalNatLogCandidate)
    sourceAboveTwoRegion
    (sourceRegionWideBaselCertificate
      inputs inverseLaw pythagorean)
    s aboveTwo

sourceRegionUniformLimitError :
  (inputs : Round11.Round11BishopCutset)
  (inverseLaw : (n : Nat) →
    R._≃_
      (Exp.bishopExp (D.sourceCanonicalNatLogCandidate n))
      (NatReal.natReal (suc n)))
  (pythagorean : sourceAllAnglesPythagorean inputs)
  (k : Nat) → .{{_ : Nat.NonZero k}} →
  (s : A.BishopComplex)
  (aboveTwo : sourceAboveTwoRegion s)
  (m : Nat) →
  m Nat.≥ UniformTails.baselUniformTailCutoff k →
  let
    terms = D.bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs)
      D.sourceCanonicalNatLogCandidate
    value = sourceRegionUniformDirichletValue
      inputs inverseLaw pythagorean s aboveTwo
  in
  (R._≤_
    (R.∣ R._-_ (A.re value)
      (Seq.SeriesOf (Dirichlet.realTerm terms s) m) ∣)
    (R._⋆ (+ 1 / k)))
  ×
  (R._≤_
    (R.∣ R._-_ (A.im value)
      (Seq.SeriesOf (Dirichlet.imagTerm terms s) m) ∣)
    (R._⋆ (+ 1 / k)))
sourceRegionUniformLimitError
    inputs inverseLaw pythagorean k s aboveTwo m mPast =
  let
    terms = D.bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs)
      D.sourceCanonicalNatLogCandidate
    bound = sourceRegionWideBaselCertificate
      inputs inverseLaw pythagorean
  in
  UniformTails.regionRealUniformLimitError
    terms sourceAboveTwoRegion bound
    k s aboveTwo m mPast
  ,
  UniformTails.regionImagUniformLimitError
    terms sourceAboveTwoRegion bound
    k s aboveTwo m mPast
