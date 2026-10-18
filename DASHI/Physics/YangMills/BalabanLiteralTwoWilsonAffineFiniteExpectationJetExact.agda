{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonAffineFiniteExpectationJetExact where

------------------------------------------------------------------------
-- ACTUAL NORMALIZED FINITE-MEASURE AFFINE TWO-SOURCE JET
--
-- The physical finite YM expectation is already normalized, additive and
-- scalar-linear.  Hence the expanded affine two-source insertion
--
--   1 + s L + t R + s t (L R)
--
-- has normalized expectation
--
--   1 + s E[L] + t E[R] + s t E[LR].
--
-- This is the literal finite-measure moment jet underlying the normalized
-- mixed-log/cumulant compiler.  No polymer or localization theorem is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 1ℝ; _+ℝ_; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

productObservable :
  ∀ {Configuration} →
  (Configuration → ℝ) →
  (Configuration → ℝ) →
  Configuration → ℝ
productObservable left right configuration =
  left configuration *ℝ right configuration

affineTwoSourceObservable :
  ∀ {Configuration} →
  ℝ → ℝ →
  (Configuration → ℝ) →
  (Configuration → ℝ) →
  Configuration → ℝ
affineTwoSourceObservable leftSource rightSource left right =
  Finite.addObservable
    Finite.oneObservable
    (Finite.addObservable
      (Finite.scaleObservable leftSource left)
      (Finite.addObservable
        (Finite.scaleObservable rightSource right)
        (Finite.scaleObservable
          (leftSource *ℝ rightSource)
          (productObservable left right))))

finiteAffineExpectationPolynomial :
  ∀ {Configuration sequenceLimit limitLaws quotient division}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    cutoff leftSource rightSource left right →
  Limit.finiteExpectation family cutoff
    (affineTwoSourceObservable
      leftSource rightSource left right)
  ≡
  1ℝ
  +ℝ
  (leftSource *ℝ Limit.finiteExpectation family cutoff left
  +ℝ
  (rightSource *ℝ Limit.finiteExpectation family cutoff right
  +ℝ
  ((leftSource *ℝ rightSource)
    *ℝ
    Limit.finiteExpectation family cutoff
      (productObservable left right))))
finiteAffineExpectationPolynomial
    family cutoff leftSource rightSource left right
  rewrite
    Limit.finiteExpectationAdd family cutoff
      Finite.oneObservable
      (Finite.addObservable
        (Finite.scaleObservable leftSource left)
        (Finite.addObservable
          (Finite.scaleObservable rightSource right)
          (Finite.scaleObservable
            (leftSource *ℝ rightSource)
            (productObservable left right))))
  | Limit.finiteExpectationOne family cutoff
  | Limit.finiteExpectationAdd family cutoff
      (Finite.scaleObservable leftSource left)
      (Finite.addObservable
        (Finite.scaleObservable rightSource right)
        (Finite.scaleObservable
          (leftSource *ℝ rightSource)
          (productObservable left right)))
  | Limit.finiteExpectationScale family cutoff leftSource left
  | Limit.finiteExpectationAdd family cutoff
      (Finite.scaleObservable rightSource right)
      (Finite.scaleObservable
        (leftSource *ℝ rightSource)
        (productObservable left right))
  | Limit.finiteExpectationScale family cutoff rightSource right
  | Limit.finiteExpectationScale family cutoff
      (leftSource *ℝ rightSource)
      (productObservable left right)
  = refl

record FiniteAffineMomentJet
    {Configuration : Set}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    (cutoff : Nat)
    (left right : Configuration → ℝ)
    : Set where
  constructor finite-affine-moment-jet
  field
    constantCoefficient : ℝ
    leftCoefficient : ℝ
    rightCoefficient : ℝ
    mixedCoefficient : ℝ

open FiniteAffineMomentJet public

literalFiniteAffineMomentJet :
  ∀ {Configuration sequenceLimit limitLaws quotient division}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    cutoff left right →
  FiniteAffineMomentJet family cutoff left right
literalFiniteAffineMomentJet family cutoff left right =
  finite-affine-moment-jet
    1ℝ
    (Limit.finiteExpectation family cutoff left)
    (Limit.finiteExpectation family cutoff right)
    (Limit.finiteExpectation family cutoff
      (productObservable left right))

literalFiniteAffineMixedCoefficient :
  ∀ {Configuration sequenceLimit limitLaws quotient division}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    cutoff left right →
  mixedCoefficient (literalFiniteAffineMomentJet family cutoff left right)
  ≡
  Limit.finiteExpectation family cutoff
    (productObservable left right)
literalFiniteAffineMixedCoefficient family cutoff left right = refl

literalTwoSourceAffineFiniteExpectationLevel : ProofLevel
literalTwoSourceAffineFiniteExpectationLevel = machineChecked
