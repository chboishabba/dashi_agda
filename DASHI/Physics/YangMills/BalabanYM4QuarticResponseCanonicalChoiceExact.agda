{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact where

------------------------------------------------------------------------
-- ROW A: FINITE b,C,L,R,D -> CANONICAL QUARTIC-RESPONSE COUPLING CAP
--
-- The quartic-response reduction needs
--
--       (C + L + 4 R D) gamma < b,      0 <= gamma <= 1.
--
-- Reuse the existing canonical choice with effective derivative
--
--       L_eff = L + 4 R D.
--
-- If additionally b <= 1 (true for the fixed Ward floor 1/8388608), the same
-- canonical denominator is at least 2, hence gamma <= b/2 <= 1/2 < 1.
-- Thus the quadratic-to-linear absorption condition is automatic; no second
-- coupling choice or numerical search is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; Positive; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot
import DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact as Cubic
import DASHI.Physics.YangMills.BalabanYM4RowACanonicalSmallCouplingChoiceExact as Choice
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalGateExact as Gate

mulNN : ∀ {left right : ℚ} → 0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
mulNN {left} {right} leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = ℚ.nonNegative leftNN
      rightNonnegative : NonNegative right
      rightNonnegative = ℚ.nonNegative rightNN
  in
  ℚP.nonNegative⁻¹ (left * right)

record FiniteQuarticResponseConstants : Set where
  field
    gaussianFloor interactionConstant localDerivative : ℚ
    responseCoefficient sourceCoefficient : ℚ

    gaussianFloorPositive : 0ℚ < gaussianFloor
    gaussianFloorAtMostOne : gaussianFloor ≤ 1ℚ
    interactionConstantNonnegative : 0ℚ ≤ interactionConstant
    localDerivativeNonnegative : 0ℚ ≤ localDerivative
    responseCoefficientNonnegative : 0ℚ ≤ responseCoefficient
    sourceCoefficientNonnegative : 0ℚ ≤ sourceCoefficient

open FiniteQuarticResponseConstants public

effectiveDerivative : FiniteQuarticResponseConstants → ℚ
effectiveDerivative dataSet =
  localDerivative dataSet
    + Gate.fourℚ * responseCoefficient dataSet * sourceCoefficient dataSet

effectiveDerivativeNonnegative :
  (dataSet : FiniteQuarticResponseConstants) →
  0ℚ ≤ effectiveDerivative dataSet
effectiveDerivativeNonnegative dataSet =
  let
    twoNN = ℚP.+-mono-≤ Geo.oneNonnegativeProof Geo.oneNonnegativeProof
    fourNN = mulNN twoNN twoNN
    responsePartNN = mulNN
      (mulNN fourNN (responseCoefficientNonnegative dataSet))
      (sourceCoefficientNonnegative dataSet)
  in
  ℚP.+-mono-≤ (localDerivativeNonnegative dataSet) responsePartNN

asCanonicalSourceConstants :
  FiniteQuarticResponseConstants → Choice.FiniteRowASourceConstants
asCanonicalSourceConstants dataSet = record
  { Choice.FiniteRowASourceConstants.gaussianFloor = gaussianFloor dataSet
  ; Choice.FiniteRowASourceConstants.interactionConstant =
      interactionConstant dataSet
  ; Choice.FiniteRowASourceConstants.derivativeBound =
      effectiveDerivative dataSet
  ; Choice.FiniteRowASourceConstants.gaussianFloorPositive =
      gaussianFloorPositive dataSet
  ; Choice.FiniteRowASourceConstants.interactionConstantNonnegative =
      interactionConstantNonnegative dataSet
  ; Choice.FiniteRowASourceConstants.derivativeBoundNonnegative =
      effectiveDerivativeNonnegative dataSet
  }

canonicalQuarticResponseGamma : FiniteQuarticResponseConstants → ℚ
canonicalQuarticResponseGamma dataSet =
  Choice.canonicalGamma (asCanonicalSourceConstants dataSet)

canonicalQuarticResponseGammaPositive :
  (dataSet : FiniteQuarticResponseConstants) →
  0ℚ < canonicalQuarticResponseGamma dataSet
canonicalQuarticResponseGammaPositive dataSet =
  Choice.canonicalGammaPositive (asCanonicalSourceConstants dataSet)

canonicalQuarticResponsePaysLinearGate :
  (dataSet : FiniteQuarticResponseConstants) →
  (interactionConstant dataSet + localDerivative dataSet
    + Gate.fourℚ * responseCoefficient dataSet * sourceCoefficient dataSet)
    * canonicalQuarticResponseGamma dataSet
  < gaussianFloor dataSet
canonicalQuarticResponsePaysLinearGate dataSet =
  Choice.canonicalGammaPaysCombinedSmallness
    (asCanonicalSourceConstants dataSet)

denominatorAtLeastTwo :
  (dataSet : FiniteQuarticResponseConstants) →
  Cubic.twoℚ ≤ Choice.canonicalDenominator (asCanonicalSourceConstants dataSet)
denominatorAtLeastTwo dataSet =
  let
    source = asCanonicalSourceConstants dataSet
    S = Choice.sourceSlope source
    slopeNN = Choice.sourceSlopeNonnegative source

    oneBelow : 1ℚ ≤ S + 1ℚ
    oneBelow =
      let
        raw : 0ℚ + 1ℚ ≤ S + 1ℚ
        raw = ℚP.+-mono-≤ slopeNN ℚP.≤-refl
      in
      subst (λ left → left ≤ S + 1ℚ) (ℚP.+-identityˡ 1ℚ) raw

    twoNN : 0ℚ ≤ Cubic.twoℚ
    twoNN = ℚP.nonNegative⁻¹ Cubic.twoℚ
  in
  Norm.scaleNonnegative Cubic.twoℚ twoNN oneBelow

canonicalReciprocalAtMostHalf :
  (dataSet : FiniteQuarticResponseConstants) →
  Quot.positiveReciprocal
      (Choice.canonicalDenominator (asCanonicalSourceConstants dataSet))
      (Choice.canonicalDenominatorPositive (asCanonicalSourceConstants dataSet))
  ≤ Cubic.half
canonicalReciprocalAtMostHalf dataSet =
  let
    source = asCanonicalSourceConstants dataSet
    D = Choice.canonicalDenominator source
    Dpos = Choice.canonicalDenominatorPositive source
    twoPos : 0ℚ < Cubic.twoℚ
    twoPos = ℚP.positive⁻¹ Cubic.twoℚ
    anti = Quot.reciprocalAntitonePositive
      Cubic.twoℚ D twoPos Dpos (denominatorAtLeastTwo dataSet)

    halfAsReciprocal :
      Quot.positiveReciprocal Cubic.twoℚ twoPos ≡ Cubic.half
    halfAsReciprocal = refl
  in
  subst
    (λ right → Quot.positiveReciprocal D Dpos ≤ right)
    halfAsReciprocal
    anti

canonicalQuarticResponseGammaAtMostHalf :
  (dataSet : FiniteQuarticResponseConstants) →
  canonicalQuarticResponseGamma dataSet ≤ Cubic.half
canonicalQuarticResponseGammaAtMostHalf dataSet =
  let
    source = asCanonicalSourceConstants dataSet
    D = Choice.canonicalDenominator source
    Dpos = Choice.canonicalDenominatorPositive source

    first = Norm.scaleNonnegative
      (gaussianFloor dataSet)
      (ℚP.<⇒≤ (gaussianFloorPositive dataSet))
      (canonicalReciprocalAtMostHalf dataSet)

    halfNN : 0ℚ ≤ Cubic.half
    halfNN = ℚP.nonNegative⁻¹ Cubic.half
    second = Norm.scaleʳ-nonNeg halfNN (gaussianFloorAtMostOne dataSet)
  in
  ℚP.≤-trans first
    (subst
      (λ right → gaussianFloor dataSet * Cubic.half ≤ right)
      (ℚP.*-identityˡ Cubic.half)
      second)

canonicalQuarticResponseGammaAtMostOne :
  (dataSet : FiniteQuarticResponseConstants) →
  canonicalQuarticResponseGamma dataSet ≤ 1ℚ
canonicalQuarticResponseGammaAtMostOne dataSet =
  ℚP.≤-trans
    (canonicalQuarticResponseGammaAtMostHalf dataSet)
    (toWitness {a? = Cubic.half ℚP.≤? 1ℚ} _)

rowAQuarticResponseCanonicalChoiceLevel : ProofLevel
rowAQuarticResponseCanonicalChoiceLevel = machineChecked

rowAQuarticResponseCanonicalCapAtMostOneLevel : ProofLevel
rowAQuarticResponseCanonicalCapAtMostOneLevel = machineChecked

-- With the fixed Ward floor, `gaussianFloorAtMostOne` is exact arithmetic.  The
-- remaining physical inputs are finite source constants C,L,R,D on the same
-- literal trajectory; the coupling cap then exists constructively and is <=1.
literalFiniteQuarticResponseConstantsLevel : ProofLevel
literalFiniteQuarticResponseConstantsLevel = conditional
