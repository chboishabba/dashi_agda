{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact where

------------------------------------------------------------------------
-- ROUND104 BC1: FINITE CMP116 SMALLNESS DEMANDS -> CANONICAL COMMON RADIUS
--
-- CMP116 Sect.1 does not require a distinguished numerical radius.  Its
-- analyticity proof produces finitely many inequalities of the schematic form
--
--       c_i * epsilon < reserve_i.
--
-- After dividing each finite positive reserve into its coefficient, write the
-- normalized demands as lambda_i >= 0 and require lambda_i * epsilon < 1.
-- There is no need to leave existence of epsilon as another physical theorem:
-- sum the finitely many normalized demands S and choose
--
--       epsilon_* = 1 / (2 (S + 1)).
--
-- The already-checked Row-A canonical-smallness arithmetic proves S epsilon_*<1;
-- every individual demand is below S, hence every source smallness condition is
-- paid simultaneously.  Physical work is reduced to obtaining the finite
-- normalized coefficients from CMP116 (1.13)--(1.22) on the literal family.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4RowACanonicalSmallCouplingChoiceExact as Canon

record CMP116FiniteNormalizedAnalyticDemands : Set where
  field
    propagatorDemand : ℚ
    linearizingFixedPointDemand : ℚ
    minimizerFixedPointDemand : ℚ
    substitutedBackgroundDemand : ℚ

    propagatorDemandNN : 0ℚ ≤ propagatorDemand
    linearizingFixedPointDemandNN : 0ℚ ≤ linearizingFixedPointDemand
    minimizerFixedPointDemandNN : 0ℚ ≤ minimizerFixedPointDemand
    substitutedBackgroundDemandNN : 0ℚ ≤ substitutedBackgroundDemand

open CMP116FiniteNormalizedAnalyticDemands public

totalDemand : CMP116FiniteNormalizedAnalyticDemands → ℚ
totalDemand d =
  propagatorDemand d
    + linearizingFixedPointDemand d
    + minimizerFixedPointDemand d
    + substitutedBackgroundDemand d

totalDemandNN :
  (d : CMP116FiniteNormalizedAnalyticDemands) → 0ℚ ≤ totalDemand d
totalDemandNN d =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (propagatorDemandNN d)
        (linearizingFixedPointDemandNN d))
      (minimizerFixedPointDemandNN d))
    (substitutedBackgroundDemandNN d)

asCanonicalSmallnessData :
  CMP116FiniteNormalizedAnalyticDemands → Canon.FiniteRowASourceConstants
asCanonicalSmallnessData d = record
  { Canon.FiniteRowASourceConstants.gaussianFloor = 1ℚ
  ; Canon.FiniteRowASourceConstants.interactionConstant = totalDemand d
  ; Canon.FiniteRowASourceConstants.derivativeBound = 0ℚ
  ; Canon.FiniteRowASourceConstants.gaussianFloorPositive = ℚP.positive⁻¹ 1ℚ
  ; Canon.FiniteRowASourceConstants.interactionConstantNonnegative = totalDemandNN d
  ; Canon.FiniteRowASourceConstants.derivativeBoundNonnegative = ℚP.≤-refl
  }

canonicalCommonRadius : CMP116FiniteNormalizedAnalyticDemands → ℚ
canonicalCommonRadius d = Canon.canonicalGamma (asCanonicalSmallnessData d)

canonicalCommonRadiusPositive :
  (d : CMP116FiniteNormalizedAnalyticDemands) → 0ℚ < canonicalCommonRadius d
canonicalCommonRadiusPositive d =
  Canon.canonicalGammaPositive (asCanonicalSmallnessData d)

totalDemandTimesRadiusBelowOne :
  (d : CMP116FiniteNormalizedAnalyticDemands) →
  totalDemand d * canonicalCommonRadius d < 1ℚ
totalDemandTimesRadiusBelowOne d =
  Canon.canonicalGammaPaysCombinedSmallness (asCanonicalSmallnessData d)

propagatorBelowTotal :
  (d : CMP116FiniteNormalizedAnalyticDemands) →
  propagatorDemand d ≤ totalDemand d
propagatorBelowTotal d =
  let
    tailNN = ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (linearizingFixedPointDemandNN d)
        (minimizerFixedPointDemandNN d))
      (substitutedBackgroundDemandNN d)
  in
  subst
    (λ right → propagatorDemand d ≤ right)
    (ℚP.+-assoc
      (propagatorDemand d)
      (linearizingFixedPointDemand d)
      (minimizerFixedPointDemand d + substitutedBackgroundDemand d))
    (ℚP.+-monoʳ-≤ (propagatorDemand d) tailNN)

linearizingBelowTotal :
  (d : CMP116FiniteNormalizedAnalyticDemands) →
  linearizingFixedPointDemand d ≤ totalDemand d
linearizingBelowTotal d =
  let
    leftNN = propagatorDemandNN d
    rightNN = ℚP.+-mono-≤
      (minimizerFixedPointDemandNN d)
      (substitutedBackgroundDemandNN d)
    first = ℚP.+-mono-≤ leftNN ℚP.≤-refl
    second = ℚP.+-monoʳ-≤
      (propagatorDemand d + linearizingFixedPointDemand d)
      rightNN
  in
  ℚP.≤-trans
    (subst
      (λ left → left ≤ propagatorDemand d + linearizingFixedPointDemand d)
      (ℚP.+-identityˡ (linearizingFixedPointDemand d))
      first)
    second

minimizerBelowTotal :
  (d : CMP116FiniteNormalizedAnalyticDemands) →
  minimizerFixedPointDemand d ≤ totalDemand d
minimizerBelowTotal d =
  let
    prefixNN = ℚP.+-mono-≤
      (propagatorDemandNN d)
      (linearizingFixedPointDemandNN d)
    first = ℚP.+-mono-≤ prefixNN ℚP.≤-refl
    second = ℚP.+-monoʳ-≤
      ((propagatorDemand d + linearizingFixedPointDemand d)
        + minimizerFixedPointDemand d)
      (substitutedBackgroundDemandNN d)
  in
  ℚP.≤-trans
    (subst
      (λ left → left ≤
        (propagatorDemand d + linearizingFixedPointDemand d)
          + minimizerFixedPointDemand d)
      (ℚP.+-identityˡ (minimizerFixedPointDemand d))
      first)
    second

substitutedBelowTotal :
  (d : CMP116FiniteNormalizedAnalyticDemands) →
  substitutedBackgroundDemand d ≤ totalDemand d
substitutedBelowTotal d =
  let
    prefixNN = ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (propagatorDemandNN d)
        (linearizingFixedPointDemandNN d))
      (minimizerFixedPointDemandNN d)
  in
  subst
    (λ left → left ≤ totalDemand d)
    (ℚP.+-identityˡ (substitutedBackgroundDemand d))
    (ℚP.+-mono-≤ prefixNN ℚP.≤-refl)

individualDemandPaid :
  (d : CMP116FiniteNormalizedAnalyticDemands) →
  (demand : ℚ) →
  demand ≤ totalDemand d →
  0ℚ ≤ demand →
  demand * canonicalCommonRadius d < 1ℚ
individualDemandPaid d demand demand≤total demandNN =
  let
    radiusNN = ℚP.<⇒≤ (canonicalCommonRadiusPositive d)
    scaled = ℚP.*-mono-≤
      demandNN demand≤total
      radiusNN ℚP.≤-refl
  in
  ℚP.≤-<-trans scaled (totalDemandTimesRadiusBelowOne d)

propagatorDemandPaid :
  (d : CMP116FiniteNormalizedAnalyticDemands) →
  propagatorDemand d * canonicalCommonRadius d < 1ℚ
propagatorDemandPaid d = individualDemandPaid d
  (propagatorDemand d) (propagatorBelowTotal d) (propagatorDemandNN d)

linearizingFixedPointDemandPaid :
  (d : CMP116FiniteNormalizedAnalyticDemands) →
  linearizingFixedPointDemand d * canonicalCommonRadius d < 1ℚ
linearizingFixedPointDemandPaid d = individualDemandPaid d
  (linearizingFixedPointDemand d) (linearizingBelowTotal d)
  (linearizingFixedPointDemandNN d)

minimizerFixedPointDemandPaid :
  (d : CMP116FiniteNormalizedAnalyticDemands) →
  minimizerFixedPointDemand d * canonicalCommonRadius d < 1ℚ
minimizerFixedPointDemandPaid d = individualDemandPaid d
  (minimizerFixedPointDemand d) (minimizerBelowTotal d)
  (minimizerFixedPointDemandNN d)

substitutedBackgroundDemandPaid :
  (d : CMP116FiniteNormalizedAnalyticDemands) →
  substitutedBackgroundDemand d * canonicalCommonRadius d < 1ℚ
substitutedBackgroundDemandPaid d = individualDemandPaid d
  (substitutedBackgroundDemand d) (substitutedBelowTotal d)
  (substitutedBackgroundDemandNN d)

cmp116CanonicalCommonRadiusCompilerLevel : ProofLevel
cmp116CanonicalCommonRadiusCompilerLevel = machineChecked

-- Physical/source leaf: extract finite nonnegative normalized demand constants
-- from the literal CMP116 inequalities (1.13)--(1.22).  Once supplied, existence
-- and positivity of a common radius and all four smallness gates are theorem-owned.
literalCMP116FiniteNormalizedDemandExtractionLevel : ProofLevel
literalCMP116FiniteNormalizedDemandExtractionLevel = conditional
