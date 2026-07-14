module DASHI.Physics.Closure.NSTriadKNStrictExactQNGramRoute where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Data.Nat using (_≤_; _<_; _∸_; _≥_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; *-mono-≤; <⇒≤; ∸-monoˡ-≤)

import DASHI.Physics.Closure.NSTriadKNExactGramBaseFormBridge as ExactGram
import DASHI.Physics.Closure.NSTriadKNExactQNBaseForm as ExactQN
import DASHI.Physics.Closure.NSTriadKNGramRayleighBaseForm as GramRayleigh
import DASHI.Physics.Closure.NSTriadKNGramRayleighMarginAuditReceipt as RayleighAudit
import DASHI.Physics.Closure.NSTriadKNQGapTransfer as QGap
import DASHI.Physics.Closure.NSTriadKNRayleighCoercivityStage3MarginBridge as Stage3
import DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom as ScaleHeadroom
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm

------------------------------------------------------------------------
-- Strict replacement for the saturated C_err = 4 route.
--
-- The least Nat-valued base constant that can beat C_err = 4 is 5.  The
-- central theorem-facing obligation is therefore the exact pointwise
-- inequality below, with the exact QN base form fixed to exactKNAQBase.
-- This module records the obligation; it does not provide an analytic
-- witness for it.

saturatedStage3ErrorConstant : Nat
saturatedStage3ErrorConstant = 4

minimalStrictBaseGapConstant : Nat
minimalStrictBaseGapConstant = 5

fourLessThanFive : saturatedStage3ErrorConstant < minimalStrictBaseGapConstant
fourLessThanFive = ≤-refl

record StrictExactQNGramBaseFormRoute
    (N : Nat)
    (scale : ScaleHeadroom.CompatibilityScale N)
    (strongNormSquared : ResidueNorm.ResidueEnergyCarrier N → Nat)
    : Setω where
  constructor mkStrictExactQNGramBaseFormRoute
  field
    exactBaseFormIdentification :
      ExactGram.ExactKNABaseQuadraticFormIdentificationTarget
        (ResidueNorm.ResidueEnergyCarrier N)

    exactBaseFormAgreement :
      (x : ResidueNorm.ResidueEnergyCarrier N) →
      ExactGram.ExactKNABaseQuadraticFormIdentificationTarget.baseQuadraticForm
        exactBaseFormIdentification x
        ≡
      ExactQN.exactKNAQBase x

    rayleighReceipt :
      RayleighAudit.NSTriadKNGramRayleighMarginAuditReceipt

    rayleighReceiptRecorded :
      RayleighAudit.failClosed rayleighReceipt ≡ true

    baseGapConstant : Nat

    baseGapExceedsSaturatedError :
      saturatedStage3ErrorConstant < baseGapConstant

    baseGapPositive : Set

    strictBaseCoercive :
      (x : ResidueNorm.ResidueEnergyCarrier N) →
      baseGapConstant * strongNormSquared x
        ≤
      ScaleHeadroom.CompatibilityScale.scaleSq scale
        * ExactQN.exactKNAQBase x

open StrictExactQNGramBaseFormRoute public

------------------------------------------------------------------------
-- Algebraic consequence: every strict base constant above 4 dominates the
-- minimal replacement constant 5.

baseGapAtLeastMinimalStrictConstant :
  {N : Nat} →
  {scale : ScaleHeadroom.CompatibilityScale N} →
  {strongNormSquared : ResidueNorm.ResidueEnergyCarrier N → Nat} →
  (route : StrictExactQNGramBaseFormRoute N scale strongNormSquared) →
  minimalStrictBaseGapConstant ≤ baseGapConstant route
baseGapAtLeastMinimalStrictConstant route =
  baseGapExceedsSaturatedError route

------------------------------------------------------------------------
-- This is the exact replacement inequality at saturated C_err = 4.

strictCoercivityReplacementAtCerr4 :
  {N : Nat} →
  {scale : ScaleHeadroom.CompatibilityScale N} →
  {strongNormSquared : ResidueNorm.ResidueEnergyCarrier N → Nat} →
  (route : StrictExactQNGramBaseFormRoute N scale strongNormSquared) →
  (x : ResidueNorm.ResidueEnergyCarrier N) →
  minimalStrictBaseGapConstant * strongNormSquared x
    ≤
  ScaleHeadroom.CompatibilityScale.scaleSq scale
    * ExactQN.exactKNAQBase x
strictCoercivityReplacementAtCerr4
  {strongNormSquared = strongNormSquared}
  route x =
  ≤-trans
    (*-mono-≤
      (baseGapAtLeastMinimalStrictConstant route)
      (≤-refl))
    (strictBaseCoercive route x)

strictReplacementMarginAtCerr4 : Nat
strictReplacementMarginAtCerr4 =
  minimalStrictBaseGapConstant ∸ saturatedStage3ErrorConstant

strictReplacementMarginAtCerr4IsOne :
  strictReplacementMarginAtCerr4 ≡ suc zero
strictReplacementMarginAtCerr4IsOne =
  refl

strictReplacementMarginPositive :
  zero < strictReplacementMarginAtCerr4
strictReplacementMarginPositive =
  QGap.positiveDifferenceFromStrictLess
    saturatedStage3ErrorConstant
    minimalStrictBaseGapConstant
    fourLessThanFive

------------------------------------------------------------------------
-- The same obligation can feed the existing Stage 3 core and Gram-Rayleigh
-- target surfaces.  These are conversions only; the route remains open until
-- a caller supplies strictBaseCoercive.

toStage3MarginCore :
  {N : Nat} →
  {scale : ScaleHeadroom.CompatibilityScale N} →
  {strongNormSquared : ResidueNorm.ResidueEnergyCarrier N → Nat} →
  (route : StrictExactQNGramBaseFormRoute N scale strongNormSquared) →
  Stage3.NegativeFrameRayleighMarginCore
    (ResidueNorm.ResidueEnergyCarrier N)
    N
    strongNormSquared
    ExactQN.exactKNAQBase
    saturatedStage3ErrorConstant
toStage3MarginCore {scale = scale} route =
  Stage3.mkNegativeFrameRayleighMarginCore
    (baseGapConstant route)
    (baseGapPositive route)
    scale
    (strictBaseCoercive route)
    (baseGapExceedsSaturatedError route)

toGramRayleighBaseFormTarget :
  {N : Nat} →
  {scale : ScaleHeadroom.CompatibilityScale N} →
  {strongNormSquared : ResidueNorm.ResidueEnergyCarrier N → Nat} →
  (route : StrictExactQNGramBaseFormRoute N scale strongNormSquared) →
  GramRayleigh.GramRayleighBaseFormTarget
    (ResidueNorm.ResidueEnergyCarrier N)
    N
    strongNormSquared
    saturatedStage3ErrorConstant
toGramRayleighBaseFormTarget {scale = scale} route =
  GramRayleigh.mkGramRayleighBaseFormTarget
    (ExactGram.ExactKNAPositiveSubspaceCarrierTarget.gramCoercivityReceipt
      (ExactGram.ExactKNABaseQuadraticFormIdentificationTarget.positiveSubspaceCarrier
        (exactBaseFormIdentification route)))
    (rayleighReceipt route)
    (ExactGram.ExactKNAPositiveSubspaceCarrierTarget.gramCoercivityRecorded
      (ExactGram.ExactKNABaseQuadraticFormIdentificationTarget.positiveSubspaceCarrier
        (exactBaseFormIdentification route)))
    (rayleighReceiptRecorded route)
    ExactQN.exactKNAQBase
    (baseGapConstant route)
    (baseGapPositive route)
    scale
    (strictBaseCoercive route)
    (baseGapExceedsSaturatedError route)

------------------------------------------------------------------------
-- QGap algebraic consequences after the independent error and decomposition
-- obligations are supplied.

record StrictExactQNQGapInputs
    {N : Nat}
    {scale : ScaleHeadroom.CompatibilityScale N}
    {strongNormSquared : ResidueNorm.ResidueEnergyCarrier N → Nat}
    (route : StrictExactQNGramBaseFormRoute N scale strongNormSquared)
    : Setω where
  constructor mkStrictExactQNQGapInputs
  field
    qError : ResidueNorm.ResidueEnergyCarrier N → Nat
    qGap : ResidueNorm.ResidueEnergyCarrier N → Nat

    scaledErrorBound :
      (x : ResidueNorm.ResidueEnergyCarrier N) →
      ScaleHeadroom.CompatibilityScale.scaleSq scale * qError x
        ≤
      saturatedStage3ErrorConstant * strongNormSquared x

    gapDecomposition :
      (x : ResidueNorm.ResidueEnergyCarrier N) →
      qGap x ≡ ExactQN.exactKNAQBase x ∸ qError x

open StrictExactQNQGapInputs public

strictQGapMarginAtCerr4 :
  {N : Nat} →
  {scale : ScaleHeadroom.CompatibilityScale N} →
  {strongNormSquared : ResidueNorm.ResidueEnergyCarrier N → Nat} →
  (route : StrictExactQNGramBaseFormRoute N scale strongNormSquared) →
  QGap.GapMargin
strictQGapMarginAtCerr4 route =
  QGap.strictGapMarginFromConstants
    (baseGapConstant route)
    saturatedStage3ErrorConstant
    (baseGapExceedsSaturatedError route)

strictQGapMarginEquationAtCerr4 :
  {N : Nat} →
  {scale : ScaleHeadroom.CompatibilityScale N} →
  {strongNormSquared : ResidueNorm.ResidueEnergyCarrier N → Nat} →
  (route : StrictExactQNGramBaseFormRoute N scale strongNormSquared) →
  baseGapConstant route ≡
    saturatedStage3ErrorConstant
      + (baseGapConstant route ∸ saturatedStage3ErrorConstant)
strictQGapMarginEquationAtCerr4 route =
  QGap.baseMinusErrorEquation
    (baseGapConstant route)
    saturatedStage3ErrorConstant
    (<⇒≤ (baseGapExceedsSaturatedError route))

strictQGapAbsorptionAtCerr4 :
  {N : Nat} →
  {scale : ScaleHeadroom.CompatibilityScale N} →
  {strongNormSquared : ResidueNorm.ResidueEnergyCarrier N → Nat} →
  (route : StrictExactQNGramBaseFormRoute N scale strongNormSquared) →
  (inputs : StrictExactQNQGapInputs route) →
  (x : ResidueNorm.ResidueEnergyCarrier N) →
  ScaleHeadroom.CompatibilityScale.scaleSq scale
    * StrictExactQNQGapInputs.qGap inputs x
    ≥
  (baseGapConstant route ∸ saturatedStage3ErrorConstant)
    * strongNormSquared x
strictQGapAbsorptionAtCerr4
  {scale = scale}
  {strongNormSquared = strongNormSquared}
  route inputs x =
  QGap.strictScaledBaseGapMinusErrorAbsorption
    scale
    ExactQN.exactKNAQBase
    (StrictExactQNQGapInputs.qError inputs)
    (StrictExactQNQGapInputs.qGap inputs)
    strongNormSquared
    (baseGapConstant route)
    saturatedStage3ErrorConstant
    (strictBaseCoercive route)
    (StrictExactQNQGapInputs.scaledErrorBound inputs)
    (StrictExactQNQGapInputs.gapDecomposition inputs)
    (baseGapExceedsSaturatedError route)
    x

strictQGapAbsorptionAtMinimalReplacement :
  {N : Nat} →
  {scale : ScaleHeadroom.CompatibilityScale N} →
  {strongNormSquared : ResidueNorm.ResidueEnergyCarrier N → Nat} →
  (route : StrictExactQNGramBaseFormRoute N scale strongNormSquared) →
  (inputs : StrictExactQNQGapInputs route) →
  (x : ResidueNorm.ResidueEnergyCarrier N) →
  ScaleHeadroom.CompatibilityScale.scaleSq scale
    * StrictExactQNQGapInputs.qGap inputs x
    ≥
  (minimalStrictBaseGapConstant ∸ saturatedStage3ErrorConstant)
    * strongNormSquared x
strictQGapAbsorptionAtMinimalReplacement
  {scale = scale}
  {strongNormSquared = strongNormSquared}
  route inputs x =
  ≤-trans
    (*-mono-≤
      (∸-monoˡ-≤
        saturatedStage3ErrorConstant
        (baseGapAtLeastMinimalStrictConstant route))
      (≤-refl {strongNormSquared x}))
    (strictQGapAbsorptionAtCerr4 route inputs x)
