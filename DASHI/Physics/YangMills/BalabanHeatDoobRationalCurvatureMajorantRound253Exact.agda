{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanHeatDoobRationalCurvatureMajorantRound253Exact where

------------------------------------------------------------------------
-- ROUND253 / EXACT REAL LOG-HEAT SPLIT -> RATIONAL CURVATURE MAJORANT
--
-- The compact-group Heat/Doob identity is standard analysis and already wired
-- on the exact BC1 potential.  Once the static Hessian and gradient covariance
-- terms have rational majorants S and C, the actual log-heat Hessian has the
-- rational majorant S + C by the real absolute-value triangle inequality.
--
-- Hence a consumer must not carry an additional physical theorem
--   actualDebt <= staticDebt + covarianceDebt.
-- The RHS can be chosen as the actual rational debt by construction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; absℝ; _-ℝ_; _≤ℝ_; absSubadditive; +-mono-≤; ≤ℝ-trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2RationalShellBudgetToRealRound108Exact as Embed

record RationalMajorizedHeatDoobSplit
    (embedding : Embed.OrderedRationalRealRingEmbedding) : Set₁ where
  field
    actual static covariance : ℝ

    staticDebt covarianceDebt : ℚ
    staticDebtNonnegative : 0ℚ ≤ staticDebt
    covarianceDebtNonnegative : 0ℚ ≤ covarianceDebt

    exactStaticMinusCovariance :
      actual ≡ static -ℝ covariance

    staticAbsMajorized :
      absℝ static ≤ℝ Embed.embed embedding staticDebt

    covarianceAbsMajorized :
      absℝ covariance ≤ℝ Embed.embed embedding covarianceDebt

open RationalMajorizedHeatDoobSplit public

actualDebt :
  ∀ {embedding} → RationalMajorizedHeatDoobSplit embedding → ℚ
actualDebt dataSet = staticDebt dataSet + covarianceDebt dataSet

actualDebtNonnegative :
  ∀ {embedding}
    (dataSet : RationalMajorizedHeatDoobSplit embedding) →
  0ℚ ≤ actualDebt dataSet
actualDebtNonnegative dataSet =
  ℚP.+-mono-≤
    (staticDebtNonnegative dataSet)
    (covarianceDebtNonnegative dataSet)

actualAbsMajorized :
  ∀ {embedding}
    (dataSet : RationalMajorizedHeatDoobSplit embedding) →
  absℝ (actual dataSet)
  ≤ℝ Embed.embed embedding (actualDebt dataSet)
actualAbsMajorized {embedding} dataSet =
  subst
    (λ right → absℝ (actual dataSet) ≤ℝ right)
    (sym (Embed.addExact embedding (staticDebt dataSet) (covarianceDebt dataSet)))
    (subst
      (λ left → left
        ≤ℝ Embed.embed embedding (staticDebt dataSet)
          +ℝ Embed.embed embedding (covarianceDebt dataSet))
      (sym (congAbs (exactStaticMinusCovariance dataSet)))
      (≤ℝ-trans
        (absSubadditive (static dataSet) (covariance dataSet))
        (+-mono-≤
          (staticAbsMajorized dataSet)
          (covarianceAbsMajorized dataSet))))
  where
  open import DASHI.Foundations.RealAnalysisAxioms using (_+ℝ_)

  congAbs : ∀ {a b : ℝ} → a ≡ b → absℝ a ≡ absℝ b
  congAbs refl = refl

rationalHeatDoobMajorantCompilerLevel : ProofLevel
rationalHeatDoobMajorantCompilerLevel = machineChecked

heatDoobAbsoluteValueTriangleLevel : ProofLevel
heatDoobAbsoluteValueTriangleLevel = standardImported
