module DASHI.Physics.YangMills.BalabanSU2AdOperator where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; _*R_; -R_; oneR)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; su2Lie; su2LieExt; lieAdd; lieScale)
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  (su2Dot)
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  (twoR; lieBracket; adOperator; lieBracketAddRight; lieBracketScaleRight)
open import DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction using
  (adCubicReduction)

lieNormSquared : SU2LieAlgebra → ℝ
lieNormSquared X = su2Dot X X

fourR : ℝ
fourR = twoR *R twoR

cAd : ℝ
cAd = fourR

adAdd :
  ∀ Y X Z →
  adOperator Y (lieAdd X Z)
    ≡ lieAdd (adOperator Y X) (adOperator Y Z)
adAdd Y X Z = lieBracketAddRight Y X Z

adScale :
  ∀ Y scalar X →
  adOperator Y (lieScale scalar X)
    ≡ lieScale scalar (adOperator Y X)
adScale Y scalar X = lieBracketScaleRight scalar Y X

-- With [X,Y] = 2 X×Y, ad_Y^3 = -4 |Y|² ad_Y.
adCubic :
  ∀ Y X →
  adOperator Y (adOperator Y (adOperator Y X))
    ≡ lieScale
        (-R (cAd *R lieNormSquared Y))
        (adOperator Y X)
adCubic Y X = adCubicReduction Y X
