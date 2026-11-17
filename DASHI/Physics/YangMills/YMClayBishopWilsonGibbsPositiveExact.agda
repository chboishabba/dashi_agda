module DASHI.Physics.YangMills.YMClayBishopWilsonGibbsPositiveExact where

------------------------------------------------------------------------
-- ACTUAL constructed Bishop exp(-S) strict positivity for any S >= 0.
-- Reuses existing ALL-REAL Cauchy-product exp(x)exp(-x)=1 and
-- positivity exp(x)>=1 for x>=0, plus real inverse positivity.
--
-- This removes the strict-exp-positive authority leaf from the
-- Bishop finite Wilson side: it is a CONSTRUCTED function/order theorem.
-- Remaining Wilson source: same-original-action nonnegativity,
-- product Haar, 4D plaquettes and the original carrier identification.
--
-- Attribution: Bishop–Bridges, Murray/Csimma, original DASHI
-- BishopExponentialSeriesConvergenceExact, CauchyProductExact,
-- PositiveOrderExact, BishopNegativeExponentialGlobalUnitIntervalExact,
-- Wilson/Balaban physical selected action.
------------------------------------------------------------------------

open import Data.Sum.Base using (inj₂)
import Real as B
import RealProperties as P
import Inverse as Inv
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as Positive
import DASHI.Foundations.BishopExponentialCauchyProductExact as Product
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact
  as Global

-- Positive side includes the ZERO action case, because exp(0)=1.
expOfNonnegativePositive :
  ∀ {action : B.ℝ} →
  B.NonNegative action →
  B._<_ B.0ℝ (Exp.bishopExp action)
expOfNonnegativePositive actionNN =
  P.<-≤-trans
    Global.onePositive
    (Positive.bishopExpAtLeastOneOnNonnegative actionNN)

positiveExpApart :
  ∀ {action : B.ℝ} →
  (actionNN : B.NonNegative action) →
  Exp.bishopExp action B.≄0
positiveExpApart actionNN =
  inj₂ (expOfNonnegativePositive actionNN)

-- Original Bishop exponentials on this SAME real carrier, not
-- independent abstract functions or an arbitrary divide parameter.
negativeExpIsInverseFromNonnegative :
  ∀ {action : B.ℝ} →
  (actionNN : B.NonNegative action) →
  B._≃_
    (Exp.bishopExp (B.- action))
    (Inv._⁻¹ (Exp.bishopExp action)
      (positiveExpApart actionNN))
negativeExpIsInverseFromNonnegative {action} actionNN =
  Inv.⁻¹-unique
    (Exp.bishopExp (B.- action))
    (Exp.bishopExp action)
    (positiveExpApart actionNN)
    (P.≃-trans
      (P.*-comm
        (Exp.bishopExp (B.- action))
        (Exp.bishopExp action))
      (Product.bishopExpTimesNegativeIsOne action))

-- This is the actual strict positive Gibbs density theorem.
-- Constructive: no decidable sign trichotomy or split action=0/>0.
bishopWilsonExpNegativeStrictPositive :
  ∀ {action : B.ℝ} →
  B.NonNegative action →
  B._<_ B.0ℝ (Exp.bishopExp (B.- action))
bishopWilsonExpNegativeStrictPositive actionNN =
  P.<-respʳ-≃
    (P.≃-symm
      (negativeExpIsInverseFromNonnegative actionNN))
    (Inv.0<x⇒0<x⁻¹
      (positiveExpApart actionNN)
      (expOfNonnegativePositive actionNN))

-- For an actual selected source action S_n(U), the remaining
-- SAME-OBJECT witness is: forall U, NonNegative(S_n(U)).
-- Feeding it to this theorem derives the Gibbs density positivity
-- required by the existing finite positive-weight integral proof.
bishopWilsonGibbsDensityPositiveAt :
  ∀ {Configuration : Set}
    (action : Configuration → B.ℝ)
    (actionNonnegative : ∀ U → B.NonNegative (action U))
    (U : Configuration) →
  B._<_ B.0ℝ (Exp.bishopExp (B.- (action U)))
bishopWilsonGibbsDensityPositiveAt action actionNonnegative U =
  bishopWilsonExpNegativeStrictPositive (actionNonnegative U)
