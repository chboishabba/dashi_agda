{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4LinearInteractionBetaMarginExact where

------------------------------------------------------------------------
-- ROW A: SOURCE-LINEAR INTERACTION ABSORPTION
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- SOURCE-NATIVE MOTIVATION
--
-- After the literal fluctuation rescaling B = g_k B' in CMP109 (2.12), the
-- explicit P^(k) lane is analytic with coefficients O(g_k).  Thus the first
-- physical interaction estimate to attack is the scale-local bound
--
--        betaInt_j >= - C g_{j-1}.
--
-- If the SAME tuned trajectory already satisfies g_{j-1} <= gamma and the
-- constrained Gaussian calculation gives betaZ_j >= bMinus, then no geometric
-- summability assumption on sum_j g_j is needed:
--
--        beta_j >= bMinus - C gamma.
--
-- This matters because for a marginal asymptotically-free trajectory
-- g_j ~ (u_R + b(K-j))^(-1/2), the sum of g_j over a long terminal tail is
-- generally not uniformly bounded in its length.  Linear positive drift is
-- instead obtained shell-by-shell as soon as C gamma < bMinus.
--
-- The theorem below is exact ordered-rational algebra only.  It does NOT
-- produce the physical bMinus, C, or gamma bounds.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; -_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

record LinearInteractionShell
    (bMinus interactionConstant gamma : ℚ) : Set where
  field
    coupling betaZ betaInt : ℚ

    interactionConstantNonnegative : 0ℚ ≤ interactionConstant
    couplingNonnegative : 0ℚ ≤ coupling
    gammaNonnegative : 0ℚ ≤ gamma
    couplingBelowGamma : coupling ≤ gamma

    gaussianLower : bMinus ≤ betaZ
    interactionLower :
      - (interactionConstant * coupling) ≤ betaInt

open LinearInteractionShell public

linearMargin : ℚ → ℚ → ℚ → ℚ
linearMargin bMinus interactionConstant gamma =
  bMinus - interactionConstant * gamma

betaTotal :
  ∀ {bMinus interactionConstant gamma} →
  LinearInteractionShell bMinus interactionConstant gamma → ℚ
betaTotal shell = betaZ shell + betaInt shell

uniformInteractionLower :
  ∀ {bMinus interactionConstant gamma}
    (shell : LinearInteractionShell bMinus interactionConstant gamma) →
  - (interactionConstant * gamma) ≤ betaInt shell
uniformInteractionLower {interactionConstant = interactionConstant}
    {gamma = gamma} shell =
  let
    scaled : interactionConstant * coupling shell
      ≤ interactionConstant * gamma
    scaled = Norm.scaleNonnegative
      interactionConstant
      (interactionConstantNonnegative shell)
      (couplingBelowGamma shell)

    negated : - (interactionConstant * gamma)
      ≤ - (interactionConstant * coupling shell)
    negated = ℚP.neg-mono-≤ scaled
  in
  ℚP.≤-trans negated (interactionLower shell)

singleShellLinearMargin :
  ∀ {bMinus interactionConstant gamma}
    (shell : LinearInteractionShell bMinus interactionConstant gamma) →
  linearMargin bMinus interactionConstant gamma ≤ betaTotal shell
singleShellLinearMargin {bMinus = bMinus}
    {interactionConstant = interactionConstant}
    {gamma = gamma} shell =
  let
    summed :
      bMinus + (- (interactionConstant * gamma))
      ≤ betaZ shell + betaInt shell
    summed = ℚP.+-mono-≤
      (gaussianLower shell)
      (uniformInteractionLower shell)

    marginExact :
      bMinus + (- (interactionConstant * gamma))
      ≡ linearMargin bMinus interactionConstant gamma
    marginExact = ℚRing.solve-∀ bMinus interactionConstant gamma
  in
  subst
    (λ lower → lower ≤ betaTotal shell)
    marginExact
    summed

sumMonotone :
  ∀ {A : Set} (indices : List A) (lower upper : A → ℚ) →
  (∀ index → lower index ≤ upper index) →
  Sums.sumRational indices lower ≤ Sums.sumRational indices upper
sumMonotone [] lower upper pointwise = ℚP.≤-refl
sumMonotone (index ∷ indices) lower upper pointwise =
  ℚP.+-mono-≤
    (pointwise index)
    (sumMonotone indices lower upper pointwise)

-- Finite-prefix form.  The left side is exactly the repeated linear margin;
-- callers with a Nat-length bridge may rewrite it as
--
--      (# shells) * (bMinus - C gamma).
--
-- No assumption that sum coupling is bounded independently of prefix length
-- appears anywhere in this theorem.
finitePrefixLinearMargin :
  ∀ {bMinus interactionConstant gamma}
    (shells : List
      (LinearInteractionShell bMinus interactionConstant gamma)) →
  Sums.sumRational shells
      (λ _ → linearMargin bMinus interactionConstant gamma)
  ≤
  Sums.sumRational shells betaTotal
finitePrefixLinearMargin shells =
  sumMonotone
    shells
    (λ _ → linearMargin _ _ _)
    betaTotal
    singleShellLinearMargin
