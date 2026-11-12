module DASHI.Physics.YangMills.YMClaySUNOneLinkHaarConvolutionSourceExact where

------------------------------------------------------------------------
-- R443 -> R445: EXACT CONVOLUTION OF TWO ORIGINAL SU(N) HAAR LINKS.
--
-- The native SU(N) link multiplication of two independently Haar-
-- integrated links has precisely the original one-link Haar law.
-- Proof uses the SAME existing one-link Haar interface, its genuine
-- left/right invariance, normalization, linearity and Fubini law.
--
-- This is not a new measure and introduces no postulates. It is the
-- zero-interaction reference calculation for a two-link RG block.
-- An interacting Wilson Gibbs density couples the fine links and
-- cannot be erased by this pure-Haar identity. No actual interacting
-- blocked-vs-bare density estimate, UV rate, or Clay mass gap follows.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 1ℝ; _*ℝ_; mulOneʳ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  oneLinkConstantIntegral :
    (scalar : ℝ) →
    Haar.integrateOne oneLink (λ (_ : Link) → scalar) ≡ scalar
  oneLinkConstantIntegral scalar =
    trans
      (Haar.integrateCongruent oneLink
        (λ (_ : Link) → scalar)
        (λ (_ : Link) → scalar *ℝ 1ℝ)
        (λ _ → sym (mulOneʳ scalar)))
      (trans
        (Ordered.oneScale ordered scalar (λ (_ : Link) → 1ℝ))
        (trans
          (cong (λ value → scalar *ℝ value)
            (Haar.integrateUnit oneLink))
          (mulOneʳ scalar)))

  -- Haar convolution, with outer U and inner V, for the NATIVE SU(N)
  -- multiplication. The inner integral is constant by one-left Haar
  -- translation invariance; no independent Haar convolution axiom.
  leftOrderedTwoLinkHaarConvolution :
    (test : Link → ℝ) →
    Haar.integrateOne oneLink
      (λ U → Haar.integrateOne oneLink
        (λ V → test (SUN.sunMultiply theory U V)))
    ≡ Haar.integrateOne oneLink test
  leftOrderedTwoLinkHaarConvolution test =
    trans
      (Haar.integrateCongruent oneLink
        (λ U → Haar.integrateOne oneLink
          (λ V → test (SUN.sunMultiply theory U V)))
        (λ (_ : Link) → Haar.integrateOne oneLink test)
        (λ U → Bilateral.oneLeftInvariant bilateral U test))
      (oneLinkConstantIntegral (Haar.integrateOne oneLink test))

  -- The opposite integration order is identical, using the *actual*
  -- right-invariance of the same one-link Haar functional.
  rightOrderedTwoLinkHaarConvolution :
    (test : Link → ℝ) →
    Haar.integrateOne oneLink
      (λ V → Haar.integrateOne oneLink
        (λ U → test (SUN.sunMultiply theory U V)))
    ≡ Haar.integrateOne oneLink test
  rightOrderedTwoLinkHaarConvolution test =
    trans
      (Haar.integrateCongruent oneLink
        (λ V → Haar.integrateOne oneLink
          (λ U → test (SUN.sunMultiply theory U V)))
        (λ (_ : Link) → Haar.integrateOne oneLink test)
        (λ V → Bilateral.oneRightInvariant bilateral V test))
      (oneLinkConstantIntegral (Haar.integrateOne oneLink test))

  -- Exact Haar/Fubini square for the product map. This is an all-test
  -- identity, not only a scalar/unit insertion.
  twoLinkMultiplicationHaarFubini :
    (test : Link → ℝ) →
    Haar.integrateOne oneLink
      (λ U → Haar.integrateOne oneLink
        (λ V → test (SUN.sunMultiply theory U V)))
    ≡
    Haar.integrateOne oneLink
      (λ V → Haar.integrateOne oneLink
        (λ U → test (SUN.sunMultiply theory U V)))
  twoLinkMultiplicationHaarFubini test =
    Haar.integrateTwoSwap oneLink
      (λ U V → test (SUN.sunMultiply theory U V))

  twoLinkHaarBothOrdersSameSource :
    (test : Link → ℝ) →
    Haar.integrateOne oneLink
      (λ U → Haar.integrateOne oneLink
        (λ V → test (SUN.sunMultiply theory U V)))
    ≡
    Haar.integrateOne oneLink
      (λ V → Haar.integrateOne oneLink
        (λ U → test (SUN.sunMultiply theory U V)))
  twoLinkHaarBothOrdersSameSource test =
    trans
      (leftOrderedTwoLinkHaarConvolution test)
      (sym (rightOrderedTwoLinkHaarConvolution test))
