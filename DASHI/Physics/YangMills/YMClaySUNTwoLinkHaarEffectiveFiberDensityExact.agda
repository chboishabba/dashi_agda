module DASHI.Physics.YangMills.YMClaySUNTwoLinkHaarEffectiveFiberDensityExact where

------------------------------------------------------------------------
-- R443 -> R445 physical interface: EXACT two-link Haar disintegration.
--
-- For the native SU(N) product block B(U,V) = U*V and ANY integrable
-- original two-link density g(U,V), the Haar weighted pushforward
-- admits an EXPLICIT coarse density:
--
--   rho_g(W) = integral_U g(U, (inverse U)*W) dH(U)
--
--   integral_U integral_V g(U,V) F(U*V) dH(V) dH(U)
--     = integral_W rho_g(W) F(W) dH(W).
--
-- This is a derivation, NOT an independent effective-action density
-- assumption. It follows only from the existing certified SU(N)
-- group laws, one-link bilateral Haar invariance, finite Fubini,
-- pointwise congruence and scalar linearity.
--
-- The full interacting R445 side-four -> side-two block includes
-- an entire lattice and coupled original Wilson weight. Its
-- corresponding global disintegration, physical residual estimate
-- and cutoff-uniform RG rate remain OPEN. No m_eff is postulated.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Vec.Base as Vec using (Vec)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; 1ℝ; _*ℝ_; _≤ℝ_; *-comm; mulOneʳ)

import DASHI.Physics.YangMills.CompactLieGroupCore as Group
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

  product : Link → Link → Link
  product = SUN.sunMultiply theory

  inverse : Link → Link
  inverse = SUN.sunInverse theory

  -- Actual group cancellation; no gauge-fixing/exponential chart.
  nativeInverseLeftProductCancellation :
    (U V : Link) → product (inverse U) (product U V) ≡ V
  nativeInverseLeftProductCancellation U V =
    trans
      (sym (Group.multiplyAssociative
        (SUN.sunMatrixGroup theory) (inverse U) U V))
      (trans
        (cong (λ X → product X V)
          (Group.inverseLeft (SUN.sunMatrixGroup theory) U))
        (Group.identityLeft (SUN.sunMatrixGroup theory) V))

  -- This is the EXACT finite two-link multiplication pushforward.
  -- An interacting g may be non-factorizing; that is supported.
  fineTwoLinkWeightedNumerator :
    (Link → Link → ℝ) → (Link → ℝ) → ℝ
  fineTwoLinkWeightedNumerator density observable =
    Haar.integrateOne oneLink
      (λ U → Haar.integrateOne oneLink
        (λ V → density U V *ℝ observable (product U V)))

  -- The effective density is computed from the ORIGINAL weight g.
  -- No new positivity assumption or conditional probability kernel.
  effectiveOneLinkDensity :
    (Link → Link → ℝ) → Link → ℝ
  effectiveOneLinkDensity density W =
    Haar.integrateOne oneLink
      (λ U → density U (product (inverse U) W))

  effectiveOneLinkWeightedNumerator :
    (Link → Link → ℝ) → (Link → ℝ) → ℝ
  effectiveOneLinkWeightedNumerator density observable =
    Haar.integrateOne oneLink
      (λ W → effectiveOneLinkDensity density W *ℝ observable W)

  -- The coordinate substitution W=U*V is paid by ACTUAL one-link
  -- Haar left invariance; no invented Lebesgue Jacobian.
  weightedFiberChangeOfVariables :
    (density : Link → Link → ℝ)
    (observable : Link → ℝ)
    (U : Link) →
    Haar.integrateOne oneLink
      (λ V → density U V *ℝ observable (product U V))
    ≡ Haar.integrateOne oneLink
      (λ W → density U (product (inverse U) W) *ℝ observable W)
  weightedFiberChangeOfVariables density observable U =
    trans
      (Haar.integrateCongruent oneLink
        (λ V → density U V *ℝ observable (product U V))
        (λ V →
          density U (product (inverse U) (product U V))
            *ℝ observable (product U V))
        (λ V →
          cong
            (λ X → density U X *ℝ observable (product U V))
            (sym (nativeInverseLeftProductCancellation U V))))
      (Bilateral.oneLeftInvariant bilateral U
        (λ W →
          density U (product (inverse U) W) *ℝ observable W))

  -- Pull the fixed coarse observable outside the fiber integral
  -- from the ORIGINAL one-link scalar linearity, not an analytic
  -- integration theorem on unspecified measures.
  weightedFiberScalarFactor :
    (density : Link → Link → ℝ)
    (observable : Link → ℝ)
    (W : Link) →
    Haar.integrateOne oneLink
      (λ U →
        density U (product (inverse U) W) *ℝ observable W)
    ≡ effectiveOneLinkDensity density W *ℝ observable W
  weightedFiberScalarFactor density observable W =
    trans
      (Haar.integrateCongruent oneLink
        (λ U →
          density U (product (inverse U) W) *ℝ observable W)
        (λ U →
          observable W *ℝ density U (product (inverse U) W))
        (λ U → *-comm
          (density U (product (inverse U) W)) (observable W)))
      (trans
        (Ordered.oneScale ordered (observable W)
          (λ U → density U (product (inverse U) W)))
        (*-comm (observable W)
          (effectiveOneLinkDensity density W)))

  -- All-test two-link weighted pushforward = exact explicit coarse
  -- density integration, through native Haar and group laws only.
  nativeTwoLinkWeightedPushforwardIsEffectiveDensity :
    (density : Link → Link → ℝ)
    (observable : Link → ℝ) →
    fineTwoLinkWeightedNumerator density observable
    ≡ effectiveOneLinkWeightedNumerator density observable
  nativeTwoLinkWeightedPushforwardIsEffectiveDensity density observable =
    trans
      (Haar.integrateCongruent oneLink
        (λ U → Haar.integrateOne oneLink
          (λ V → density U V *ℝ observable (product U V)))
        (λ U → Haar.integrateOne oneLink
          (λ W → density U (product (inverse U) W)
            *ℝ observable W))
        (weightedFiberChangeOfVariables density observable))
      (trans
        (Haar.integrateTwoSwap oneLink
          (λ U W →
            density U (product (inverse U) W)
              *ℝ observable W))
        (Haar.integrateCongruent oneLink
          (λ W → Haar.integrateOne oneLink
            (λ U → density U (product (inverse U) W)
              *ℝ observable W))
          (λ W →
            effectiveOneLinkDensity density W *ℝ observable W)
          (weightedFiberScalarFactor density observable)))

  -- At the unit test, original total fine weight = integrated
  -- exact effective density. This is equality of physical sources,
  -- not an independently stipulated partition normalization.
  nativeTwoLinkEffectiveDensityPreservesPartition :
    (density : Link → Link → ℝ) →
    fineTwoLinkWeightedNumerator density (λ _ → 1ℝ)
    ≡ Haar.integrateOne oneLink (effectiveOneLinkDensity density)
  nativeTwoLinkEffectiveDensityPreservesPartition density =
    trans
      (nativeTwoLinkWeightedPushforwardIsEffectiveDensity
        density (λ _ → 1ℝ))
      (Haar.integrateCongruent oneLink
        (λ W → effectiveOneLinkDensity density W *ℝ 1ℝ)
        (effectiveOneLinkDensity density)
        (λ W → mulOneʳ (effectiveOneLinkDensity density W)))

  -- E1 finite reference positivity, on the SAME weighted fiber.
  -- This consumes only the already-selected one-link Haar positivity;
  -- no separately stipulated effective coarse positivity record.
  nativeEffectiveFiberDensityPreservesPositivity :
    (density : Link → Link → ℝ) →
    (∀ U V → 0ℝ ≤ℝ density U V) →
    (W : Link) →
    0ℝ ≤ℝ effectiveOneLinkDensity density W
  nativeEffectiveFiberDensityPreservesPositivity density positive W =
    Ordered.onePositive ordered
      (λ U → density U (product (inverse U) W))
      (λ U → positive U (product (inverse U) W))

  -- Pure normalized one-link Haar is the exact density image of
  -- the two-link UNIT Wilson reference. There is no Gaussian field.
  nativeEffectiveFiberUnitWeightIsUnit :
    (W : Link) →
    effectiveOneLinkDensity (λ _ _ → 1ℝ) W ≡ 1ℝ
  nativeEffectiveFiberUnitWeightIsUnit W =
    Haar.integrateUnit oneLink

  -- On the source's all-test integrable algebra, the zero-interaction
  -- two-link weighted pushforward agrees with one-link Haar, not only
  -- with a specified test class or a formal density.
  nativeUnitWeightBlockedNumeratorIsHaar :
    (observable : Link → ℝ) →
    fineTwoLinkWeightedNumerator (λ _ _ → 1ℝ) observable
      ≡ Haar.integrateOne oneLink observable
  nativeUnitWeightBlockedNumeratorIsHaar observable =
    trans
      (nativeTwoLinkWeightedPushforwardIsEffectiveDensity
        (λ _ _ → 1ℝ) observable)
      (Haar.integrateCongruent oneLink
        (λ W →
          effectiveOneLinkDensity (λ _ _ → 1ℝ) W
            *ℝ observable W)
        observable
        (λ W →
          trans
            (cong (λ scalar → scalar *ℝ observable W)
              (nativeEffectiveFiberUnitWeightIsUnit W))
            (trans
              (*-comm 1ℝ (observable W))
              (mulOneʳ (observable W)))))

  ----------------------------------------------------------------------
  -- P0.E kernel-valued, arbitrary-interaction version.
  --
  -- The earlier weighted scalar theorem factors an observable out of
  -- a single fiber. This stronger identity changes variables for an
  -- arbitrary h(U,V,W), including a kernel with *all* remaining fine
  -- links and a coupled Wilson action inside it. No product form of
  -- the weight, independence assumption, or analytic approximation.
  ----------------------------------------------------------------------

  nativeTwoLinkKernelChangeOfVariables :
    (kernel : Link → Link → Link → ℝ) →
    Haar.integrateOne oneLink
      (λ U → Haar.integrateOne oneLink
        (λ V → kernel U V (product U V)))
    ≡ Haar.integrateOne oneLink
      (λ W → Haar.integrateOne oneLink
        (λ U → kernel U (product (inverse U) W) W))
  nativeTwoLinkKernelChangeOfVariables kernel =
    trans
      (Haar.integrateCongruent oneLink
        (λ U → Haar.integrateOne oneLink
          (λ V → kernel U V (product U V)))
        (λ U → Haar.integrateOne oneLink
          (λ W → kernel U (product (inverse U) W) W))
        (λ U →
          trans
            (Haar.integrateCongruent oneLink
              (λ V → kernel U V (product U V))
              (λ V →
                kernel U
                  (product (inverse U) (product U V))
                  (product U V))
              (λ V →
                cong
                  (λ value → kernel U value (product U V))
                  (sym (nativeInverseLeftProductCancellation U V))))
            (Bilateral.oneLeftInvariant bilateral U
              (λ W → kernel U (product (inverse U) W) W))))
      (Haar.integrateTwoSwap oneLink
        (λ U W → kernel U (product (inverse U) W) W))

  -- Strong local R445 source interface: a single native two-link
  -- product with ANY finite number m of residual original fine links.
  -- The actual Wilson density may couple U, V and all residual links.
  -- It remains INSIDE the SAME integral on both sides.
  nativeOnePairAllInteriorWeightedChangeOfVariables :
    ∀ {m}
      (density : Link → Link → Vec Link m → ℝ)
      (observable : Link → ℝ) →
    Haar.integrateOne oneLink
      (λ U → Haar.integrateOne oneLink
        (λ V →
          Haar.productIntegral {n = m} oneLink
            (λ interior →
              density U V interior *ℝ observable (product U V))))
    ≡ Haar.integrateOne oneLink
      (λ W → Haar.integrateOne oneLink
        (λ U →
          Haar.productIntegral {n = m} oneLink
            (λ interior →
              density U (product (inverse U) W) interior
                *ℝ observable W)))
  nativeOnePairAllInteriorWeightedChangeOfVariables
      {m} density observable =
    nativeTwoLinkKernelChangeOfVariables
      (λ U V W →
        Haar.productIntegral {n = m} oneLink
          (λ interior → density U V interior *ℝ observable W))
