module DASHI.Physics.YangMills.YMClaySUNWeightedHaarPairFibreDisintegrationExact where

------------------------------------------------------------------------
-- R445.F17: WEIGHTED NONCOMMUTATIVE ONE-PAIR HAAR DISINTEGRATION.
--
-- This is stronger than unweighted Haar pair pushforward. For ANY
-- possibly nonfactorizing weight w(U,V), and original SUN multiplication,
-- derive the actual (unnormalized) cylinder identity
--
--  ∫ dH(U) dH(V) w(U,V) F(U·V)
--    = ∫ dH(W) [∫ dH(V) w(W·V⁻¹,V)] F(W).
--
-- The coarse effective *density* is therefore the explicit original
-- one-link fibre integral, not an assumed bare-Wilson Gibbs density.
--
-- The proof uses ONLY the ORIGINAL one-link right Haar invariance,
-- Fubini, linearity and the ORIGINAL SUN group inverse/associativity.
-- No new conditional probability kernel, abstract transformation oracle,
-- second Haar source, commutative SU(N) approximation, or new real field.
--
-- All required one-link integration laws are EXPLICIT INPUTS. The
-- existing OneLinkProductHaar is a total-function axiom interface on
-- legacy RealAnalysisAxioms; genuine Borel SU(N) Haar must still be
-- constructed/restricted to a measurable selected test algebra.
--
-- This is a single pair: the original side-four Wilson density also
-- depends on other fine links. Arbitrary external spectator dependence
-- is allowed pointwise, but global Fubini/reindex and the selected
-- 1024-bond decoder/effective action remain open. No all-scale RG
-- analytic estimate, reflection positivity, OS gap or Clay result.
--
-- Source attribution: Haar; Wilson (1974), Balaban; existing original
-- DASHI SUNMatrixCarrier/oneLink Haar/Fubini/rational-block owners.
-- SOURCE WRITTEN; exact-head Agda kernel NOT checked.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _<ℝ_; *-comm)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (source : Product.OneLinkProductHaar
      (SUN.SUNMatrixElement theory))
    (linear : Ordered.OneLinkOrderedHaarAlgebra source)
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory source)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  -- The very group used by the original native signed Wilson paths.
  originalGroup : Bond.ExactLinkGroup Link
  originalGroup = Native.sunExactSignedLinkGroup theory

  multiply : Link → Link → Link
  multiply = SUN.sunMultiply theory

  inverse : Link → Link
  inverse = SUN.sunInverse theory

  -- The exact right-translation cancellation in the original matrix
  -- group; neither commutativity nor U≈1 is involved.
  originalRightTranslationCancels :
    ∀ block fibre →
    multiply (multiply block (inverse fibre)) fibre ≡ block
  originalRightTranslationCancels block fibre =
    trans
      (Bond.multiplyAssociative originalGroup
        block (inverse fibre) fibre)
      (trans
        (cong (multiply block)
          (Bond.inverseLeft originalGroup fibre))
        (Bond.identityRight originalGroup block))

  originalFinePairNumerator :
    (weight : Link → Link → ℝ)
    (coarseObservable : Link → ℝ) → ℝ
  originalFinePairNumerator weight coarseObservable =
    Product.integrateOne source
      (λ first →
        Product.integrateOne source
          (λ second →
            weight first second
              *ℝ coarseObservable (multiply first second)))

  -- Explicit fibre integral along the ORIGINAL group multiplication
  -- map B(U,V)=U·V. This is a function of the true coarse link W.
  actualCoarsePairEffectiveDensity :
    (weight : Link → Link → ℝ) → Link → ℝ
  actualCoarsePairEffectiveDensity weight block =
    Product.integrateOne source
      (λ fibre → weight (multiply block (inverse fibre)) fibre)

  originalCoarsePairEffectiveNumerator :
    (weight : Link → Link → ℝ)
    (coarseObservable : Link → ℝ) → ℝ
  originalCoarsePairEffectiveNumerator weight coarseObservable =
    Product.integrateOne source
      (λ block →
        actualCoarsePairEffectiveDensity weight block
          *ℝ coarseObservable block)

  -- The selected original oneLink Haar RIGHT-translation changes
  -- integration coordinates W -> W·V⁻¹ for fixed V. Group cancellation
  -- proves that the coarse observable is exactly F(W).
  oneLinkRightTranslateWeighted :
    (weight : Link → Link → ℝ)
    (coarseObservable : Link → ℝ)
    (fibre : Link) →
    Product.integrateOne source
      (λ block →
        weight (multiply block (inverse fibre)) fibre
          *ℝ coarseObservable block)
    ≡
    Product.integrateOne source
      (λ first →
        weight first fibre
          *ℝ coarseObservable (multiply first fibre))
  oneLinkRightTranslateWeighted weight coarseObservable fibre =
    trans
      (sym (Product.integrateCongruent source
        (λ block →
          weight (multiply block (inverse fibre)) fibre
            *ℝ coarseObservable
              (multiply (multiply block (inverse fibre)) fibre))
        (λ block →
          weight (multiply block (inverse fibre)) fibre
            *ℝ coarseObservable block)
        (λ block →
          cong
            (λ result →
              weight (multiply block (inverse fibre)) fibre
                *ℝ coarseObservable result)
            (originalRightTranslationCancels block fibre))))
      (Bilateral.oneRightInvariant bilateral (inverse fibre)
        (λ first →
          weight first fibre
            *ℝ coarseObservable (multiply first fibre)))

  -- This is a source-level Fubini calculation. The scalar coefficient
  -- is the ACTUAL fibre integral and the algebraic equality follows
  -- from original oneScale/oneLink congruence plus real commutativity.
  densityTimesObservableIsFibreIntegral :
    (weight : Link → Link → ℝ)
    (coarseObservable : Link → ℝ)
    (block : Link) →
    actualCoarsePairEffectiveDensity weight block
      *ℝ coarseObservable block
    ≡
    Product.integrateOne source
      (λ fibre →
        weight (multiply block (inverse fibre)) fibre
          *ℝ coarseObservable block)
  densityTimesObservableIsFibreIntegral
      weight coarseObservable block =
    trans
      (*-comm
        (actualCoarsePairEffectiveDensity weight block)
        (coarseObservable block))
      (trans
        (sym (Ordered.oneScale linear
          (coarseObservable block)
          (λ fibre →
            weight (multiply block (inverse fibre)) fibre)))
        (Product.integrateCongruent source _ _
          (λ fibre →
            *-comm
              (coarseObservable block)
              (weight (multiply block (inverse fibre)) fibre))))

  -- R445.F17: genuinely WEIGHTED fine-to-coarse pushforward equality.
  -- Unlike the unweighted path result, the integral over fibre V is
  -- retained and cannot be discarded when Wilson action couples links.
  actualWeightedPairDisintegration :
    (weight : Link → Link → ℝ)
    (coarseObservable : Link → ℝ) →
    originalFinePairNumerator weight coarseObservable
    ≡ originalCoarsePairEffectiveNumerator weight coarseObservable
  actualWeightedPairDisintegration weight coarseObservable =
    sym
      (trans
        (Product.integrateCongruent source _ _
          (densityTimesObservableIsFibreIntegral
            weight coarseObservable))
        (trans
          (Product.integrateTwoSwap source
            (λ block fibre →
              weight (multiply block (inverse fibre)) fibre
                *ℝ coarseObservable block))
          (trans
            (Product.integrateCongruent source _ _
              (λ fibre →
                oneLinkRightTranslateWeighted
                  weight coarseObservable fibre))
            (sym (Product.integrateTwoSwap source
              (λ first second →
                weight first second
                  *ℝ coarseObservable (multiply first second))))))

  -- Strict positivity of the effective density follows from the
  -- ORIGINAL one-link strict-positive Haar input, if a chosen actual
  -- fine Gibbs density is pointwise strictly positive.
  -- This does not assert that the effective density is bare Wilson or
  -- furnish a logarithm/physical counterterm expansion.
  actualEffectiveDensityStrictlyPositive :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration source)
    (weight : Link → Link → ℝ) →
    (∀ first second → 0ℝ <ℝ weight first second) →
    ∀ block →
    0ℝ <ℝ actualCoarsePairEffectiveDensity weight block
  actualEffectiveDensityStrictlyPositive strict weight strong block =
    Ordered.oneStrictPositive strict _
      (λ fibre → strong (multiply block (inverse fibre)) fibre)

  -- An arbitrary external fine configuration (spectator links) may
  -- affect the FULL weight in any nonfactorizing way. The single-pair
  -- disintegration remains pointwise valid, with no independent
  -- spectator-law assumption.
  originalWeightedPairWithSpectators :
    ∀ {Rest : Set}
      (weight : Link → Link → Rest → ℝ)
      (rest : Rest)
      (coarseObservable : Link → ℝ) →
    originalFinePairNumerator
      (λ first second → weight first second rest)
      coarseObservable
    ≡
    originalCoarsePairEffectiveNumerator
      (λ first second → weight first second rest)
      coarseObservable
  originalWeightedPairWithSpectators weight rest observable =
    actualWeightedPairDisintegration
      (λ first second → weight first second rest) observable
