module DASHI.Physics.YangMills.YMClaySUNHaarDisjointPairBlockingExact where

------------------------------------------------------------------------
-- R445: non-Abelian DISJOINT-PAIR Haar blocking, not a new Haar axiom.
--
-- The ORIGINAL matrix SUN group and ORIGINAL one-link Haar are used.
-- For *independent* link coordinates U,V, the block U·V has the
-- original one-link law: integral(dU dV) F(U·V) = integral(dW) F(W).
-- The proof consumes ONLY original oneLeftInvariant, integrateCongruent,
-- integrateUnit and oneScale. No one-link multiplication/disintegration
-- compatibility is inserted as an extra assumption.
--
-- The result is then iterated for all finite vectors of DISJOINT
-- two-link blocks, preserving the order of noncommutative products.
-- This is an exact kinematic Haar pushforward, without a new finite
-- probability space. It can be applied to the native side-four ->
-- side-two map only AFTER producing an exact link-coordinate partition:
-- 128 selected fine links into 64 disjoint ordered pairs, with the
-- remaining 896 spectators, and proving correspondence with original
-- Codec/SUNBlock. That actual geometric permutation/reindexing is OPEN.
--
-- The weighted original Wilson Gibbs pushforward generally has a
-- NONBARE effective action. No positive coarse density, conditional
-- distribution of fine links, arbitrary-scale blocking, reflection
-- compatibility, continuum estimates, or OS gap follows here.
--
-- Compact Haar classic mathematics; source owners Wilson/Balaban and
-- DASHI SUNMatrixCarrier, YMClayFiniteProductHaarPermutationExact,
-- YMClayFiniteProductHaarOrderedAlgebraExact,
-- YMClaySUNProductHaarGaugeFromOneLinkExact.
-- SOURCE WRITTEN; kernel not run; source imports legacy real axioms.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 1ℝ; _*ℝ_; mulOneʳ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (source : Product.OneLinkProductHaar
      (SUN.SUNMatrixElement theory))
    (ordered : Ordered.OneLinkOrderedHaarAlgebra source)
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory source)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  -- One-link normalization + scaling already imply integration of
  -- constants. This is not an independent extra Haar assumption.
  integrateConstant :
    (value : ℝ) →
    Product.integrateOne source (λ _ → value) ≡ value
  integrateConstant value =
    trans
      (Product.integrateCongruent source
        (λ _ → value)
        (λ _ → value *ℝ 1ℝ)
        (λ _ → sym (mulOneʳ value)))
      (trans
        (Ordered.oneScale ordered value (λ _ → 1ℝ))
        (trans
          (cong (value *ℝ_) (Product.integrateUnit source))
          (mulOneʳ value)))

  -- The two-link ordered holonomy is EXACTLY the existing SUN product.
  -- Since V is independent Haar, for any fixed U, U·V is Haar by
  -- oneLeftInvariant. Integrating the remaining U then preserves the
  -- same normalized one-link integral.
  oneNoncommutativePairPushforward :
    (observable : Link → ℝ) →
    Product.integrateOne source
      (λ first →
        Product.integrateOne source
          (λ second →
            observable (SUN.sunMultiply theory first second)))
    ≡ Product.integrateOne source observable
  oneNoncommutativePairPushforward observable =
    trans
      (Product.integrateCongruent source
        (λ first →
          Product.integrateOne source
            (λ second →
              observable (SUN.sunMultiply theory first second)))
        (λ _ → Product.integrateOne source observable)
        (λ first →
          Bilateral.oneLeftInvariant bilateral first observable))
      (integrateConstant (Product.integrateOne source observable))

  -- Exactly n distinct ordered link pairs: each pair uses two fresh
  -- independent original one-link Haar coordinates. There are no
  -- unproved function extensionality or generic measurable-transport
  -- axioms in this finite induction.
  disjointPairIntegral :
    ∀ {n} →
    (Vec Link n → ℝ) → ℝ
  disjointPairIntegral {zero} observable = observable []
  disjointPairIntegral {suc n} observable =
    Product.integrateOne source
      (λ first →
        Product.integrateOne source
          (λ second →
            disjointPairIntegral
              {n = n}
              (λ tail →
                observable
                  (SUN.sunMultiply theory first second ∷ tail))))

  disjointPairHaarPushforward :
    ∀ {n}
      (observable : Vec Link n → ℝ) →
    disjointPairIntegral observable
    ≡ Product.productIntegral source observable
  disjointPairHaarPushforward {zero} observable = refl
  disjointPairHaarPushforward {suc n} observable =
    trans
      (Product.integrateCongruent source _ _
        (λ first →
          Product.integrateCongruent source _ _
            (λ second →
              disjointPairHaarPushforward {n = n}
                (λ tail →
                  observable
                    (SUN.sunMultiply theory first second ∷ tail)))))
      (oneNoncommutativePairPushforward
        (λ block →
          Product.productIntegral source
            (λ tail → observable (block ∷ tail))))

  -- A chosen concrete sequence of non-Abelian blocked link values is
  -- not supplied here by a guessed Gamma/RG coarse configuration.
  -- Identifying this integration order with the original 1024-bond
  -- side-four decoder and selected 2-link SUNBlock remains R445.P04.
