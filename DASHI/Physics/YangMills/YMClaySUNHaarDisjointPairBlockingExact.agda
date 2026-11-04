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
import DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarC3Exact as IntegralCongruence
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

  -- Any finite number of genuinely independent unobserved original
  -- Haar links integrates out to one, without a conditional Gibbs
  -- factorization. Product normalization is derived from oneLink.
  productIntegralConstant :
    ∀ {spectators : Nat} (value : ℝ) →
    Product.productIntegral {n = spectators} source (λ _ → value)
    ≡ value
  productIntegralConstant {spectators = zero} value = refl
  productIntegralConstant {spectators = suc n} value =
    trans
      (Product.integrateCongruent source _ _
        (λ link → productIntegralConstant {spectators = n} value))
      (integrateConstant value)

  -- The spectators are still genuine independent original Haar link
  -- coordinates; integrating them out is legal only for the UNWEIGHTED
  -- pullback observable, which is independent of those links.
  originalUnweightedSpectatorsDisappear :
    ∀ {n spectators : Nat} (observable : Vec Link n → ℝ) →
    Product.productIntegral source
      (λ blocks →
        Product.productIntegral {n = spectators} source
          (λ _ → observable blocks))
    ≡ Product.productIntegral source observable
  originalUnweightedSpectatorsDisappear
      {spectators = spectators} observable =
    IntegralCongruence.productIntegralCongruent source _ _
      (λ blocks →
        productIntegralConstant {spectators = spectators}
          (observable blocks))

  -- Combined exact kinematic statement:
  -- 2*n independent links, grouped into disjoint ordered pairs, plus
  -- any number of independent spectators -> n original Haar links.
  -- The all-64 native block-pairs + 896 spectators coordinate PERMUTATION
  -- and equality with selected SUNBlock are separate original geometry.
  originalDisjointPairSpectatorPushforward :
    ∀ {n spectators : Nat}
      (observable : Vec Link n → ℝ) →
    disjointPairIntegral
      (λ blocks →
        Product.productIntegral {n = spectators} source
          (λ _ → observable blocks))
    ≡ Product.productIntegral source observable
  originalDisjointPairSpectatorPushforward observable =
    trans
      (disjointPairHaarPushforward _)
      (originalUnweightedSpectatorsDisappear observable)

  ----------------------------------------------------------------------
  -- ALL POSITIVE PATH LENGTHS: right-associated selected Wilson
  -- holonomy order, zero commutativity assumptions. This specializes
  -- to the existing exact two-link law and generalizes R445.F13 to L.
  ----------------------------------------------------------------------

  orderedPositivePath :
    ∀ {l : Nat} →
    Vec Link (suc l) → Link
  orderedPositivePath {zero} (head ∷ []) = head
  orderedPositivePath {suc l} (head ∷ tail) =
    SUN.sunMultiply theory head (orderedPositivePath tail)

  -- For EVERY L>=1, an ordered product of L independent original
  -- one-link Haar variables is itself exactly one-link Haar. No group
  -- commutativity, no density or new measure. This is stronger than
  -- a two-link numerical fixture because the induction is symbolic.
  originalPositivePathHaarPushforward :
    ∀ {l : Nat} (observable : Link → ℝ) →
    Product.productIntegral {n = suc l} source
      (λ path → observable (orderedPositivePath path))
    ≡ Product.integrateOne source observable
  originalPositivePathHaarPushforward {zero} observable = refl
  originalPositivePathHaarPushforward {suc l} observable =
    trans
      (Product.integrateCongruent source _ _
        (λ head →
          originalPositivePathHaarPushforward {l = l}
            (λ tail →
              observable (SUN.sunMultiply theory head tail))))
      (oneNoncommutativePairPushforward observable)

  -- A finite family of disjoint ordered L-link positive holonomies
  -- integrates as independent coarse one-link Haar variables.
  -- The original torus block-path source uses this right-associated
  -- product order; literal coordinate/index identification still open.
  disjointPositivePathIntegral :
    ∀ {paths : Nat} (l : Nat) →
    (Vec Link paths → ℝ) → ℝ
  disjointPositivePathIntegral {paths = zero} l observable =
    observable []
  disjointPositivePathIntegral {paths = suc n} l observable =
    Product.productIntegral {n = suc l} source
      (λ finePath →
        disjointPositivePathIntegral {paths = n} l
          (λ coarseTail →
            observable
              (orderedPositivePath finePath ∷ coarseTail)))

  disjointPositivePathHaarPushforward :
    ∀ {paths : Nat} (l : Nat)
      (observable : Vec Link paths → ℝ) →
    disjointPositivePathIntegral l observable
    ≡ Product.productIntegral source observable
  disjointPositivePathHaarPushforward {paths = zero} l observable =
    refl
  disjointPositivePathHaarPushforward {paths = suc n}
      l observable =
    trans
      (IntegralCongruence.productIntegralCongruent source _ _
        (λ finePath →
          disjointPositivePathHaarPushforward {paths = n} l
            (λ coarseTail →
              observable (orderedPositivePath finePath ∷ coarseTail))))
      (originalPositivePathHaarPushforward {l = l}
        (λ coarseLink →
          Product.productIntegral source
            (λ coarseTail → observable (coarseLink ∷ coarseTail))))

  originalAllLengthDisjointPathSpectatorPushforward :
    ∀ {paths spectators : Nat} (l : Nat)
      (observable : Vec Link paths → ℝ) →
    disjointPositivePathIntegral l
      (λ coarse →
        Product.productIntegral {n = spectators} source
          (λ _ → observable coarse))
    ≡ Product.productIntegral source observable
  originalAllLengthDisjointPathSpectatorPushforward l observable =
    trans
      (disjointPositivePathHaarPushforward l _)
      (originalUnweightedSpectatorsDisappear observable)

  -- A chosen concrete sequence of non-Abelian blocked link values is
  -- not supplied here by a guessed Gamma/RG coarse configuration.
  -- Identifying this integration order with the original 1024-bond
  -- side-four decoder and selected 2-link SUNBlock remains R445.P04.
