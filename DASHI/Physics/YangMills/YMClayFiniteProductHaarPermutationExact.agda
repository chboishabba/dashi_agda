{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact where

------------------------------------------------------------------------
-- R443-H: FINITE PRODUCT-HAAR PERMUTATION PROOF, WITHOUT GLOBAL SYMMETRY AXIOM.
--
-- Standard inputs: one-link integration, its extensionality/normalization,
-- and the Fubini interchange of TWO one-link integrations. The resulting
-- exact theorem proves invariance of arbitrary N-fold product integration
-- under ALL permutations constructed by composition, fixing one coordinate
-- and swapping the first two coordinates. No N-link integral symmetry is
-- postulated. The same proof applies to real SU(2) or SU(N) link values.
--
-- It does not construct one-link Haar on continuous SU(N), prove the
-- site-bond coordinate codec, or identify the source Gibbs cutoff family.
-- Fubini and single-link Haar are explicit mathematical prerequisites.
--
-- Classical compact Haar/Fubini; see B. C. Hall, "Lie Groups, Lie Algebras,
-- and Representations", 2nd ed., Springer 2015,
-- DOI 10.1007/978-3-319-13467-3.
-- DASHI owns this elementary finite-vector induction/commuting square.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 1ℝ)

record OneLinkProductHaar (Link : Set) : Set₁ where
  field
    integrateOne : (Link → ℝ) → ℝ

    integrateCongruent :
      (left right : Link → ℝ) →
      (∀ x → left x ≡ right x) →
      integrateOne left ≡ integrateOne right

    integrateUnit :
      integrateOne (λ _ → 1ℝ) ≡ 1ℝ

    -- This is the ordinary finite product Fubini theorem, not the
    -- very R443 full-lattice C3 symmetry we are trying to establish.
    integrateTwoSwap : (f : Link → Link → ℝ) →
      integrateOne (λ x → integrateOne (λ y → f x y))
      ≡ integrateOne (λ y → integrateOne (λ x → f x y))

open OneLinkProductHaar public

productIntegral :
  ∀ {Link : Set} {n : Nat} →
  OneLinkProductHaar Link → (Vec Link n → ℝ) → ℝ
productIntegral {n = zero} source term = term []
productIntegral {n = suc n} source term =
  integrateOne source
    (λ link → productIntegral source (λ tail → term (link ∷ tail)))

productIntegralUnit :
  ∀ {Link : Set} {n : Nat} →
  (source : OneLinkProductHaar Link) →
  productIntegral {n = n} source (λ _ → 1ℝ) ≡ 1ℝ
productIntegralUnit {n = zero} source = refl
productIntegralUnit {n = suc n} source =
  trans
    (integrateCongruent source _ _
      (λ link → productIntegralUnit {n = n} source))
    (integrateUnit source)

-- A concrete finite-permutation presentation, enough to represent all
-- finite adjacent transpositions by nested fixHead.
data LinkPermutation : Nat → Set where
  identity : ∀ {n} → LinkPermutation n
  compose : ∀ {n} → LinkPermutation n → LinkPermutation n → LinkPermutation n
  fixHead : ∀ {n} → LinkPermutation n → LinkPermutation (suc n)
  swapHead : ∀ {n} → LinkPermutation (suc (suc n))

permuteLinks :
  ∀ {Link : Set} {n : Nat} →
  LinkPermutation n → Vec Link n → Vec Link n
permuteLinks identity links = links
permuteLinks (compose first second) links =
  permuteLinks first (permuteLinks second links)
permuteLinks (fixHead p) (link ∷ links) =
  link ∷ permuteLinks p links
permuteLinks swapHead (first ∷ second ∷ rest) =
  second ∷ first ∷ rest

-- The theorem supplies the N-link invariance used by R443 after the
-- physical 4*256 positive-link coordinate order and its C3 reindexing are
-- identified with a concrete LinkPermutation witness.
productHaarPermutationInvariant :
  ∀ {Link : Set} {n : Nat}
    (source : OneLinkProductHaar Link)
    (p : LinkPermutation n)
    (observable : Vec Link n → ℝ) →
  productIntegral source
    (λ links → observable (permuteLinks p links))
  ≡ productIntegral source observable
productHaarPermutationInvariant source identity observable = refl
productHaarPermutationInvariant source (compose first second) observable =
  trans
    (productHaarPermutationInvariant source second
      (λ links → observable (permuteLinks first links)))
    (productHaarPermutationInvariant source first observable)
productHaarPermutationInvariant source (fixHead p) observable =
  integrateCongruent source _ _
    (λ link →
      productHaarPermutationInvariant source p
        (λ tail → observable (link ∷ tail)))
productHaarPermutationInvariant {n = suc (suc n)} source swapHead observable =
  integrateTwoSwap source
    (λ second first →
      productIntegral source
        (λ tail → observable (first ∷ second ∷ tail)))
