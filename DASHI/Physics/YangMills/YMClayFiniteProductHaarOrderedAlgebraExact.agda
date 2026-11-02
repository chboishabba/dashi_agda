{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact where

------------------------------------------------------------------------
-- R443: FINITE PRODUCT INTEGRATION ALGEBRA FROM ONE-LINK LAWS.
--
-- The existing product-Haar permutation induction uses two-link Fubini.
-- R445's physical cylinder integration additionally needs linearity,
-- positivity and zero. Prove their N-link forms by induction, rather than
-- request an independently postulated physical N-link law package.
--
-- OneLinkProductHaar is a TOTAL functional on all functions Link -> Real.
-- Ordinary continuous compact Haar integration is defined on a suitable
-- integrable/measurable class, NOT automatically on arbitrary functions.
-- A physical instantiation must justify its selected test algebra; this
-- conditional interface is not itself a construction of Borel Haar.
--
-- Classical normalized Haar/Fubini; existing DASHI R443/finite integration
-- owners; this finite-vector induction is an original DASHI bridge.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _*ℝ_; _≤ℝ_)

import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product

record OneLinkOrderedHaarAlgebra {Link : Set}
    (source : Product.OneLinkProductHaar Link) : Set₁ where
  field
    oneZero :
      Product.integrateOne source (λ _ → 0ℝ) ≡ 0ℝ

    oneAdd : ∀ left right →
      Product.integrateOne source (λ link → left link +ℝ right link)
      ≡ Product.integrateOne source left
        +ℝ Product.integrateOne source right

    oneScale : ∀ scalar observable →
      Product.integrateOne source (λ link → scalar *ℝ observable link)
      ≡ scalar *ℝ Product.integrateOne source observable

    onePositive : ∀ observable →
      (∀ link → 0ℝ ≤ℝ observable link) →
      0ℝ ≤ℝ Product.integrateOne source observable

open OneLinkOrderedHaarAlgebra public

productIntegralZero :
  ∀ {Link : Set} {n : Nat}
    (source : Product.OneLinkProductHaar Link)
    (laws : OneLinkOrderedHaarAlgebra source) →
  Product.productIntegral {n = n} source (λ _ → 0ℝ) ≡ 0ℝ
productIntegralZero {n = zero} source laws = refl
productIntegralZero {n = suc n} source laws =
  trans
    (Product.integrateCongruent source _ _
      (λ link → productIntegralZero {n = n} source laws))
    (oneZero laws)

productIntegralAdd :
  ∀ {Link : Set} {n : Nat}
    (source : Product.OneLinkProductHaar Link)
    (laws : OneLinkOrderedHaarAlgebra source)
    (left right : Vec Link n → ℝ) →
  Product.productIntegral source
    (λ links → left links +ℝ right links)
  ≡ Product.productIntegral source left
    +ℝ Product.productIntegral source right
productIntegralAdd {n = zero} source laws left right = refl
productIntegralAdd {n = suc n} source laws left right =
  trans
    (Product.integrateCongruent source _ _
      (λ link →
        productIntegralAdd {n = n} source laws
          (λ tail → left (link ∷ tail))
          (λ tail → right (link ∷ tail))))
    (oneAdd laws _ _)

productIntegralScale :
  ∀ {Link : Set} {n : Nat}
    (source : Product.OneLinkProductHaar Link)
    (laws : OneLinkOrderedHaarAlgebra source)
    (scalar : ℝ) (observable : Vec Link n → ℝ) →
  Product.productIntegral source
    (λ links → scalar *ℝ observable links)
  ≡ scalar *ℝ Product.productIntegral source observable
productIntegralScale {n = zero} source laws scalar observable = refl
productIntegralScale {n = suc n} source laws scalar observable =
  trans
    (Product.integrateCongruent source _ _
      (λ link →
        productIntegralScale {n = n} source laws scalar
          (λ tail → observable (link ∷ tail))))
    (oneScale laws scalar _)

productIntegralPositive :
  ∀ {Link : Set} {n : Nat}
    (source : Product.OneLinkProductHaar Link)
    (laws : OneLinkOrderedHaarAlgebra source)
    (observable : Vec Link n → ℝ) →
  (∀ links → 0ℝ ≤ℝ observable links) →
  0ℝ ≤ℝ Product.productIntegral source observable
productIntegralPositive {n = zero} source laws observable positive =
  positive []
productIntegralPositive {n = suc n} source laws observable positive =
  onePositive laws _
    (λ link →
      productIntegralPositive {n = n} source laws
        (λ tail → observable (link ∷ tail))
        (λ tail → positive (link ∷ tail)))
