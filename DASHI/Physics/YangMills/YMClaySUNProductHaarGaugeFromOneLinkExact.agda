{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact where

------------------------------------------------------------------------
-- PHYSICAL FINITE GAUGE INVARIANCE OF N-LINK PRODUCT HAAR.
--
-- Existing WilsonAction/SixPlaneGaugeInvariant already prove gauge action
-- invariance on the original SU(N) periodic links. That does not imply
-- invariance of the *Haar* integration independently.
--
-- Reuse existing OneLinkProductHaar and its integrateCongruent. Prove
-- n-link coordinatewise left/right translation invariance by induction.
-- This is NOT permutation invariance: every original bond experiences
-- gamma(source) * U * gamma(target)^(-1), with different site factors.
-- One-link invariance is the only analytic input. No n-link gauge Haar
-- invariance is postulated.
--
-- Physical source: Wilson (1974), compact-group Haar bi-invariance,
-- Balaban periodic oriented-link geometry. DASHI finite induction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN

record OneLinkSUNBilateralHaar
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (source : Product.OneLinkProductHaar
      (SUN.SUNMatrixElement theory)) : Set₁ where
  field
    oneLeftInvariant : ∀ left observable →
      Product.integrateOne source
        (λ U → observable (SUN.sunMultiply theory left U))
      ≡ Product.integrateOne source observable

    oneRightInvariant : ∀ right observable →
      Product.integrateOne source
        (λ U → observable (SUN.sunMultiply theory U right))
      ≡ Product.integrateOne source observable

open OneLinkSUNBilateralHaar public

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (source : Product.OneLinkProductHaar
      (SUN.SUNMatrixElement theory))
    (laws : OneLinkSUNBilateralHaar theory source)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  -- rightFactor is the native gamma(target)^(-1) parameter. We preserve
  -- the exact orientation as in the original Wilson gauge transformation.
  gaugeOneLink :
    Link → Link → Link → Link
  gaugeOneLink left right U =
    SUN.sunMultiply theory left (SUN.sunMultiply theory U right)

  gaugeOneLinkHaarInvariant :
    ∀ left right observable →
    Product.integrateOne source
      (λ U → observable (gaugeOneLink left right U))
    ≡ Product.integrateOne source observable
  gaugeOneLinkHaarInvariant left right observable =
    trans
      (oneRightInvariant laws right
        (λ U → observable (SUN.sunMultiply theory left U)))
      (oneLeftInvariant laws left observable)

  gaugeBondVector :
    ∀ {n} → Vec Link n → Vec Link n →
    Vec Link n → Vec Link n
  gaugeBondVector [] [] [] = []
  gaugeBondVector (left ∷ lefts) (right ∷ rights) (U ∷ links) =
    gaugeOneLink left right U
      ∷ gaugeBondVector lefts rights links

  productHaarNativeGaugeInvariant :
    ∀ {n} (left right : Vec Link n)
      (observable : Vec Link n → ℝ) →
    Product.productIntegral source
      (λ links → observable (gaugeBondVector left right links))
    ≡ Product.productIntegral source observable
  productHaarNativeGaugeInvariant {n = zero} [] [] observable = refl
  productHaarNativeGaugeInvariant {n = suc n}
      (left ∷ lefts) (right ∷ rights) observable =
    trans
      (Product.integrateCongruent source _ _
        (λ U →
          productHaarNativeGaugeInvariant lefts rights
            (λ tail → observable (gaugeOneLink left right U ∷ tail))))
      (gaugeOneLinkHaarInvariant left right
        (λ U →
          Product.productIntegral source
            (λ tail → observable (U ∷ tail))))
