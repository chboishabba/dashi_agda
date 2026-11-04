module DASHI.Physics.YangMills.YMClaySUNWeightedDisjointPairFibreReparamExact where

------------------------------------------------------------------------
-- R445.F18: ALL FINITE DISJOINT NONCOMMUTATIVE PAIRS, ARBITRARY WEIGHT.
--
-- The prior single-pair fibre theorem F17 has now been generalized to
-- any finite number of independent pairs U_j,V_j and any arbitrary
-- spectator configuration, WITHOUT factoring the selected fine weight.
--
-- Source integration variables are the ORIGINAL oneLink SU(N) matrix
-- Haar variables. A single Fubini + RIGHT Haar translation proves
--
--  int_U int_V f(U,V)
--    = int_W int_V f(W V^-1, V).
--
-- Repeating this finite exact identity under the existing product Haar
-- gives one original reparametrized fibre integration per native link
-- pair, in the SAME order as the selected original native path product.
-- The weight may couple ALL pairs and ALL original spectator links.
--
-- The original side4 -> side2 lattice has 64 coarse bonds (128 pair
-- links) + 896 spectator links. The final specialization instantiates
-- EXACTLY these arities with no additional abstract probability law.
-- The original *1024-link codec reordering* is still a separate open
-- kernel obligation, so this does not silently declare the selected
-- original Wilson-Gibbs measure to be this nested integral.
--
-- No physical measurable Haar construction, continuous density, bare
-- Wilson closure, volume/cutoff estimates, OS spectral gap or Clay claim.
-- Original attribution: Haar, Wilson, Balaban, original DASHI owners.
-- SOURCE WRITTEN; Agda typechecking and transitive trust PENDING.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (source : Product.OneLinkProductHaar
      (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory source)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  Pair : Set
  Pair = Torus.Product Link Link

  originalGroup : Bond.ExactLinkGroup Link
  originalGroup = Native.sunExactSignedLinkGroup theory

  multiply : Link → Link → Link
  multiply = SUN.sunMultiply theory

  inverse : Link → Link
  inverse = SUN.sunInverse theory

  actualPairBlock : Pair → Link
  actualPairBlock pair =
    multiply (Torus.first pair) (Torus.second pair)

  actualPairBlockVector :
    ∀ {n} → Vec Pair n → Vec Link n
  actualPairBlockVector [] = []
  actualPairBlockVector (pair ∷ pairs) =
    actualPairBlock pair ∷ actualPairBlockVector pairs

  -- Inverse of the original U,V -> W=U·V block, with fibre V held
  -- fixed. Both multiplication and inverse are the selected SUN group.
  pairFromCoarseAndFibre : Link → Link → Pair
  pairFromCoarseAndFibre block fibre =
    Torus.pair (multiply block (inverse fibre)) fibre

  selectedBlockAfterPairReparam :
    ∀ block fibre →
    actualPairBlock (pairFromCoarseAndFibre block fibre) ≡ block
  selectedBlockAfterPairReparam block fibre =
    trans
      (Bond.multiplyAssociative originalGroup
        block (inverse fibre) fibre)
      (trans
        (cong (multiply block)
          (Bond.inverseLeft originalGroup fibre))
        (Bond.identityRight originalGroup block))

  pairVectorFromCoarseAndFibre :
    ∀ {n} → Vec Link n → Vec Link n → Vec Pair n
  pairVectorFromCoarseAndFibre [] [] = []
  pairVectorFromCoarseAndFibre (block ∷ blocks) (fibre ∷ fibres) =
    pairFromCoarseAndFibre block fibre
      ∷ pairVectorFromCoarseAndFibre blocks fibres

  -- No function extensionality: this is a proof on arbitrary Vec values.
  pairVectorReparamHasOriginalCoarseHolonomy :
    ∀ {n} (blocks fibres : Vec Link n) →
    actualPairBlockVector (pairVectorFromCoarseAndFibre blocks fibres)
    ≡ blocks
  pairVectorReparamHasOriginalCoarseHolonomy [] [] = refl
  pairVectorReparamHasOriginalCoarseHolonomy
      (block ∷ blocks) (fibre ∷ fibres) =
    cong₂ _∷_
      (selectedBlockAfterPairReparam block fibre)
      (pairVectorReparamHasOriginalCoarseHolonomy blocks fibres)

  -- This uses the ORIGINAL product-Haar order, U outer and V inner.
  finePairsIntegral :
    ∀ {n} → (Vec Pair n → ℝ) → ℝ
  finePairsIntegral {n = zero} integrand = integrand []
  finePairsIntegral {n = suc n} integrand =
    Product.integrateOne source
      (λ first →
        Product.integrateOne source
          (λ second →
            finePairsIntegral {n = n}
              (λ remainder →
                integrand (Torus.pair first second ∷ remainder))))

  -- Exact per-pair reparametrization: W outer, V inner, preserving
  -- all subsequent independent link coordinates under the original
  -- recursively defined integral. No factorization of integrand.
  reparametrizedPairsIntegral :
    ∀ {n} → (Vec Pair n → ℝ) → ℝ
  reparametrizedPairsIntegral {n = zero} integrand = integrand []
  reparametrizedPairsIntegral {n = suc n} integrand =
    Product.integrateOne source
      (λ block →
        Product.integrateOne source
          (λ fibre →
            reparametrizedPairsIntegral {n = n}
              (λ remainder →
                integrand
                  (pairFromCoarseAndFibre block fibre ∷ remainder))))

  -- Core exact one-pair, ANY possibly nonfactorizing fine integrand.
  -- Original Fubini exchanges U,V, original right-invariance changes
  -- U to W·V^-1 at fixed V, then Fubini exchanges W,V back.
  originalOnePairGeneralWeightedChange :
    (integrand : Link → Link → ℝ) →
    Product.integrateOne source
      (λ first →
        Product.integrateOne source (λ second → integrand first second))
    ≡
    Product.integrateOne source
      (λ block →
        Product.integrateOne source
          (λ fibre →
            integrand (multiply block (inverse fibre)) fibre))
  originalOnePairGeneralWeightedChange integrand =
    trans
      (Product.integrateTwoSwap source integrand)
      (trans
        (Product.integrateCongruent source _ _
          (λ fibre →
            sym (Bilateral.oneRightInvariant
              bilateral (inverse fibre)
              (λ first → integrand first fibre))))
        (sym (Product.integrateTwoSwap source
          (λ block fibre →
            integrand (multiply block (inverse fibre)) fibre))))

  -- Induction on the selected number of independent link pairs.
  -- Arbitrary coupling across all original pairs is allowed because
  -- the induction hypothesis is quantified over EVERY integrand.
  originalAllPairsGeneralWeightedChange :
    ∀ {n} (integrand : Vec Pair n → ℝ) →
    finePairsIntegral integrand
    ≡ reparametrizedPairsIntegral integrand
  originalAllPairsGeneralWeightedChange {n = zero} integrand = refl
  originalAllPairsGeneralWeightedChange {n = suc n} integrand =
    trans
      (Product.integrateCongruent source _ _
        (λ first →
          Product.integrateCongruent source _ _
            (λ second →
              originalAllPairsGeneralWeightedChange {n = n}
                (λ tail →
                  integrand (Torus.pair first second ∷ tail)))))
      (originalOnePairGeneralWeightedChange
        (λ first second →
          reparametrizedPairsIntegral {n = n}
            (λ tail →
              integrand (Torus.pair first second ∷ tail))))

  -- A selected original spectator vector may enter the arbitrary
  -- fine weight and the arbitrary cylinder observable. Its entire
  -- Haar integration is left WITHIN the integrand; no independence
  -- or spectator decoupling is asserted for the fine Wilson density.
  originalAllPairsWithArbitrarySpectatorWeight :
    ∀ {n spectators}
      (integrand : Vec Pair n → Vec Link spectators → ℝ) →
    finePairsIntegral
      (λ pairs →
        Product.productIntegral source
          (λ spectator → integrand pairs spectator))
    ≡
    reparametrizedPairsIntegral
      (λ pairs →
        Product.productIntegral source
          (λ spectator → integrand pairs spectator))
  originalAllPairsWithArbitrarySpectatorWeight integrand =
    originalAllPairsGeneralWeightedChange _

  -- Specific arities of the native periodic side-four -> side-two
  -- fine-bond partition from F15/F16; linking THIS vector integral
  -- to the selected original Codec.decodeOriginalBonds 4 is still
  -- unpaid R445 coordinate reindex/theory construction.
  selectedSideFour64Pair896SpectatorChange :
    (integrand : Vec Pair 64 → Vec Link 896 → ℝ) →
    finePairsIntegral
      (λ pairs →
        Product.productIntegral source
          (λ spectator → integrand pairs spectator))
    ≡
    reparametrizedPairsIntegral
      (λ pairs →
        Product.productIntegral source
          (λ spectator → integrand pairs spectator))
  selectedSideFour64Pair896SpectatorChange integrand =
    originalAllPairsWithArbitrarySpectatorWeight integrand
