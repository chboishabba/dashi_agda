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
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_; *-comm)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarC3Exact as IntegralCongruence

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


  ----------------------------------------------------------------------
  -- R445.F19: explicit ALL-PAIR COARSE EFFECTIVE DENSITY from the
  -- ORIGINAL one-link Haar and selected noncommutative link product.
  -- Retain the FULL arbitrary fine weight; no bare-Wilson promotion.
  ----------------------------------------------------------------------

  -- Exact Fubini: commute one original one-link Haar integral across
  -- any existing finite ordered product Haar vector of link variables.
  -- This is DERIVED from integrateTwoSwap, not a new n-link theorem.
  oneLinkAcrossProductFubini :
    ∀ {n} (integrand : Link → Vec Link n → ℝ) →
    Product.integrateOne source
      (λ first →
        Product.productIntegral source
          (λ rest → integrand first rest))
    ≡
    Product.productIntegral source
      (λ rest →
        Product.integrateOne source
          (λ first → integrand first rest))
  oneLinkAcrossProductFubini {n = zero} integrand = refl
  oneLinkAcrossProductFubini {n = suc n} integrand =
    trans
      (Product.integrateTwoSwap source
        (λ first head →
          Product.productIntegral source
            (λ tail → integrand first (head ∷ tail))))
      (Product.integrateCongruent source _ _
        (λ head →
          oneLinkAcrossProductFubini {n = n}
            (λ first tail → integrand first (head ∷ tail))))

  -- The true fibre V_j at each coarse group value W_j is integrated
  -- conditionally at fixed W_j; ALL other fibre variables are retained.
  -- It is the explicit finite Haar Radon--Nikodym candidate density.
  actualAllPairsFibreIntegral :
    ∀ {n} (integrand : Vec Pair n → ℝ) →
    Vec Link n → ℝ
  actualAllPairsFibreIntegral {n = zero} integrand [] =
    integrand []
  actualAllPairsFibreIntegral {n = suc n}
      integrand (block ∷ blocks) =
    Product.integrateOne source
      (λ fibre →
        actualAllPairsFibreIntegral {n = n}
          (λ tail →
            integrand
              (pairFromCoarseAndFibre block fibre ∷ tail))
          blocks)

  -- Convert the interleaved Haar integral
  --   int dW1 dV1 ... dWn dVn f
  -- to the exact coarse-then-fibre order
  --   int dW1 ... dWn [int dV1 ... dVn f].
  -- Does not require any integrand factorization or positivity.
  originalInterleavedIntegralIsCoarseFibre :
    ∀ {n} (integrand : Vec Pair n → ℝ) →
    reparametrizedPairsIntegral integrand
    ≡
    Product.productIntegral source
      (actualAllPairsFibreIntegral integrand)
  originalInterleavedIntegralIsCoarseFibre
      {n = zero} integrand = refl
  originalInterleavedIntegralIsCoarseFibre
      {n = suc n} integrand =
    trans
      (Product.integrateCongruent source _ _
        (λ block →
          Product.integrateCongruent source _ _
            (λ fibre →
              originalInterleavedIntegralIsCoarseFibre
                {n = n}
                (λ tail →
                  integrand
                    (pairFromCoarseAndFibre block fibre ∷ tail)))))
      (Product.integrateCongruent source _ _
        (λ block →
          oneLinkAcrossProductFubini {n = n}
            (λ fibre blocks →
              actualAllPairsFibreIntegral
                (λ tail →
                  integrand
                    (pairFromCoarseAndFibre block fibre ∷ tail))
                blocks)))

  -- Actual arbitrary-weight SOURCE-WIDE coarse density, not an
  -- independently chosen coarse Wilson action or second Haar measure.
  originalAllPairsEffectiveDensity :
    ∀ {n} → (Vec Pair n → ℝ) → Vec Link n → ℝ
  originalAllPairsEffectiveDensity = actualAllPairsFibreIntegral

  actualAllPairsWeightedCoarseNumerator :
    ∀ {n}
      (weight : Vec Pair n → ℝ)
      (observable : Vec Link n → ℝ) → ℝ
  actualAllPairsWeightedCoarseNumerator weight observable =
    Product.productIntegral source
      (λ blocks →
        originalAllPairsEffectiveDensity weight blocks
          *ℝ observable blocks)

  -- The actual coarse effective density must remain INSIDE the
  -- original coarse Haar. Pulling an arbitrary observable through
  -- fibre integration requires the ORIGINAL oneScale and real
  -- multiplication commutativity, not a new action density axiom.
  module _ (linear : Ordered.OneLinkOrderedHaarAlgebra source) where

    oneLinkScaleOnRight :
      (observable : Link → ℝ) (scalar : ℝ) →
      Product.integrateOne source
        (λ fibre → observable fibre *ℝ scalar)
      ≡ Product.integrateOne source observable *ℝ scalar
    oneLinkScaleOnRight observable scalar =
      trans
        (Product.integrateCongruent source _ _
          (λ fibre → *-comm (observable fibre) scalar))
        (trans
          (Ordered.oneScale linear scalar observable)
          (*-comm scalar (Product.integrateOne source observable)))

    originalFibreIntegralCongruent :
      ∀ {n}
        (left right : Vec Pair n → ℝ) →
        (∀ pairs → left pairs ≡ right pairs) →
        ∀ blocks →
        actualAllPairsFibreIntegral left blocks
        ≡ actualAllPairsFibreIntegral right blocks
    originalFibreIntegralCongruent {n = zero}
        left right pointwise [] = pointwise []
    originalFibreIntegralCongruent {n = suc n}
        left right pointwise (block ∷ blocks) =
      Product.integrateCongruent source _ _
        (λ fibre →
          originalFibreIntegralCongruent
            (λ tail →
              left (pairFromCoarseAndFibre block fibre ∷ tail))
            (λ tail →
              right (pairFromCoarseAndFibre block fibre ∷ tail))
            (λ tail →
              pointwise
                (pairFromCoarseAndFibre block fibre ∷ tail))
            blocks)

    originalFibreIntegralPullsCoarseObservable :
      ∀ {n}
        (weight : Vec Pair n → ℝ)
        (observable : Vec Link n → ℝ)
        (blocks : Vec Link n) →
      actualAllPairsFibreIntegral
        (λ pairs →
          weight pairs
            *ℝ observable (actualPairBlockVector pairs))
        blocks
      ≡
      actualAllPairsFibreIntegral weight blocks
        *ℝ observable blocks
    originalFibreIntegralPullsCoarseObservable
        {n = zero} weight observable [] = refl
    originalFibreIntegralPullsCoarseObservable
        {n = suc n} weight observable (block ∷ blocks) =
      let
        originalHeadWeight :
          Link → Vec Pair n → ℝ
        originalHeadWeight fibre tail =
          weight (pairFromCoarseAndFibre block fibre ∷ tail)

        -- The original group cancellation is EXACT, not a heuristic
        -- replacement of the noncommutative link product.
        originalHeadObservable :
          Link → Vec Pair n → ℝ
        originalHeadObservable fibre tail =
          observable
            (actualPairBlock
              (pairFromCoarseAndFibre block fibre)
              ∷ actualPairBlockVector tail)

        selectedHeadObservable :
          Vec Pair n → ℝ
        selectedHeadObservable tail =
          observable (block ∷ actualPairBlockVector tail)

        integratedPointwise :
          ∀ fibre →
          actualAllPairsFibreIntegral
            (λ tail →
              originalHeadWeight fibre tail
                *ℝ originalHeadObservable fibre tail)
            blocks
          ≡
          actualAllPairsFibreIntegral
            (originalHeadWeight fibre)
            blocks *ℝ observable (block ∷ blocks)
        integratedPointwise fibre =
          trans
            (originalFibreIntegralCongruent
              (λ tail →
                originalHeadWeight fibre tail
                  *ℝ originalHeadObservable fibre tail)
              (λ tail →
                originalHeadWeight fibre tail
                  *ℝ selectedHeadObservable tail)
              (λ tail →
                cong
                  (λ value →
                    originalHeadWeight fibre tail
                      *ℝ observable (value ∷ actualPairBlockVector tail))
                  (selectedBlockAfterPairReparam block fibre))
              blocks)
            (originalFibreIntegralPullsCoarseObservable
              (originalHeadWeight fibre)
              (λ rest → observable (block ∷ rest))
              blocks)
      in
      trans
        (Product.integrateCongruent source _ _
          integratedPointwise)
        (oneLinkScaleOnRight
          (λ fibre →
            actualAllPairsFibreIntegral
              (originalHeadWeight fibre) blocks)
          (observable (block ∷ blocks)))

    -- The ALL-pair WEIGHTED effective density theorem. Unweighted
    -- path Haar is a corollary, but the actual Wilson Gibbs density
    -- is NOT assumed to be constant or independent of spectators.
    originalAllPairsWeightedHaarDisintegration :
      ∀ {n}
        (weight : Vec Pair n → ℝ)
        (observable : Vec Link n → ℝ) →
      finePairsIntegral
        (λ pairs →
          weight pairs *ℝ observable (actualPairBlockVector pairs))
      ≡ actualAllPairsWeightedCoarseNumerator weight observable
    originalAllPairsWeightedHaarDisintegration
        weight observable =
      trans
        (originalAllPairsGeneralWeightedChange _)
        (trans
          (originalInterleavedIntegralIsCoarseFibre _)
          (IntegralCongruence.productIntegralCongruent source _ _
            (originalFibreIntegralPullsCoarseObservable
              weight observable)))

    -- The selected original 64 coarse-link/896 spectator arities:
    -- arbitrary fine Gibbs weight can couple all 128 block-selected
    -- fine links and all 896 spectators. The spectators are INTEGRATED,
    -- not silently dropped as in an invalid bare-Wilson argument.
    originalSelected64Pair896SpectatorEffectiveDensity :
      (fineWeight : Vec Pair 64 → Vec Link 896 → ℝ) →
      Vec Link 64 → ℝ
    originalSelected64Pair896SpectatorEffectiveDensity fineWeight =
      originalAllPairsEffectiveDensity
        (λ pairs →
          Product.productIntegral source
            (λ spectators → fineWeight pairs spectators))

    selected64Pair896SpectatorWeightedDisintegration :
      (fineWeight : Vec Pair 64 → Vec Link 896 → ℝ)
      (coarseObservable : Vec Link 64 → ℝ) →
      finePairsIntegral
        (λ pairs →
          Product.productIntegral source
            (λ spectators → fineWeight pairs spectators)
            *ℝ coarseObservable (actualPairBlockVector pairs))
      ≡
      Product.productIntegral source
        (λ blocks →
          originalSelected64Pair896SpectatorEffectiveDensity
            fineWeight blocks *ℝ coarseObservable blocks)
    selected64Pair896SpectatorWeightedDisintegration
        fineWeight observable =
      originalAllPairsWeightedHaarDisintegration
        (λ pairs →
          Product.productIntegral source
            (λ spectators → fineWeight pairs spectators))
        observable
