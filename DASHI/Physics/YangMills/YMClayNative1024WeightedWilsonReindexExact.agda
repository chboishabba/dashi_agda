module DASHI.Physics.YangMills.YMClayNative1024WeightedWilsonReindexExact where

------------------------------------------------------------------------
-- YM M.01 -> M.02: ORIGINAL 1024-bond interacting Wilson density under
-- the ACTUAL 64 ordered-pair + 896 spectator adjacent-swap reindex.
--
-- Crucially this transforms the entire fine interacting Wilson weight.
-- It never replaces the blocked effective measure with bare Wilson
-- action, ignores spectators, or assumes that Gibbs bonds factorize.
-- The chosen compact one-link integral and Fubini are explicit inputs.
--
-- Agda exact-head / transitive trust acceptance still required.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Wilson
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Native
import DASHI.Physics.YangMills.YMClayNative1024ClosedReindexHaarConsequencesExact as Reindex
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar

-- Every adjacent-swap programme has a computable inverse.
inverseProgram : ∀ {n} → Haar.LinkPermutation n → Haar.LinkPermutation n
inverseProgram Haar.identity = Haar.identity
inverseProgram (Haar.compose first second) =
  Haar.compose (inverseProgram second) (inverseProgram first)
inverseProgram (Haar.fixHead inner) = Haar.fixHead (inverseProgram inner)
inverseProgram Haar.swapHead = Haar.swapHead

-- This proof is structural in the ORIGINAL permutation syntax, not a
-- source equality token or a separately chosen inverse map.
inverseAfterForward :
  ∀ {Value : Set} {n}
    (program : Haar.LinkPermutation n)
    (values : Vec.Vec Value n) →
  Haar.permuteLinks (inverseProgram program)
    (Haar.permuteLinks program values) ≡ values
inverseAfterForward Haar.identity values = refl
inverseAfterForward (Haar.compose first second) values =
  trans
    (cong (Haar.permuteLinks (inverseProgram second))
      (inverseAfterForward first (Haar.permuteLinks second values)))
    (inverseAfterForward second values)
inverseAfterForward (Haar.fixHead inner) (head Vec.∷ tail) =
  cong (Vec._∷_ head) (inverseAfterForward inner tail)
inverseAfterForward Haar.swapHead
    (first Vec.∷ second Vec.∷ tail) = refl

productIntegralCongruent :
  ∀ {Value : Set} {n}
    (source : Haar.OneLinkProductHaar Value)
    (left right : Vec.Vec Value n → ℝ) →
    (∀ values → left values ≡ right values) →
    Haar.productIntegral source left ≡ Haar.productIntegral source right
productIntegralCongruent {n = zero} source left right same = same Vec.[]
productIntegralCongruent {n = suc n} source left right same =
  Haar.integrateCongruent source _ _
    (λ head → productIntegralCongruent source
      (λ tail → left (head Vec.∷ tail))
      (λ tail → right (head Vec.∷ tail))
      (λ tail → same (head Vec.∷ tail)))

-- This is a general, same-source WEIGHTED finite integral reindex:
-- even the full interacting density is inside the moved integrand.
actualWeightedReindex :
  ∀ {Value : Set} {n}
    (source : Haar.OneLinkProductHaar Value)
    (program : Haar.LinkPermutation n)
    (originalWeight : Vec.Vec Value n → ℝ) →
  let sortedWeight = λ sorted →
        originalWeight
          (Haar.permuteLinks (inverseProgram program) sorted)
  in
  Haar.productIntegral source originalWeight
    ≡ Haar.productIntegral source sortedWeight
actualWeightedReindex source program originalWeight =
  let
    sortedWeight = λ sorted →
      originalWeight
        (Haar.permuteLinks (inverseProgram program) sorted)
  in
  trans
    (productIntegralCongruent source
      originalWeight
      (λ original → sortedWeight (Haar.permuteLinks program original))
      (λ original →
        sym (cong originalWeight (inverseAfterForward program original))))
    (Haar.productHaarPermutationInvariant source program sortedWeight)

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  originalWilsonVectorWeight : Vec.Vec Link Native.Count → ℝ
  originalWilsonVectorWeight original =
    Wilson.periodicSUNGibbsDensity theory traceData exponential 3 beta
      (Codec.decodeOriginalBonds 4 original)

  actualPairProgram : Haar.LinkPermutation Native.Count
  actualPairProgram = Reindex.actualPairProgram theory

  physicallySortedWilsonWeight : Vec.Vec Link Native.Count → ℝ
  physicallySortedWilsonWeight sorted =
    originalWilsonVectorWeight
      (Haar.permuteLinks (inverseProgram actualPairProgram) sorted)

  -- The original physical Wilson action, not an independent effective
  -- source chosen after blocking, is reconstructed pointwise.
  sortedWilsonWeightRecoversOriginal :
    ∀ original →
    physicallySortedWilsonWeight
      (Haar.permuteLinks actualPairProgram original)
      ≡ originalWilsonVectorWeight original
  sortedWilsonWeightRecoversOriginal original =
    cong originalWilsonVectorWeight
      (inverseAfterForward actualPairProgram original)

  -- Its FULL partition is unchanged, with all spectator interactions
  -- retained in physicallySortedWilsonWeight.
  originalWilsonPartitionIsSortedPhysicalPartition :
    (source : Haar.OneLinkProductHaar Link) →
    Haar.productIntegral source originalWilsonVectorWeight
      ≡ Haar.productIntegral source physicallySortedWilsonWeight
  originalWilsonPartitionIsSortedPhysicalPartition source =
    actualWeightedReindex source actualPairProgram originalWilsonVectorWeight
