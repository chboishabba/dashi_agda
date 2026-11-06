module DASHI.Physics.YangMills.YMClayNative1024ClosedReindexHaarConsequencesExact where

------------------------------------------------------------------------
-- YM M.01: actual original 1024 positive-bond C3 AND 64-pair/896-spectator
-- closed sorting candidates, promoted to arbitrary link values and finite
-- ordered product-Haar reindexing consequences WITHOUT free permutations.
--
-- All sources are the SAME original side-four periodic bond codec.
-- In particular the pair/spectator permutation is not guessed anew.
-- The source's closed Bool/refl proofs MUST normalize in the Agda kernel.
-- One-link Haar/Fubini is an explicit existing physical input and is not
-- constructed by this finite combinatorial result.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClayNativeClosedThreeEqualitiesCandidateExact as Closed
import DASHI.Physics.YangMills.YMClayNativeC3AdjacentSortProgramExact as Sort
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Single
import DASHI.Physics.YangMills.YMClayNativeSideFourPairSpectatorSortProgramExact as PairSort
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayNativeSideFourC3VectorWeldExact as C3
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec

-- The original C3 permutation, universally on the literal 1024 labels
-- and thus on any original native value vector, including SU(N) links.
actualNativeC3EveryOriginalVector :
  ∀ {Value : Set} (values : Vec.Vec Value Single.Count) →
  Haar.permuteLinks Sort.constructedNativeC3Program values
    ≡
  C3.forwardVector values
actualNativeC3EveryOriginalVector =
  Sort.constructedNativeC3AllVectors Closed.originalC3CanonicalLabelsClosed

-- Real one-link Haar/Fubini invariance for the ACTUAL constructed C3
-- adjacent-swap program (not a free symmetry/orbit axiom).
actualNativeC3FiniteProductHaarInvariant :
  ∀ {Value : Set} (oneLink : Haar.OneLinkProductHaar Value)
    (observable : Vec.Vec Value Single.Count → ℝ) →
  Haar.productIntegral oneLink
    (λ links → observable
      (Haar.permuteLinks Sort.constructedNativeC3Program links))
    ≡ Haar.productIntegral oneLink observable
actualNativeC3FiniteProductHaarInvariant oneLink observable =
  Haar.productHaarPermutationInvariant
    oneLink Sort.constructedNativeC3Program observable

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  actualPairProgram : Haar.LinkPermutation Single.Count
  actualPairProgram =
    PairSort.constructedOriginalPairSpectatorProgram
      theory (Closed.originalPairSpectatorLengthClosed theory)

  -- This is the exact native 128 selected labels followed by the
  -- 896 ORIGINAL spectator labels, transported to arbitrary link values.
  -- The right-hand side reads the native labels from the SAME decoder.
  actualPairSpectatorReindexEveryOriginalVector :
    ∀ {Value : Set} (values : Vec.Vec Value Single.Count) →
    Haar.permuteLinks actualPairProgram values
      ≡
    Vec.map
      (Codec.decodeOriginalBonds
        4 values)
      (PairSort.originalPairSpectatorTargetVector
        theory (Closed.originalPairSpectatorLengthClosed theory))
  actualPairSpectatorReindexEveryOriginalVector values =
    let
      read = Codec.decodeOriginalBonds
        4 values
      target = PairSort.originalPairSpectatorTargetVector
        theory (Closed.originalPairSpectatorLengthClosed theory)
    in
    trans
      (cong (Haar.permuteLinks actualPairProgram)
        (sym (Single.reconstructFromCanonicalLabels values)))
      (trans
        (sym (Single.permuteLinksMap
          read actualPairProgram Single.canonicalLabelVector))
        (cong (Vec.map read)
          (Closed.originalPairSpectatorCanonicalLabelsClosed theory)))

  -- Exact finite product-Haar invariance under the physical pair/spectator
  -- sort, using the ORIGINAL adjacent-swap program. This is an integration
  -- coordinate reorder; the interacting Wilson weight must remain inside
  -- the transformed integrand.
  actualPairSpectatorFiniteProductHaarInvariant :
    ∀ {Value : Set} (oneLink : Haar.OneLinkProductHaar Value)
      (observable : Vec.Vec Value Single.Count → ℝ) →
    Haar.productIntegral oneLink
      (λ links → observable (Haar.permuteLinks actualPairProgram links))
      ≡ Haar.productIntegral oneLink observable
  actualPairSpectatorFiniteProductHaarInvariant oneLink observable =
    Haar.productHaarPermutationInvariant
      oneLink actualPairProgram observable
