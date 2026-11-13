module DASHI.Physics.YangMills.YMClayOriginalWilsonCanonicalBlockedMarkF19Exact where

-- Physical M.02/F19 source: original 1024-bond Wilson Gibbs expectation
-- of an ACTUAL blocked-holonomy observable equals the selected
-- effective-density expectation. The entire interacting Wilson
-- density, all 64 disjoint pair holonomies and 896 spectators are
-- retained, and no new Haar measure is chosen.
--
-- The proof composes, rather than restarts:
--   native original canonical adjacent swap on MARKED densities,
--   original 1024-to-64-pair/896-spectator inverse vector codec,
--   original flat/nested Fubini,
--   original 64-pair full coupled-weight Haar disintegration.
--
-- A fixed level-four original pair blocking is intended: this is
-- FINITE, not the uniform P0.F effective-minus-bare Wilson estimate.
--
-- SOURCE WRITTEN. Local Agda checker / all imports pending.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)
import Data.Vec.Base as Vec
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Native
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNWeightedDisjointPairFibreReparamExact as Fibre
import DASHI.Physics.YangMills.YMClayNativePairsSpectatorsFubiniExact as Flat
import DASHI.Physics.YangMills.YMClayOriginalWilsonF19ConcreteWeightExact as Physical
import DASHI.Physics.YangMills.YMClayOriginalWilsonPhysicalF19PartitionExact as Partition
import DASHI.Physics.YangMills.YMClayOriginalWilsonCanonicalMarkedReindexExact as Mark
import DASHI.Physics.YangMills.YMClayOriginalWilsonPairSpectatorDecoderExact as Split
import DASHI.Physics.YangMills.YMClayNative1024WeightedWilsonReindexExact as Original

-- Ordinary transport; no altered 1,024-link integral measure.
productIntegralAlongCountEquality :
  ∀ {A : Set} {n m : Nat}
    (oneLink : Haar.OneLinkProductHaar A)
    (eq : n ≡ m)
    (integrand : Vec.Vec A n → ℝ) →
  Haar.productIntegral oneLink integrand
  ≡
  Haar.productIntegral oneLink
    (λ new → integrand (subst (Vec.Vec A) (sym eq) new))
productIntegralAlongCountEquality oneLink refl integrand = refl

substThenUnsubst :
  ∀ {A : Set} {n m : Nat}
    (eq : n ≡ m) (xs : Vec.Vec A m) →
  subst (Vec.Vec A) eq
    (subst (Vec.Vec A) (sym eq) xs) ≡ xs
substThenUnsubst refl xs = refl

-- Source native F19 pair integral congruence, derived from the SAME
-- original one-link Haar congruence, not an assumed new law.
module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (source : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory source)
    (linear : Ordered.OneLinkOrderedHaarAlgebra source)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  Pair : Set
  Pair = Torus.Product Link Link

  actualProgram : Haar.LinkPermutation Native.Count
  actualProgram = Original.actualPairProgram theory

  originalCountToSortedCount :
    Native.Count ≡ Physical.twice 64 + 896
  originalCountToSortedCount = Codec.originalSideFourCountIs1024

  toFlat : Vec.Vec Link Native.Count → Vec.Vec Link (Physical.twice 64 + 896)
  toFlat = subst (Vec.Vec Link) originalCountToSortedCount

  toNative : Vec.Vec Link (Physical.twice 64 + 896) → Vec.Vec Link Native.Count
  toNative = subst (Vec.Vec Link) (sym originalCountToSortedCount)

  coarseFromSortedOriginal :
    Vec.Vec Link Native.Count → Vec.Vec Link 64
  coarseFromSortedOriginal sorted =
    Fibre.actualPairBlockVector theory source bilateral
      (Torus.first (Split.sourceSideFourDecode (toFlat sorted)))

  -- Original SOURCE coarse observable, defined on all 1,024 canonical
  -- bond fields by actual adjacent permutation and pair holonomies.
  canonicalSourceCoarseObservable :
    (Vec.Vec Link 64 → ℝ) → Vec.Vec Link Native.Count → ℝ
  canonicalSourceCoarseObservable observable original =
    observable
      (coarseFromSortedOriginal (Haar.permuteLinks actualProgram original))

  sortedSourceCoarseObservable :
    (Vec.Vec Link 64 → ℝ) → Vec.Vec Link Native.Count → ℝ
  sortedSourceCoarseObservable observable sorted =
    observable (coarseFromSortedOriginal sorted)

  -- The canonical 64-pair ordered source is exactly recovered from
  -- its 128 concatenated links followed by the 896 spectators.
  sourceSortedBlockIsOriginalPairs :
    ∀ (pairs : Vec.Vec Pair 64)
      (spectators : Vec.Vec Link 896) →
    coarseFromSortedOriginal
      (Physical.originalPairsAndSpectators pairs spectators)
    ≡ Fibre.actualPairBlockVector theory source bilateral pairs
  sourceSortedBlockIsOriginalPairs pairs spectators =
    let
      flat : Vec.Vec Link (Physical.twice 64 + 896)
      flat = Physical.appendVec (Physical.flattenPairs pairs) spectators
    in
    trans
      (cong (Fibre.actualPairBlockVector theory source bilateral
        ∘ Torus.first ∘ Split.sourceSideFourDecode)
        (substThenUnsubst originalCountToSortedCount flat))
      (cong (Fibre.actualPairBlockVector theory source bilateral
        ∘ Torus.first)
        (Split.sourceSideFourSplitJoin pairs spectators))
    where open import Function using (_∘_)

  originalFinePhysicalWeight :
    Vec.Vec Pair 64 → Vec.Vec Link 896 → ℝ
  originalFinePhysicalWeight =
    Physical.physicalWeight theory traceData exponential beta source bilateral linear

  -- Literal original sorted Wilson observable, including all coupled
  -- spectator links (not a bare Wilson replacement).
  flatSourceMarkedWeight :
    (Vec.Vec Link 64 → ℝ) →
    Vec.Vec Link (Physical.twice 64 + 896) → ℝ
  flatSourceMarkedWeight observable flat =
    Original.physicallySortedWilsonWeight
      theory traceData exponential beta (toNative flat)
      *ℝ observable
        (Fibre.actualPairBlockVector theory source bilateral
          (Torus.first (Split.sourceSideFourDecode flat)))

  finePairsIntegralCongruent :
    ∀ {n} (left right : Vec.Vec Pair n → ℝ) →
    (∀ pairs → left pairs ≡ right pairs) →
    Fibre.finePairsIntegral theory source bilateral left
      ≡ Fibre.finePairsIntegral theory source bilateral right
  finePairsIntegralCongruent {n = Agda.Builtin.Nat.zero} left right same =
    same Vec.[]
  finePairsIntegralCongruent {n = Agda.Builtin.Nat.suc n} left right same =
    Haar.integrateCongruent source _ _
      (λ first →
        Haar.integrateCongruent source _ _
          (λ second →
            finePairsIntegralCongruent
              (λ pairs → left (Torus.pair first second Vec.∷ pairs))
              (λ pairs → right (Torus.pair first second Vec.∷ pairs))
              (λ pairs → same (Torus.pair first second Vec.∷ pairs))))

  -- The explicit sorted-marked-1024 -> flat-1024 identity transports
  -- a single selected native bond count equality, no floating casts.
  markedSortedToFlat :
    ∀ observable →
    Mark.sortedOriginalMarkedNumerator
      theory traceData exponential beta source
      (sortedSourceCoarseObservable observable)
    ≡ Haar.productIntegral source (flatSourceMarkedWeight observable)
  markedSortedToFlat observable =
    trans
      (productIntegralAlongCountEquality source
        originalCountToSortedCount
        (Mark.sortedMarkedWilsonWeight
          theory traceData exponential beta
          (sortedSourceCoarseObservable observable)))
      (Original.productIntegralCongruent source _ _
        (λ flat →
          cong
            (λ sorted →
              Original.physicallySortedWilsonWeight
                theory traceData exponential beta sorted
                *ℝ observable
                  (coarseFromSortedOriginal sorted))
            (sym (substThenUnsubst
              (sym originalCountToSortedCount) (toNative flat)))))

  -- Original source real Fubini + SAME weighted physical 64-pair test.
  markedFlatToActualFinePairs :
    ∀ observable →
    Haar.productIntegral source (flatSourceMarkedWeight observable)
    ≡
    Fibre.finePairsIntegral theory source bilateral
      (λ pairs →
        Haar.productIntegral source
          (λ spectators →
            originalFinePhysicalWeight pairs spectators
             *ℝ observable
               (Fibre.actualPairBlockVector
                 theory source bilateral pairs)))
  markedFlatToActualFinePairs observable =
    trans
      (Flat.originalFlatEqualsNestedPairsSpectators
        theory source bilateral (flatSourceMarkedWeight observable))
      (finePairsIntegralCongruent
        (λ pairs →
          Haar.productIntegral source
            (λ spectators →
              flatSourceMarkedWeight observable
                (Physical.appendVec (Physical.flattenPairs pairs) spectators)))
        (λ pairs →
          Haar.productIntegral source
            (λ spectators →
              originalFinePhysicalWeight pairs spectators
              *ℝ observable
                (Fibre.actualPairBlockVector
                  theory source bilateral pairs)))
        (λ pairs →
          Original.productIntegralCongruent source _ _
            (λ spectators →
              cong
                (λ blocks →
                  originalFinePhysicalWeight pairs spectators
                  *ℝ observable blocks)
                (cong
                  (Fibre.actualPairBlockVector theory source bilateral
                    ∘ Torus.first)
                  (Split.sourceSideFourSplitJoin pairs spectators))))
    where open import Function using (_∘_)

  -- The requested F19 original-Wilson-Gibbs pushforward for EVERY
  -- observable of the 64 blocked holonomies, not just the partition.
  originalFineCanonicalBlockedNumeratorEqualsPhysicalEffective :
    ∀ observable →
    Mark.canonicalOriginalMarkedNumerator
      theory traceData exponential beta source
      (sortedSourceCoarseObservable observable)
    ≡
    Haar.productIntegral source
      (λ blocks →
        Fibre.originalSelected64Pair896SpectatorEffectiveDensity
          theory source bilateral linear
          originalFinePhysicalWeight blocks
          *ℝ observable blocks)
  originalFineCanonicalBlockedNumeratorEqualsPhysicalEffective observable =
    trans
      (Mark.originalWeightedMarkedReindexExact
        theory traceData exponential beta source
        (sortedSourceCoarseObservable observable))
      (trans
        (markedSortedToFlat observable)
        (trans
          (markedFlatToActualFinePairs observable)
          (Fibre.selected64Pair896SpectatorWeightedDisintegration
            theory source bilateral linear
            originalFinePhysicalWeight observable)))

  originalCanonicalBlockedNormalized :
    (divide : ℝ → ℝ → ℝ) →
    (Vec.Vec Link 64 → ℝ) → ℝ
  originalCanonicalBlockedNormalized divide observable =
    divide
      (Mark.canonicalOriginalMarkedNumerator
        theory traceData exponential beta source
        (sortedSourceCoarseObservable observable))
      (Haar.productIntegral source
        (Original.originalWilsonVectorWeight
          theory traceData exponential beta))

  originalEffectiveBlockedNormalized :
    (divide : ℝ → ℝ → ℝ) →
    (Vec.Vec Link 64 → ℝ) → ℝ
  originalEffectiveBlockedNormalized divide observable =
    divide
      (Haar.productIntegral source
        (λ blocks →
          Fibre.originalSelected64Pair896SpectatorEffectiveDensity
            theory source bilateral linear
            originalFinePhysicalWeight blocks
            *ℝ observable blocks))
      (Haar.productIntegral source
        (Partition.originalFullInteractingEffectiveDensity
          theory traceData exponential beta source bilateral))

  -- Full ORIGINAL canonical 1024-bond Wilson observable -> ACTUAL
  -- effective-density normalized blocked-observable pushforward.
  -- Both numerator AND denominator are source-preserving identities.
  originalCanonicalBlockedNormalizedEqualsPhysicalEffective :
    (divide : ℝ → ℝ → ℝ) →
    ∀ observable →
    originalCanonicalBlockedNormalized divide observable
    ≡ originalEffectiveBlockedNormalized divide observable
  originalCanonicalBlockedNormalizedEqualsPhysicalEffective divide observable =
    cong₂ divide
      (originalFineCanonicalBlockedNumeratorEqualsPhysicalEffective observable)
      (Partition.originalFinePhysicalPartitionEqualsActualEffectivePartition
        theory traceData exponential beta source bilateral)
