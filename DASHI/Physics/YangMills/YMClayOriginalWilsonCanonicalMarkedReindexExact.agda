module DASHI.Physics.YangMills.YMClayOriginalWilsonCanonicalMarkedReindexExact where

-- M.02/F19 marked lift: the existing ORIGINAL 1024-bond native
-- adjacent-swap programme already preserves every full interacting
-- Wilson-weighted marked observable, not only the partition.
--
-- NEW: prove original permutation has the correct TWO-SIDED inverse
-- at the vector source level (not an assumed inverse action).
-- Then apply the existing exact arbitrary-weight Haar change of
-- variables to the original Wilson Gibbs weight * marked observable.
--
-- This theorem holds for EVERY arbitrary real function on the same
-- SORTED 1024-link carrier, including one- and two-source marks.
-- No spectator coupling is discarded, no second measure is introduced,
-- and the normalized denominator is the SAME original physical Z.
--
-- Unpaid: identify an actual sorted mark with one of the 64 coarse
-- BLOCKED HOLONOMY observables in the F19 all-pairs source, and
-- obtain kernel receipts for the imported native reindex chain.
--
-- No UV-uniform RG estimate or continuum limit is claimed.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
import Data.Vec.Base as Vec
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayNative1024WeightedWilsonReindexExact as Original
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Native

inverseProgramTwice :
  ∀ {n} (program : Haar.LinkPermutation n) →
  Original.inverseProgram (Original.inverseProgram program) ≡ program
inverseProgramTwice Haar.identity = refl
inverseProgramTwice (Haar.compose first second) =
  cong₂ Haar.compose
    (inverseProgramTwice first)
    (inverseProgramTwice second)
inverseProgramTwice (Haar.fixHead program) =
  cong Haar.fixHead (inverseProgramTwice program)
inverseProgramTwice Haar.swapHead = refl

forwardAfterInverse :
  ∀ {Value : Set} {n}
    (program : Haar.LinkPermutation n)
    (values : Vec.Vec Value n) →
  Haar.permuteLinks program
    (Haar.permuteLinks (Original.inverseProgram program) values)
  ≡ values
forwardAfterInverse program values =
  trans
    (cong
      (λ inv → Haar.permuteLinks inv
        (Haar.permuteLinks (Original.inverseProgram program) values))
      (sym (inverseProgramTwice program)))
    (Original.inverseAfterForward
      (Original.inverseProgram program) values)

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (source : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  actualProgramme : Haar.LinkPermutation Native.Count
  actualProgramme = Original.actualPairProgram theory

  OriginalVector : Set
  OriginalVector = Vec.Vec Link Native.Count

  originalMarkedWilsonWeight : (OriginalVector → ℝ) → OriginalVector → ℝ
  originalMarkedWilsonWeight observable original =
    Original.originalWilsonVectorWeight theory traceData exponential beta original
      *ℝ observable (Haar.permuteLinks actualProgramme original)

  sortedMarkedWilsonWeight : (OriginalVector → ℝ) → OriginalVector → ℝ
  sortedMarkedWilsonWeight observable sorted =
    Original.physicallySortedWilsonWeight
      theory traceData exponential beta sorted
      *ℝ observable sorted

  canonicalOriginalMarkedNumerator : (OriginalVector → ℝ) → ℝ
  canonicalOriginalMarkedNumerator observable =
    Haar.productIntegral source (originalMarkedWilsonWeight observable)

  sortedOriginalMarkedNumerator : (OriginalVector → ℝ) → ℝ
  sortedOriginalMarkedNumerator observable =
    Haar.productIntegral source (sortedMarkedWilsonWeight observable)

  -- The only nontrivial step after original weighted Haar reindex:
  -- the inverse permutation is TWO-SIDED, so the marked observable
  -- on sorted originals is exactly the original mark pulled forward.
  originalWeightedMarkedReindexExact :
    ∀ observable →
    canonicalOriginalMarkedNumerator observable
      ≡ sortedOriginalMarkedNumerator observable
  originalWeightedMarkedReindexExact observable =
    trans
      (Original.actualWeightedReindex
        source actualProgramme (originalMarkedWilsonWeight observable))
      (Original.productIntegralCongruent
        source
        (λ sorted →
          originalMarkedWilsonWeight observable
            (Haar.permuteLinks (Original.inverseProgram actualProgramme) sorted))
        (sortedMarkedWilsonWeight observable)
        (λ sorted →
          cong
            (λ value →
              Original.physicallySortedWilsonWeight
                theory traceData exponential beta sorted
              *ℝ observable value)
            (forwardAfterInverse actualProgramme sorted)))

  canonicalOriginalMarkedNormalized :
    (divide : ℝ → ℝ → ℝ) →
    (OriginalVector → ℝ) → ℝ
  canonicalOriginalMarkedNormalized divide observable =
    divide
      (canonicalOriginalMarkedNumerator observable)
      (Haar.productIntegral source
        (Original.originalWilsonVectorWeight
          theory traceData exponential beta))

  sortedOriginalMarkedNormalized :
    (divide : ℝ → ℝ → ℝ) →
    (OriginalVector → ℝ) → ℝ
  sortedOriginalMarkedNormalized divide observable =
    divide
      (sortedOriginalMarkedNumerator observable)
      (Haar.productIntegral source
        (Original.physicallySortedWilsonWeight
          theory traceData exponential beta))

  -- Normalized source identity, with no new independent denominator.
  originalCanonicalMarkedNormalizedIsSorted :
    (divide : ℝ → ℝ → ℝ) →
    ∀ observable →
    canonicalOriginalMarkedNormalized divide observable
    ≡ sortedOriginalMarkedNormalized divide observable
  originalCanonicalMarkedNormalizedIsSorted divide observable =
    cong₂ divide
      (originalWeightedMarkedReindexExact observable)
      (Original.originalWilsonPartitionIsSortedPhysicalPartition
        theory traceData exponential beta source)

  -- This is a stronger elementary original-physics source weld than
  -- equality of Z alone: it is valid for ALL measurable/abstract
  -- sorted marks admitted by the selected OneLinkProductHaar record.
  -- The F19 native coarse-block observable decoder remains a separate
  -- explicit physical map obligation.
