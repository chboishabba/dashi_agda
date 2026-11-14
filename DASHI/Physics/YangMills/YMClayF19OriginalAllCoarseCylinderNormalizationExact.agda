module DASHI.Physics.YangMills.YMClayF19OriginalAllCoarseCylinderNormalizationExact where

------------------------------------------------------------------------
-- F19 -> ORIGINAL PHYSICAL ALL-COARSE-OBSERVABLE NORMALIZATION.
--
-- NEW SOURCE A PROOF, not a new probability oracle:
--
-- For EVERY original SU(N) coarse bounded/test observable F on the
-- actual 64-link F19 carrier, the true interacting 1024-link Wilson
-- weight inside the original 64 ordered pairs + 896 spectator integral
-- disintegrates to the SAME physical effective F19 coarse density.
--
-- Both sides are divided by the SAME original positive source-normalizer
-- (the F19 same-Wilson-partition theorem), using cong₂ on the actual
-- physical scalar division. F may be any function of the original
-- 64 coarse links, not a single Wilson-loop or two-mark exponential.
--
-- This proves the INTRINSIC F19 normalized cylinder equality. It does
-- NOT prove a pointwise identification of F19's pair-block map with
-- R445's independently selected nativeSUNBlockLinks {m=1}{l=1},
-- nor construct the original renormalized R445 target/counterterms.
--
-- Physical cutoff-uniform local TV, Wilson/target action oscillation,
-- P0 Ward/coefficient RG, E1/D1/D2 and the Clay gap are still OPEN.
--
-- Sources: Wilson lattice action, F19 original 1024-bond reindex,
-- weighted Haar Fubini and 64-fibre disintegration; source priority
-- retained under AGENTS.md and Docs/SourceAttributionPolicy.md.
--
-- This uses original legacy RealAnalysisAxioms, hence NOT --safe.
-- Source-written only; pinned Agda 2.9 kernel acceptance pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong₂)
import Data.Vec.Base as Vec
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNWeightedDisjointPairFibreReparamExact as Fibre
import DASHI.Physics.YangMills.YMClayOriginalWilsonF19ConcreteWeightExact as F19Physical
import DASHI.Physics.YangMills.YMClayNative1024WeightedWilsonReindexExact as Original
import DASHI.Physics.YangMills.YMClayOriginalWilsonPhysicalF19PartitionExact as F19

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (source : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory source)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  OriginalF19CoarseTest : Set
  OriginalF19CoarseTest = Vec.Vec Link 64 → ℝ

  originalF19SortedPhysicalWeight :
    Vec.Vec (Fibre.Pair theory source bilateral) 64 →
    Vec.Vec Link 896 → ℝ
  originalF19SortedPhysicalWeight pairs spectators =
    Original.physicallySortedWilsonWeight
      theory traceData exponential beta
      (F19Physical.originalPairsAndSpectators pairs spectators)

  -- The numerator on the left is the ACTUAL physical F19 nested fine
  -- interacting weight. Its arbitrary F is evaluated on the original
  -- noncommutative pair-block vector, before spectators are integrated.
  -- The numerator on the right is the ACTUAL physical F19 effective
  -- density from the same original 1024-link Wilson weight.
  originalF19AllCoarseNumeratorsSamePhysicalSource :
    (F : OriginalF19CoarseTest) →
    Fibre.finePairsIntegral theory source bilateral
      (λ pairs →
        Haar.productIntegral source
          (λ spectators → originalF19SortedPhysicalWeight
            pairs spectators)
        *ℝ F (Fibre.actualPairBlockVector
            theory source bilateral pairs))
    ≡
    Haar.productIntegral source
      (λ coarse →
        F19.originalFullInteractingEffectiveDensity
          theory traceData exponential beta source bilateral
          coarse
        *ℝ F coarse)
  originalF19AllCoarseNumeratorsSamePhysicalSource F =
    Fibre.selected64Pair896SpectatorWeightedDisintegration
      theory source bilateral originalF19SortedPhysicalWeight F

  -- This is an actual division-of-the-two-real-physical-functionals
  -- theorem for EVERY F, not an explicit "assume expectations equal".
  -- Original strict positivity is in F19 and not replaced by a
  -- postulated new Z; no division cancellation axiom is added.
  originalF19AllCoarseNormalizedSamePhysicalSource :
    (divide : ℝ → ℝ → ℝ)
    (F : OriginalF19CoarseTest) →
    divide
      (Fibre.finePairsIntegral theory source bilateral
        (λ pairs →
          Haar.productIntegral source
            (λ spectators → originalF19SortedPhysicalWeight
              pairs spectators)
          *ℝ F (Fibre.actualPairBlockVector
              theory source bilateral pairs)))
      (Haar.productIntegral source
        (Original.originalWilsonVectorWeight
          theory traceData exponential beta))
    ≡
    divide
      (Haar.productIntegral source
        (λ coarse →
          F19.originalFullInteractingEffectiveDensity
            theory traceData exponential beta source bilateral
            coarse
          *ℝ F coarse))
      (Haar.productIntegral source
        (F19.originalFullInteractingEffectiveDensity
          theory traceData exponential beta source bilateral))
  originalF19AllCoarseNormalizedSamePhysicalSource divide F =
    cong₂ divide
      (originalF19AllCoarseNumeratorsSamePhysicalSource F)
      (F19.originalFinePhysicalPartitionEqualsActualEffectivePartition
        theory traceData exponential beta source bilateral)
