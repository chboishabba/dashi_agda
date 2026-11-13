module DASHI.Physics.YangMills.YMClayOriginalWilsonEffectiveBetaFiniteDifferenceExact where

-- Exact original physical Wilson coupling-variation corollary of M.02/F19.
-- At every beta, the SAME native 1024-bond physical partition equals
-- its 64-block/896-spectator source-derived effective partition.
-- Thus every finite FIRST and SECOND Wilson coupling difference also
-- agrees. No differentiation-under-Haar theorem is assumed.
--
-- THIS IS NOT the Yang-Mills perturbative beta function. The latter
-- in CMP109 is extracted from a mixed EXTERNAL-MOMENTUM derivative
-- of the off-diagonal vacuum-polarization tensor, and requires
-- the separate Bałaban #1498 Wilson/ghost/Haar physical scalar weld.
--
-- No UV-uniform effective-minus-bare decay, volume convergence,
-- continuum measure, spectral gap or Clay claim is implied.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong₂)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _-ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClayNative1024WeightedWilsonReindexExact as Original
import DASHI.Physics.YangMills.YMClayOriginalWilsonPhysicalF19PartitionExact as F19

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (source : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory source)
  where

  fineOriginalWilsonPartition : ℝ → ℝ
  fineOriginalWilsonPartition beta =
    Haar.productIntegral source
      (Original.originalWilsonVectorWeight
        theory traceData exponential beta)

  constructedOriginalEffectivePartition : ℝ → ℝ
  constructedOriginalEffectivePartition beta =
    Haar.productIntegral source
      (F19.originalFullInteractingEffectiveDensity
        theory traceData exponential beta source bilateral)

  originalCouplingPointwisePartitionEquality :
    ∀ beta →
    fineOriginalWilsonPartition beta
      ≡ constructedOriginalEffectivePartition beta
  originalCouplingPointwisePartitionEquality beta =
    F19.originalFinePhysicalPartitionEqualsActualEffectivePartition
      theory traceData exponential beta source bilateral

  originalCouplingFirstFiniteDifferenceExact :
    ∀ betaLeft betaRight →
    (fineOriginalWilsonPartition betaRight
      -ℝ fineOriginalWilsonPartition betaLeft)
    ≡
    (constructedOriginalEffectivePartition betaRight
      -ℝ constructedOriginalEffectivePartition betaLeft)
  originalCouplingFirstFiniteDifferenceExact betaLeft betaRight =
    cong₂ _-ℝ_
      (originalCouplingPointwisePartitionEquality betaRight)
      (originalCouplingPointwisePartitionEquality betaLeft)

  originalCouplingSecondFiniteDifferenceExact :
    ∀ beta0 beta1 beta2 →
    ((fineOriginalWilsonPartition beta2
        -ℝ fineOriginalWilsonPartition beta1)
       -ℝ
      (fineOriginalWilsonPartition beta1
        -ℝ fineOriginalWilsonPartition beta0))
    ≡
    ((constructedOriginalEffectivePartition beta2
        -ℝ constructedOriginalEffectivePartition beta1)
       -ℝ
      (constructedOriginalEffectivePartition beta1
        -ℝ constructedOriginalEffectivePartition beta0))
  originalCouplingSecondFiniteDifferenceExact beta0 beta1 beta2 =
    cong₂ _-ℝ_
      (originalCouplingFirstFiniteDifferenceExact beta1 beta2)
      (originalCouplingFirstFiniteDifferenceExact beta0 beta1)

-- The next analytic claim would need an actual physical derivative
-- of the original Wilson partition and compatible Bishop/Haar limit
-- exchange. Equality of all finite differences is a useful lemma
-- but is NOT that limit or Bałaban's off-diagonal tensor beta.
