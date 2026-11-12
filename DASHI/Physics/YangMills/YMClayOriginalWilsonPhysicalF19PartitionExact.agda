module DASHI.Physics.YangMills.YMClayOriginalWilsonPhysicalF19PartitionExact where

-- YM M.02: SAME original 1024-link Wilson Gibbs partition, reindexed
-- to the physical ordered F19 64-pair/896-spectator fine integral.
-- Reuses original-weight inverse permutation and general flat/nested
-- original product-Haar theorem; arbitrary coupled spectators remain.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNWeightedDisjointPairFibreReparamExact as Fibre
import DASHI.Physics.YangMills.YMClayNative1024WeightedWilsonReindexExact as Original
import DASHI.Physics.YangMills.YMClayNativePairsSpectatorsFubiniExact as Flat
import DASHI.Physics.YangMills.YMClayOriginalWilsonF19ConcreteWeightExact as F19Physical

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

  originalFinePhysicalPartitionEqualsNestedF19 :
    Haar.productIntegral source
      (Original.originalWilsonVectorWeight
        theory traceData exponential beta)
    ≡
    Fibre.finePairsIntegral theory source bilateral
      (λ pairs →
        Haar.productIntegral source
          (λ spectators →
            Original.physicallySortedWilsonWeight
              theory traceData exponential beta
              (F19Physical.originalPairsAndSpectators pairs spectators)))
  originalFinePhysicalPartitionEqualsNestedF19 =
    trans
      (Original.originalWilsonPartitionIsSortedPhysicalPartition
        theory traceData exponential beta source)
      (Flat.originalFlatEqualsNestedPairsSpectators
        theory source bilateral
        (Original.physicallySortedWilsonWeight
          theory traceData exponential beta))

  ----------------------------------------------------------------------
  -- P0.E SAME-OBJECT PHYSICAL PARTITION ENDPOINT.
  --
  -- The existing original canonical 1024-bond sorter already proves
  -- originalFinePhysicalPartitionEqualsNestedF19, and the source F19
  -- arbitrary-weight Haar theorem already proves general 64-pair
  -- disintegration. Their direct composition gives the TRUE original
  -- fine Wilson partition as one coarse Haar integral of the
  -- constructed full physical effective density.
  --
  -- No additional positive-mass assumption, redefined Wilson action,
  -- factorized Gibbs weight, real division or independent coarse
  -- measure occurs. All existing sources still require local Agda
  -- acceptance; this is NOT a UV residual/continuum mass-gap proof.
  ----------------------------------------------------------------------

  originalFullInteractingEffectiveDensity : Vec.Vec Link 64 → ℝ
  originalFullInteractingEffectiveDensity =
    Fibre.originalAllPairsEffectiveDensity
      theory source bilateral
      (λ pairs →
        Haar.productIntegral source
          (λ spectators →
            Original.physicallySortedWilsonWeight
              theory traceData exponential beta
              (F19Physical.originalPairsAndSpectators
                pairs spectators)))

  -- This is a source-written direct producer of the missing
  -- canonical-fine-to-actual-effective PARTITION identity.
  -- It reuses M.01/M.02 and F18/F19 instead of introducing a new
  -- finite permutation or an assumed density-transport record.
  originalFinePhysicalPartitionEqualsActualEffectivePartition :
    Haar.productIntegral source
      (Original.originalWilsonVectorWeight
        theory traceData exponential beta)
    ≡ Haar.productIntegral source
        originalFullInteractingEffectiveDensity
  originalFinePhysicalPartitionEqualsActualEffectivePartition =
    let
      originalNestedFineWeight =
        λ pairs →
          Haar.productIntegral source
            (λ spectators →
              Original.physicallySortedWilsonWeight
                theory traceData exponential beta
                (F19Physical.originalPairsAndSpectators
                  pairs spectators))
    in
    trans
      originalFinePhysicalPartitionEqualsNestedF19
      (trans
        (Fibre.originalAllPairsGeneralWeightedChange
          theory source bilateral originalNestedFineWeight)
        (Fibre.originalInterleavedIntegralIsCoarseFibre
          theory source bilateral originalNestedFineWeight))
