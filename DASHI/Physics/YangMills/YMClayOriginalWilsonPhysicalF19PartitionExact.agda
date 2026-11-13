module DASHI.Physics.YangMills.YMClayOriginalWilsonPhysicalF19PartitionExact where

-- YM M.02: SAME original 1024-link Wilson Gibbs partition, reindexed
-- to the physical ordered F19 64-pair/896-spectator fine integral.
-- Reuses original-weight inverse permutation and general flat/nested
-- original product-Haar theorem; arbitrary coupled spectators remain.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (sym; trans; subst)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; -ℝ_; _<ℝ_)
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNWeightedDisjointPairFibreReparamExact as Fibre
import DASHI.Physics.YangMills.YMClayNative1024WeightedWilsonReindexExact as Original
import DASHI.Physics.YangMills.YMClayNativePairsSpectatorsFubiniExact as Flat
import DASHI.Physics.YangMills.YMClayOriginalWilsonF19ConcreteWeightExact as F19Physical
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Wilson
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered

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

  ----------------------------------------------------------------------
  -- P0.E: EXACT ORIGINAL PHYSICAL POSITIVE-EFFECTIVE-MEASURE WELD.
  --
  -- The *same* 1024-link interacting Wilson source, sorted by the
  -- actually constructed M.01/M.02 adjacent-swap program, is literally
  -- exp(-S_Wilson). Its strict positivity is an EXISTING property of
  -- Exp.StrictPositiveRealExponential, not an assumed positive
  -- blocked density. The original 896 spectators are still integrated.
  --
  -- The only physical Haar premise is the already explicit original
  -- OneLinkStrictlyPositiveIntegration on the actual SU(N) carrier.
  -- No auxiliary coarse density, bare-action substitution, new scalar
  -- postulate, trace bound, UV cutoff estimate or continuum limit.
  ----------------------------------------------------------------------

  originalSortedWilsonPhysicalWeightPointwisePositive :
    (pairs : Vec.Vec (Fibre.Pair theory source bilateral) 64)
    (spectators : Vec.Vec Link 896) →
    0ℝ <ℝ
      Original.physicallySortedWilsonWeight
        theory traceData exponential beta
        (F19Physical.originalPairsAndSpectators pairs spectators)
  originalSortedWilsonPhysicalWeightPointwisePositive
      pairs spectators =
    Exp.expPositive exponential
      (-ℝ Wilson.periodicSUNWilsonAction theory traceData 3 beta
        (Codec.decodeOriginalBonds 4
          (Haar.permuteLinks
            (Original.inverseProgram (Original.actualPairProgram theory))
            (F19Physical.originalPairsAndSpectators pairs spectators))))

  -- The ORIGINAL pointwise positive Wilson density remains strictly
  -- positive after integrating ALL 896 interacting spectator links.
  -- The finite Haar primitive must be instantiated on a legitimate
  -- physical test class; its strict property is explicit here.
  originalPhysical896SpectatorMarginalStrictlyPositive :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration source) →
    (pairs : Vec.Vec (Fibre.Pair theory source bilateral) 64) →
    0ℝ <ℝ
      Haar.productIntegral source
        (λ spectators →
          Original.physicallySortedWilsonWeight
            theory traceData exponential beta
            (F19Physical.originalPairsAndSpectators pairs spectators))
  originalPhysical896SpectatorMarginalStrictlyPositive strict pairs =
    Ordered.productIntegralStrictlyPositive source strict
      (λ spectators →
        Original.physicallySortedWilsonWeight
          theory traceData exponential beta
          (F19Physical.originalPairsAndSpectators pairs spectators))
      (originalSortedWilsonPhysicalWeightPointwisePositive pairs)

  -- This is the SAME effective density of
  -- originalFinePhysicalPartitionEqualsActualEffectivePartition.
  -- The actual 64 noncommutative pair fibres have also been integrated.
  originalFullInteractingEffectiveDensityStrictlyPositive :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration source) →
    ∀ coarse →
    0ℝ <ℝ originalFullInteractingEffectiveDensity coarse
  originalFullInteractingEffectiveDensityStrictlyPositive strict =
    Fibre.originalAllPairsFibreDensityStrictlyPositive
      theory source bilateral strict
      (λ pairs →
        Haar.productIntegral source
          (λ spectators →
            Original.physicallySortedWilsonWeight
              theory traceData exponential beta
              (F19Physical.originalPairsAndSpectators pairs spectators)))
      (originalPhysical896SpectatorMarginalStrictlyPositive strict)

  -- On this exact original finite SU(N) Gibbs source, the final
  -- constructed coarse effective partition is STRICTLY POSITIVE.
  -- No independently supplied "effective partition > 0" axiom.
  originalFullInteractingEffectivePartitionStrictlyPositive :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration source) →
    0ℝ <ℝ Haar.productIntegral source
      originalFullInteractingEffectiveDensity
  originalFullInteractingEffectivePartitionStrictlyPositive strict =
    Ordered.productIntegralStrictlyPositive source strict
      originalFullInteractingEffectiveDensity
      (originalFullInteractingEffectiveDensityStrictlyPositive strict)

  -- By SAME SOURCE canonical fine/coarse partition equality, the
  -- original UNSORTED 1024-link fine Gibbs partition is positive too.
  -- This is not a new coupling-constant estimate or RG contraction.
  originalCanonicalFineWilsonPartitionStrictlyPositiveFromF19 :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration source) →
    0ℝ <ℝ
      Haar.productIntegral source
        (Original.originalWilsonVectorWeight
          theory traceData exponential beta)
  originalCanonicalFineWilsonPartitionStrictlyPositiveFromF19 strict =
    subst (λ z → 0ℝ <ℝ z)
      (sym originalFinePhysicalPartitionEqualsActualEffectivePartition)
      (originalFullInteractingEffectivePartitionStrictlyPositive strict)
