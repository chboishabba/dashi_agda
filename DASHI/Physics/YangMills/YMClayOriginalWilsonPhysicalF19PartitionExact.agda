module DASHI.Physics.YangMills.YMClayOriginalWilsonPhysicalF19PartitionExact where

-- YM M.02: SAME original 1024-link Wilson Gibbs partition, reindexed
-- to the physical ordered F19 64-pair/896-spectator fine integral.
-- Reuses original-weight inverse permutation and general flat/nested
-- original product-Haar theorem; arbitrary coupled spectators remain.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; subst)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; -ℝ_; _+ℝ_; _*ℝ_; _<ℝ_;
   mulZeroˡ; mulOneʳ; +-identityʳ)
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
import DASHI.Physics.YangMills.YMClaySUNOriginal64Pair896MarkedEffectiveSourceExact as Marked

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

  ----------------------------------------------------------------------
  -- P0.E SAME ORIGINAL CANONICAL FINE PARTITION IS THE PHYSICAL
  -- TWO-MARKED NORMALIZER. No second measure or independent Z oracle.
  --
  -- The F19 original physically sorted Wilson fine weight was
  -- ALREADY supplied by F19Physical.physicalWeight, and the full
  -- 2-source identity by actualF19WilsonTwoMarkTheorem. This pays the
  -- exact zero-source literal Z_aff(0,0) identification with the
  -- UNSORTED original 1024-link Wilson partition, including all
  -- coupled spectators and native M.01/M.02 Haar reordering.
  --
  -- This is still for original coarse block TEST FUNCTIONS. The
  -- physical Wilson-loop word -> actual native block observable
  -- identification is a separate source-specific uninhabited weld.
  ----------------------------------------------------------------------

  module OriginalPhysicalF19TwoMarked
      (linear : Ordered.OneLinkOrderedHaarAlgebra source) where

    CoarseTest : Set
    CoarseTest =
      Marked.OriginalCoarseTest theory source bilateral linear

    originalPhysicalF19Weight :
      Marked.OriginalFineWeight theory source bilateral linear
    originalPhysicalF19Weight =
      F19Physical.physicalWeight
        theory traceData exponential beta source bilateral linear

    originalPhysicalTwoMarkedAtZeroIsOne :
      (left right : CoarseTest) (coarse : Vec.Vec Link 64) →
      Marked.actualTwoMarkedCoarseTest
        theory source bilateral linear
        left right 0ℝ 0ℝ coarse
      ≡ 1ℝ
    originalPhysicalTwoMarkedAtZeroIsOne left right coarse =
      trans
        (cong₂ _*ℝ_
          (trans
            (cong (λ v → 1ℝ +ℝ v) (mulZeroˡ (left coarse)))
            (+-identityʳ 1ℝ))
          (trans
            (cong (λ v → 1ℝ +ℝ v) (mulZeroˡ (right coarse)))
            (+-identityʳ 1ℝ)))
        (mulOneʳ 1ℝ)

    -- The actual F19 source selected effective density is
    -- DEFINITIONALLY the originalFullInteractingEffectiveDensity
    -- already constructed above: same original Wilson weight,
    -- same spectator integrals and same 64 fibre measures.
    originalPhysicalF19EffectiveMarkedZeroIsPartition :
      (left right : CoarseTest) →
      Marked.actualEffectiveTwoMarkedNumerator
        theory source bilateral linear
        originalPhysicalF19Weight left right 0ℝ 0ℝ
      ≡ Haar.productIntegral source
          originalFullInteractingEffectiveDensity
    originalPhysicalF19EffectiveMarkedZeroIsPartition left right =
      Original.productIntegralCongruent source
        (λ coarse →
          originalFullInteractingEffectiveDensity coarse *ℝ
          Marked.actualTwoMarkedCoarseTest
            theory source bilateral linear
            left right 0ℝ 0ℝ coarse)
        originalFullInteractingEffectiveDensity
        (λ coarse →
          trans
            (cong
              (λ marked →
                originalFullInteractingEffectiveDensity coarse *ℝ marked)
              (originalPhysicalTwoMarkedAtZeroIsOne left right coarse))
            (mulOneʳ (originalFullInteractingEffectiveDensity coarse)))

    -- True ORIGINAL fine Wilson Z, rather than independently selected
    -- Z_aff(0,0), normalizes the full F19 two-source polynomial.
    originalPhysicalF19FineMarkedZeroIsCanonicalPartition :
      (left right : CoarseTest) →
      Marked.actualOriginalFineTwoMarkedNumerator
        theory source bilateral linear
        originalPhysicalF19Weight left right 0ℝ 0ℝ
      ≡ Haar.productIntegral source
          (Original.originalWilsonVectorWeight
            theory traceData exponential beta)
    originalPhysicalF19FineMarkedZeroIsCanonicalPartition
        left right =
      trans
        (F19Physical.actualF19WilsonTwoMarkTheorem
          theory traceData exponential beta
          source bilateral linear left right 0ℝ 0ℝ)
        (trans
          (originalPhysicalF19EffectiveMarkedZeroIsPartition
            left right)
          (sym originalFinePhysicalPartitionEqualsActualEffectivePartition))

    -- Source-native denominator positivity from the SAME exponential/
    -- strict Haar requirements, not a new "Z_aff > 0" postulate.
    originalPhysicalF19FineMarkedNormalizerStrictlyPositive :
      (strict : Ordered.OneLinkStrictlyPositiveIntegration source) →
      (left right : CoarseTest) →
      0ℝ <ℝ
        Marked.actualOriginalFineTwoMarkedNumerator
          theory source bilateral linear
          originalPhysicalF19Weight left right 0ℝ 0ℝ
    originalPhysicalF19FineMarkedNormalizerStrictlyPositive
        strict left right =
      subst (λ z → 0ℝ <ℝ z)
        (sym
          (originalPhysicalF19FineMarkedZeroIsCanonicalPartition
            left right))
        (originalCanonicalFineWilsonPartitionStrictlyPositiveFromF19
          strict)

    -- Full physical finite F19 marked numerator and SAME original
    -- canonical Z on both sides. This proves no RG rate: the coarse
    -- effective and distinct bare-coarse Wilson Gibbs laws generally
    -- differ, and P0.F remains a genuine UV/IR-uniform estimate.
    originalPhysicalF19TwoMarksNormalizeByCanonicalPartition :
      (divide : ℝ → ℝ → ℝ)
      (left right : CoarseTest) (s t : ℝ) →
      divide
        (Marked.actualOriginalFineTwoMarkedNumerator
          theory source bilateral linear
          originalPhysicalF19Weight left right s t)
        (Haar.productIntegral source
          (Original.originalWilsonVectorWeight
            theory traceData exponential beta))
      ≡
      divide
        (Marked.actualEffectiveTwoMarkedNumerator
          theory source bilateral linear
          originalPhysicalF19Weight left right s t)
        (Haar.productIntegral source
          (Original.originalWilsonVectorWeight
            theory traceData exponential beta))
    originalPhysicalF19TwoMarksNormalizeByCanonicalPartition
        divide left right s t =
      cong (λ numerator →
        divide numerator
          (Haar.productIntegral source
            (Original.originalWilsonVectorWeight
              theory traceData exponential beta)))
        (F19Physical.actualF19WilsonTwoMarkTheorem
          theory traceData exponential beta
          source bilateral linear left right s t)
