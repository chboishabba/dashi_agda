module DASHI.Physics.YangMills.YMClayOriginalWilsonC3WeightedHaarTransferExact where

------------------------------------------------------------------------
-- R443: REAL SELECTED ORIGINAL WILSON--GIBBS C3 WEIGHTED TRANSFER.
--
-- Finitely many original native SU(N) side-four link coordinates.
-- The weight below is DEFINITIONALLY the ORIGINAL six-plane
-- Variable.periodicSUNGibbsDensity on the ORIGINAL
-- Codec.decodeOriginalBonds 4, not a new arbitrary coarse model.
--
-- There are TWO independent, visible exact physical prerequisites:
--   (1) the existing R443 ONE closed canonical-label equality;
--   (2) invariance of the ACTUAL selected original Wilson--Gibbs
--       density under the original C3.forwardVector action.
--
-- Given both, the prior original product-Haar permutation theorem
-- derives the *WEIGHTED* C3 expectation symmetry on arbitrary real
-- cylinder functions. It is not inferred from unweighted Haar alone.
--
-- This is the correct source-native non-promotion firewall:
-- an arbitrary link-permutation preserves product Haar but generally
-- NOT a Wilson--Gibbs probability with a non-invariant action.
--
-- Still OPEN: kernel check of C3 closed equality, actual proof of
-- this physical action invariance for CMP119 E/R/B/V terms, genuine
-- continuous Borel SU(N) one-link Haar/integrability and all
-- continuum, CMP116, OS, Clay results.
--
-- Source provenance: Wilson, Balaban; original DASHI native
-- Variable/Gibbs/Codec/Product and C3 owners. No new axioms or holes.
-- SOURCE WRITTEN; Agda kernel / inherited real-analysis trust PENDING.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 1ℝ; _*ℝ_; mulOneʳ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayNativeSideFourC3VectorWeldExact as C3
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Single
import DASHI.Physics.YangMills.YMClayNativeC3AdjacentSortProgramExact as Sort
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarC3Exact as Congruence
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClaySUNConstructedPeriodicGaugeCodecExact as Constructed
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Cyl
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (divide : ℝ → ℝ → ℝ)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  OriginalFineVec : Set
  OriginalFineVec = Vec.Vec Link Single.Count

  actualOriginalFineWilsonDensity :
    OriginalFineVec → ℝ
  actualOriginalFineWilsonDensity links =
    Variable.periodicSUNGibbsDensity
      theory traceData exponential 3 betaFine
      (Codec.decodeOriginalBonds Torus.four links)

  actualOriginalFineNumerator :
    (OriginalFineVec → ℝ) → ℝ
  actualOriginalFineNumerator observable =
    Product.productIntegral oneLink
      (λ links →
        actualOriginalFineWilsonDensity links *ℝ observable links)

  actualOriginalFinePartition : ℝ
  actualOriginalFinePartition =
    actualOriginalFineNumerator (λ _ → 1ℝ)

  actualOriginalFineNormalized :
    (OriginalFineVec → ℝ) → ℝ
  actualOriginalFineNormalized observable =
    divide (actualOriginalFineNumerator observable)
           actualOriginalFinePartition

  -- Physically selected action covariance. This premise specifically
  -- names the ACTUAL original six-plane Gibbs action and its native C3,
  -- so it cannot be satisfied by checking an arbitrary other weight.
  ActualOriginalC3GibbsActionInvariant : Set
  ActualOriginalC3GibbsActionInvariant =
    ∀ links →
    actualOriginalFineWilsonDensity (C3.forwardVector links)
    ≡ actualOriginalFineWilsonDensity links

  -- The *closed* original canonical-label equality is not provided
  -- automatically by the native 46,592-swap reference program.
  actualOriginalWeightedC3NumeratorInvariant :
    Sort.constructedNativeC3CanonicalLabelGoal →
    ActualOriginalC3GibbsActionInvariant →
    ∀ observable →
    actualOriginalFineNumerator
      (λ links → observable (C3.forwardVector links))
    ≡ actualOriginalFineNumerator observable
  actualOriginalWeightedC3NumeratorInvariant
      closedC3 densityC3 observable =
    trans
      (Congruence.productIntegralCongruent oneLink _ _
        (λ links →
          trans
            (cong
              (λ weight →
                weight *ℝ observable (C3.forwardVector links))
              (sym (densityC3 links)))
            (cong
              (λ moved →
                actualOriginalFineWilsonDensity moved
                  *ℝ observable moved)
              (sym
                (Sort.constructedNativeC3AllVectors closedC3 links)))))
      (Product.productHaarPermutationInvariant
        oneLink Sort.constructedNativeC3Program
        (λ links →
          actualOriginalFineWilsonDensity links *ℝ observable links))

  -- No assumed coarse partition or extra division rule. Both
  -- normalized expectations share the ORIGINAL same scalar partition.
  actualOriginalWeightedC3NormalizedInvariant :
    Sort.constructedNativeC3CanonicalLabelGoal →
    ActualOriginalC3GibbsActionInvariant →
    ∀ observable →
    actualOriginalFineNormalized
      (λ links → observable (C3.forwardVector links))
    ≡ actualOriginalFineNormalized observable
  actualOriginalWeightedC3NormalizedInvariant closedC3 densityC3 observable =
    cong (λ numerator → divide numerator actualOriginalFinePartition)
      (actualOriginalWeightedC3NumeratorInvariant
        closedC3 densityC3 observable)

  ----------------------------------------------------------------------
  -- Exact same-selected-physical-measure interface, not a new Gibbs
  -- law. The original #1444 measure is Constructed.actualPeriodic-
  -- ProductMeasure theory traceData exponential n=3 ... with exactly
  -- Codec.decodeOriginalBonds (suc 3) = Codec.decodeOriginalBonds 4.
  ----------------------------------------------------------------------

  module _
      (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    where

    originalSelectedPhysicalMeasure :
      Physical.PhysicalFiniteYMMeasure
        (Variable.SUNPeriodicLinks theory 3) ℝ
    originalSelectedPhysicalMeasure =
      Constructed.actualPeriodicProductMeasure
        theory traceData exponential 3 betaFine
        oneLink bilateral divide

    -- A selected original physical Gibbs cylinder numerator literally
    -- equals the same original 1024-vector weighted numerator. No new
    -- density, source or cutoff index appears in this equality.
    selectedPhysicalNumeratorIsLiteralOriginalC3Vector :
      (observable : Variable.SUNPeriodicLinks theory 3 → ℝ) →
      Cyl.unnormalizedNumerator originalSelectedPhysicalMeasure observable
      ≡
      actualOriginalFineNumerator
        (λ links → observable (Codec.decodeOriginalBonds Torus.four links))
    selectedPhysicalNumeratorIsLiteralOriginalC3Vector observable = refl

    -- The actual selected physical partition lacks an explicit *1,
    -- whereas the original vector partition uses the numeral unit.
    -- The equality is obtained from ORIGINAL all-link congruence,
    -- rather than assuming a second partition authority.
    selectedPhysicalPartitionIsLiteralOriginalC3Vector :
      Physical.partitionFunction originalSelectedPhysicalMeasure
      ≡ actualOriginalFinePartition
    selectedPhysicalPartitionIsLiteralOriginalC3Vector =
      Congruence.productIntegralCongruent oneLink _ _
        (λ links →
          sym (mulOneʳ (actualOriginalFineWilsonDensity links)))

    selectedPhysicalNormalizedIsLiteralOriginalC3Vector :
      (observable : Variable.SUNPeriodicLinks theory 3 → ℝ) →
      Physical.normalizedExpectation
        originalSelectedPhysicalMeasure observable
      ≡ actualOriginalFineNormalized
        (λ links → observable (Codec.decodeOriginalBonds Torus.four links))
    selectedPhysicalNormalizedIsLiteralOriginalC3Vector observable =
      cong
        (λ partition →
          divide
            (actualOriginalFineNumerator
              (λ links →
                observable (Codec.decodeOriginalBonds Torus.four links)))
            partition)
        selectedPhysicalPartitionIsLiteralOriginalC3Vector

