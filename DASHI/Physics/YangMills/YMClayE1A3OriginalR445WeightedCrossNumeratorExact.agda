module DASHI.Physics.YangMills.YMClayE1A3OriginalR445WeightedCrossNumeratorExact where

------------------------------------------------------------------------
-- P0 E1/A3 ORIGINAL WILSON weighted cross numerator.
--
-- The physical all-test RG mismatch has two real measures:
--   fine Wilson side four (cutoff 3), then native SU(N) two-link block;
--   independent bare coarse Wilson side two (cutoff 1).
--
-- Their true unnormalized source integrals and their true partitions
-- define a division-free cross numerator.
--
-- This module proves its exact full-weight expansion and unit
-- cancellation from existing original source Haar integration laws.
-- It does NOT claim that nonconstant insertions have zero RG error,
-- or divide by an unsourced partition.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; trans; sym)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; 1ℝ; _*ℝ_; _-ℝ_; _<ℝ_; _≤ℝ_;
         *-comm; subSelf)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact as Push
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact as Original
import DASHI.Physics.YangMills.YMClayE1A3OriginalR445CrossCutoffSourceExact as Cross
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  CoarseTest : Set
  CoarseTest =
    Cross.CoarseTest
      theory traceData exponential beta oneLink bilateral divide

  finePartition : ℝ
  finePartition =
    Physical.partitionFunction
      (Original.originalWilsonMeasure
        theory traceData exponential beta oneLink bilateral divide 3)

  bareCoarsePartition : ℝ
  bareCoarsePartition =
    Physical.partitionFunction
      (Original.originalWilsonMeasure
        theory traceData exponential beta oneLink bilateral divide 1)

  -- The original full side-four interacting Gibbs integral with the
  -- ACTUAL ordered two-link nonabelian SU(N) block.
  fineBlockedNumerator : CoarseTest → ℝ
  fineBlockedNumerator =
    Push.actualPushforwardNumerator
      theory traceData exponential (beta 3) oneLink bilateral divide

  -- The original distinct side-two beta(1) Wilson bare Gibbs integral.
  bareCoarseNumerator : CoarseTest → ℝ
  bareCoarseNumerator test =
    Finite.unnormalizedNumerator
      (Original.originalWilsonMeasure
        theory traceData exponential beta oneLink bilateral divide 1)
      test

  originalWilsonR445CrossNumerator : CoarseTest → ℝ
  originalWilsonR445CrossNumerator test =
    (fineBlockedNumerator test *ℝ bareCoarsePartition)
    -ℝ (bareCoarseNumerator test *ℝ finePartition)

  -- This equality is on the SAME originally pinned finite measures.
  -- It expands the entire interacting Wilson weight, preserving the
  -- original Haar integral, native block and beta choices.
  originalWilsonR445CrossNumeratorIsWeightedSource :
    (test : CoarseTest) →
    originalWilsonR445CrossNumerator test
    ≡
      (Physical.haarIntegral
        (Original.originalWilsonMeasure
          theory traceData exponential beta oneLink bilateral divide 3)
        (λ fine →
          Physical.density
            (Original.originalWilsonMeasure
              theory traceData exponential beta oneLink bilateral divide 3)
            fine
          *ℝ test
            (Push.actualBlockedLinkMap
              theory traceData exponential (beta 3)
              oneLink bilateral divide fine))
        *ℝ bareCoarsePartition)
      -ℝ
      (Physical.haarIntegral
        (Original.originalWilsonMeasure
          theory traceData exponential beta oneLink bilateral divide 1)
        (λ coarse →
          Physical.density
            (Original.originalWilsonMeasure
              theory traceData exponential beta oneLink bilateral divide 1)
            coarse
          *ℝ test coarse)
        *ℝ finePartition)
  originalWilsonR445CrossNumeratorIsWeightedSource test = refl

  -- Unitary source cancellation at the same REAL original fine/bare
  -- partitions, NOT an abstract probability normalization assertion.
  originalWilsonR445UnitCrossNumeratorZero :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} →
      0ℝ <ℝ value →
      0ℝ ≤ℝ value) →
    originalWilsonR445CrossNumerator (λ _ → 1ℝ)
      ≡ 0ℝ
  originalWilsonR445UnitCrossNumeratorZero ordered strictToWeak =
    trans
      (cong₂ (λ left right →
         (left *ℝ bareCoarsePartition)
           -ℝ (right *ℝ finePartition))
        (Push.actualPushforwardNumeratorOne
          theory traceData exponential (beta 3)
          oneLink bilateral divide ordered strictToWeak)
        (Original.originalWilsonUnitNumeratorIsPartition
          theory traceData exponential beta oneLink bilateral divide
          ordered strictToWeak 1))
      (trans
        (cong
          (λ x → (finePartition *ℝ bareCoarsePartition) -ℝ x)
          (*-comm bareCoarsePartition finePartition))
        (subSelf (finePartition *ℝ bareCoarsePartition)))
