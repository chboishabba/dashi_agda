{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClaySUNVariablePeriodicProductHaarExact where

------------------------------------------------------------------------
-- R443 -> R445: ALL FINITE PERIODIC 4D CUT-OFFS, ONE-LINK PRODUCT HAAR.
--
-- At each actual periodic side (suc n), use the ORIGINAL SU(N) periodic
-- positive-bond field and literal six-positive-plane Wilson action.
-- Replace the previous arbitrary per-n full-field integration functional
-- with the already-proved inductive finite product of ONE selected
-- one-link functional. Derive its normalization, positivity, finite
-- integration algebra and strict Gibbs partition positivity for every n.
--
-- The vector decoder is deliberately visible. Its construction, the
-- correct number/order of native bonds, actual compact Borel Haar on a
-- measurable test algebra and changing-cutoff estimates remain OPEN.
-- This finite statement implies neither UV/IR convergence nor a Clay gap.
--
-- Original mathematics: Wilson (1974); Bałaban (1985); compact-group
-- Haar/Fubini. Existing DASHI product-Haar and periodic-action theorem
-- owners are reused, not redefined.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec.Base using (Vec)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; -ℝ_; _≤ℝ_; _<ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarC3Exact as Congruence
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite

module _
    {Matrix Complex : Set} {N linkCount : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (n : Nat) (beta : ℝ)
    (oneLink : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (decode :
      Vec (SUN.SUNMatrixElement theory) linkCount →
      Variable.SUNPeriodicLinks theory n)
    (divide : ℝ → ℝ → ℝ)
  where

  -- The per-cutoff integral is no longer an arbitrary independent input.
  -- This is the original link carrier, reached through a visible decoder.
  periodicProductHaar :
    (Variable.SUNPeriodicLinks theory n → ℝ) → ℝ
  periodicProductHaar observable =
    Product.productIntegral oneLink (λ links → observable (decode links))

  periodicProductFiniteMeasure :
    Physical.PhysicalFiniteYMMeasure
      (Variable.SUNPeriodicLinks theory n) ℝ
  periodicProductFiniteMeasure =
    Variable.periodicSUNFiniteGibbsMeasure
      theory traceData exponential n beta periodicProductHaar divide

  -- Product normalization follows from one-link normalization at any
  -- finite linkCount, not from another all-link Haar axiom.
  periodicProductHaarUnit :
    periodicProductHaar (λ _ → 1ℝ) ≡ 1ℝ
  periodicProductHaarUnit =
    Product.productIntegralUnit oneLink

  -- Strict pointwise positivity uses the same native variable-n action.
  periodicActualDensityStrictPositive :
    ∀ links →
    0ℝ <ℝ Variable.periodicSUNGibbsDensity
      theory traceData exponential n beta links
  periodicActualDensityStrictPositive links =
    Exp.expPositive exponential
      (-ℝ Variable.periodicSUNWilsonAction
        theory traceData n beta links)

  -- A positive one-link integral on the selected test class implies
  -- that the *same* finite Wilson-Gibbs partition is strictly positive.
  -- There is no independent partition-nonzero assumption here.
  periodicProductPartitionStrictPositive :
    Ordered.OneLinkStrictlyPositiveIntegration oneLink →
    0ℝ <ℝ Physical.partitionFunction periodicProductFiniteMeasure
  periodicProductPartitionStrictPositive strict =
    Ordered.productIntegralStrictlyPositive oneLink strict
      (λ links →
        Variable.periodicSUNGibbsDensity
          theory traceData exponential n beta (decode links))
      (λ links → periodicActualDensityStrictPositive (decode links))

  -- Every finite cylinder integration law is inherited from the SAME
  -- one-link source by induction. The scalar strict-to-weak step is
  -- explicit because the current legacy RealAnalysisAxioms facade does
  -- not contain that order theorem.
  periodicProductIntegrationLaws :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value) →
    Finite.PhysicalFiniteMeasureIntegrationLaws
      periodicProductFiniteMeasure
  periodicProductIntegrationLaws ordered strictToWeak = record
    { Finite.PhysicalFiniteMeasureIntegrationLaws.densityNonnegative =
        λ links → strictToWeak (periodicActualDensityStrictPositive links)
    ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralCongruent =
        λ left right equality →
          Congruence.productIntegralCongruent oneLink
            (λ vector → left (decode vector))
            (λ vector → right (decode vector))
            (λ vector → equality (decode vector))
    ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralZero =
        Ordered.productIntegralZero oneLink ordered
    ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralAdd =
        λ left right →
          Ordered.productIntegralAdd oneLink ordered
            (λ vector → left (decode vector))
            (λ vector → right (decode vector))
    ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralScale =
        λ scalar observable →
          Ordered.productIntegralScale oneLink ordered scalar
            (λ vector → observable (decode vector))
    ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralPositive =
        λ observable pointwise →
          Ordered.productIntegralPositive oneLink ordered
            (λ vector → observable (decode vector))
            (λ vector → pointwise (decode vector))
    ; Finite.PhysicalFiniteMeasureIntegrationLaws.partitionFunctionIsDensityIntegral =
        refl
    }

  periodicProductDensitySameObject :
    ∀ links →
    Physical.density periodicProductFiniteMeasure links
    ≡ Variable.periodicSUNGibbsDensity
        theory traceData exponential n beta links
  periodicProductDensitySameObject links = refl

  periodicProductPartitionSameObject :
    Physical.partitionFunction periodicProductFiniteMeasure
    ≡ periodicProductHaar
        (Variable.periodicSUNGibbsDensity
          theory traceData exponential n beta)
  periodicProductPartitionSameObject = refl
