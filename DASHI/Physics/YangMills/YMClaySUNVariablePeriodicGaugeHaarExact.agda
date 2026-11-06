{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGaugeHaarExact where

------------------------------------------------------------------------
-- R443/R445: VARIABLE PERIODIC GAUGE-INVARIANT PHYSICAL GIBBS CYLINDERS.
--
-- Every n uses the ORIGINAL SUN periodic four-torus and six-positive-plane
-- Gibbs measure from YMClaySUNVariablePeriodicProductHaarExact. Reuse the
-- existing one-link bilateral-Haar -> finite-product gauge theorem, and
-- the original variable-periodic Wilson gauge theorem.
--
-- Bond fields are FUNCTIONS. Gauge/vector naturality is therefore stated
-- pointwise, and only observables with the already-proved pointwise
-- congruence law are transported. No global function extensionality and
-- no independent full-lattice measure-invariance hypothesis is used.
--
-- OPEN: physical native bond/Vec decoder and gauge-coordinate naturality,
-- actual measurable one-link SU(N) Haar and Bishop/legacy real alignment,
-- cutoff refinement, CMP119, R445 uniform estimates, CMP116, OS gap.
-- Original Wilson/Balaban/Haar sources and in-repo proof owners retained.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicBondPointwiseExact as Pointwise
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicProductHaarExact as VariableHaar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarC3Exact as Congruence
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
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
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (decode :
      Vec (SUN.SUNMatrixElement theory) linkCount →
      Variable.SUNPeriodicLinks theory n)
    (divide : ℝ → ℝ → ℝ)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  Gamma : Set
  Gamma = Variable.SUNPeriodicGauge theory n

  selectedMeasure :
    Physical.PhysicalFiniteYMMeasure
      (Variable.SUNPeriodicLinks theory n) ℝ
  selectedMeasure =
    VariableHaar.periodicProductFiniteMeasure
      theory traceData exponential n beta oneLink decode divide

  record OriginalPeriodicGaugeVectorNaturality : Set₁ where
    field
      leftFactors rightFactors : Gamma → Vec Link linkCount

      -- Original positive-bond function equals its vector representation
      -- bond by bond, NOT by unrestricted whole-function equality.
      gaugeDecodeAt : ∀ gamma vector bond →
        Variable.periodicSUNGaugeTransform theory n
          (decode vector) gamma bond
        ≡
        decode
          (Bilateral.gaugeBondVector theory oneLink bilateral
            (leftFactors gamma) (rightFactors gamma) vector)
          bond

  open OriginalPeriodicGaugeVectorNaturality public

  record PeriodicPointwiseObservable
      (observable : Variable.SUNPeriodicLinks theory n → ℝ) : Set where
    field
      congruentAt : ∀ left right →
        Pointwise.VariableBondPointwise theory n left right →
        observable left ≡ observable right

  open PeriodicPointwiseObservable public

  periodicProductGaugeHaarInvariant :
    (weld : OriginalPeriodicGaugeVectorNaturality)
    (observable : Variable.SUNPeriodicLinks theory n → ℝ)
    (extensional : PeriodicPointwiseObservable observable)
    (gamma : Gamma) →
    Physical.haarIntegral selectedMeasure
      (λ links →
        observable (Variable.periodicSUNGaugeTransform
          theory n links gamma))
    ≡ Physical.haarIntegral selectedMeasure observable
  periodicProductGaugeHaarInvariant weld observable extensional gamma =
    trans
      (Congruence.productIntegralCongruent oneLink _ _
        (λ vector →
          congruentAt extensional
            (Variable.periodicSUNGaugeTransform theory n
              (decode vector) gamma)
            (decode
              (Bilateral.gaugeBondVector theory oneLink bilateral
                (leftFactors weld gamma) (rightFactors weld gamma)
                vector))
            (gaugeDecodeAt weld gamma vector)))
      (Bilateral.productHaarNativeGaugeInvariant
        theory oneLink bilateral
        (leftFactors weld gamma) (rightFactors weld gamma)
        (λ vector → observable (decode vector)))

  periodicGibbsPointwise :
    PeriodicPointwiseObservable
      (Variable.periodicSUNGibbsDensity
        theory traceData exponential n beta)
  periodicGibbsPointwise =
    record
      { congruentAt =
          Pointwise.variableGibbsDensityPointwise
            theory traceData exponential n beta
      }

  periodicWeightedPointwise :
    (observable : Variable.SUNPeriodicLinks theory n → ℝ)
    (extensional : PeriodicPointwiseObservable observable) →
    PeriodicPointwiseObservable
      (λ links →
        Variable.periodicSUNGibbsDensity
          theory traceData exponential n beta links
        *ℝ observable links)
  periodicWeightedPointwise observable extensional =
    record
      { congruentAt = λ left right same →
          cong₂ _*ℝ_
            (congruentAt periodicGibbsPointwise left right same)
            (congruentAt extensional left right same)
      }

  -- Exact original same-Gibbs unnormalized numerator for every n.
  -- The first step replaces density(U) by density(gamma·U) using the
  -- EXISTING full native Wilson gauge theorem, then translates vectors.
  periodicGaugeNumeratorInvariant :
    (weld : OriginalPeriodicGaugeVectorNaturality)
    (observable : Variable.SUNPeriodicLinks theory n → ℝ)
    (extensional : PeriodicPointwiseObservable observable)
    (gamma : Gamma) →
    Finite.unnormalizedNumerator selectedMeasure
      (λ links →
        observable (Variable.periodicSUNGaugeTransform
          theory n links gamma))
    ≡ Finite.unnormalizedNumerator selectedMeasure observable
  periodicGaugeNumeratorInvariant weld observable extensional gamma =
    trans
      (Congruence.productIntegralCongruent oneLink _ _
        (λ vector →
          cong
            (λ densityValue →
              densityValue *ℝ
                observable (Variable.periodicSUNGaugeTransform
                  theory n (decode vector) gamma))
            (sym
              (Variable.periodicSUNGibbsDensityGaugeInvariant
                theory traceData exponential n beta
                (decode vector) gamma))))
      (periodicProductGaugeHaarInvariant weld
        (λ links →
          Variable.periodicSUNGibbsDensity
            theory traceData exponential n beta links
          *ℝ observable links)
        (periodicWeightedPointwise observable extensional)
        gamma)

  periodicGaugeNormalizedExpectationInvariant :
    (weld : OriginalPeriodicGaugeVectorNaturality)
    (observable : Variable.SUNPeriodicLinks theory n → ℝ)
    (extensional : PeriodicPointwiseObservable observable)
    (gamma : Gamma) →
    Physical.normalizedExpectation selectedMeasure
      (λ links →
        observable (Variable.periodicSUNGaugeTransform
          theory n links gamma))
    ≡ Physical.normalizedExpectation selectedMeasure observable
  periodicGaugeNormalizedExpectationInvariant weld observable extensional gamma =
    cong
      (λ numerator →
        divide numerator (Physical.partitionFunction selectedMeasure))
      (periodicGaugeNumeratorInvariant weld observable extensional gamma)
