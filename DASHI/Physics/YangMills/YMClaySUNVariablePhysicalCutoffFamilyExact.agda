module DASHI.Physics.YangMills.YMClaySUNVariablePhysicalCutoffFamilyExact where

------------------------------------------------------------------------
-- R443 -> R445: DEPENDENT PHYSICAL FAMILY ON THE ACTUAL CHANGING 4-TORUS.
--
-- This module deliberately does NOT use SUNOriginalWilsonFiniteFamily:
-- that older owner's cutoff parameter only changes beta at fixed side four.
-- Here every n has (n+1)^4 original sites and 4*(n+1)^4 positive links.
--
-- Reuses (i) the actual all-size six-positive-plane Wilson action,
-- (ii) the original-bond finite decoder from canonical enumeration,
-- (iii) a single chosen one-link Haar and its bilateral laws, and
-- (iv) the source-written all-size product measure and gauge proofs.
-- The same Haar functional is used at every finite cutoff; beta may vary.
--
-- Mathematical limits: no relation a(n), physical volume L(n), beta(a),
-- cross-cutoff coarsening, continuum tightness or OS mass gap is proved.
-- This is a finite *dependent family*, NOT a common infinite-volume
-- measure. RealAnalysisAxioms is an explicit postulated boundary, so this
-- interface is NOT declared golden --safe and has NO kernel receipt yet.
--
-- Credits: Wilson lattice action, Haar/Fubini, Balaban RG;
-- original DASHI source and finite-codec theorem owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _<ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicProductHaarExact as VariableHaar
import DASHI.Physics.YangMills.YMClaySUNConstructedPeriodicGaugeCodecExact as Constructed
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  finiteCutoffLinks : Nat → Nat
  finiteCutoffLinks n = Codec.originalPositiveBondCount (suc n)

  linksAt : Nat → Set
  linksAt n = Variable.SUNPeriodicLinks theory n

  gaugeAt : Nat → Set
  gaugeAt n = Variable.SUNPeriodicGauge theory n

  physicalFiniteCutoffMeasure :
    (n : Nat) → Physical.PhysicalFiniteYMMeasure (linksAt n) ℝ
  physicalFiniteCutoffMeasure n =
    Constructed.actualPeriodicProductMeasure
      theory traceData exponential n (beta n) oneLink bilateral divide

  -- The size count is tied to the original bond-list enumeration; it
  -- cannot be supplied as a floating external cardinality.
  finiteCutoffLinkCountFormula :
    ∀ n →
    finiteCutoffLinks n
    ≡ (((suc n * suc n) * (suc n * suc n)) * 4)
  finiteCutoffLinkCountFormula n =
    Codec.originalPositiveBondCountFormula (suc n)

  physicalFiniteDensitySameWilson :
    ∀ n links →
    Physical.density (physicalFiniteCutoffMeasure n) links
    ≡
    Variable.periodicSUNGibbsDensity
      theory traceData exponential n (beta n) links
  physicalFiniteDensitySameWilson n links = refl

  physicalFinitePartitionSameWilson :
    ∀ n →
    Physical.partitionFunction (physicalFiniteCutoffMeasure n)
    ≡
    VariableHaar.periodicProductHaar
      theory traceData exponential n (beta n)
      oneLink (Codec.decodeOriginalBonds (suc n)) divide
      (Variable.periodicSUNGibbsDensity
        theory traceData exponential n (beta n))
  physicalFinitePartitionSameWilson n = refl

  physicalFinitePartitionPositive :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink) →
    ∀ n →
    0ℝ <ℝ Physical.partitionFunction (physicalFiniteCutoffMeasure n)
  physicalFinitePartitionPositive strict n =
    Constructed.actualPeriodicPartitionPositive
      theory traceData exponential n (beta n)
      oneLink bilateral divide strict

  -- This is the literal ORIGINAL six-plane source, not an unrelated
  -- gauge-invariant observable selected from another finite model.
  physicalSixDeficitGaugeExpectation :
    ∀ n (gamma : gaugeAt n) →
    Physical.normalizedExpectation (physicalFiniteCutoffMeasure n)
      (λ links →
        Variable.periodicSUNSixDeficit theory traceData n
          (Variable.periodicSUNGaugeTransform theory n links gamma))
    ≡
    Physical.normalizedExpectation (physicalFiniteCutoffMeasure n)
      (Variable.periodicSUNSixDeficit theory traceData n)
  physicalSixDeficitGaugeExpectation n gamma =
    Constructed.actualSixDeficitGaugeNormalized
      theory traceData exponential n (beta n)
      oneLink bilateral divide gamma

  -- The original β(n) SU(N) Wilson action and its Gibbs density are the
  -- same physical finite source at each size, by definitional reduction.
  physicalWilsonActionAt : (n : Nat) → linksAt n → ℝ
  physicalWilsonActionAt n =
    Variable.periodicSUNWilsonAction theory traceData n (beta n)

  physicalWilsonActionGauge :
    ∀ n (links : linksAt n) (gamma : gaugeAt n) →
    physicalWilsonActionAt n
      (Variable.periodicSUNGaugeTransform theory n links gamma)
    ≡ physicalWilsonActionAt n links
  physicalWilsonActionGauge n links gamma =
    Variable.periodicSUNWilsonActionGaugeInvariant
      theory traceData n (beta n) links gamma
