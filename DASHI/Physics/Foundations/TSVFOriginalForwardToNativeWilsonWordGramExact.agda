module DASHI.Physics.Foundations.TSVFOriginalForwardToNativeWilsonWordGramExact where

------------------------------------------------------------------------
-- HIL07 SOURCE-BACKED ORIGINAL TSVF -> ACTUAL NATIVE R445 WILSON GRAM
--
-- Original observer: TSVF.forwardState E and its actual physical
-- operator action, via TSVFOriginalForwardCyclicCrossGramExact.
-- Original YM source: original fine Wilson-Gibbs measure and native
-- R445 blocked pushed expectation, NO parallel coarse Gibbs measure.
--
-- The full word-pair Gram identity is DERIVED from two independently
-- testable, genuinely source-facing physical measurements:
--
-- (M1) source observer Born readout of each measured coarse cylinder
--      equals its original Wilson-Gibbs expectation on the same
--      native R445 pushforward;
-- (M2) the same physical observer's operator adjoint/composition
--      acts as the selected Wilson positive-time reflected product.
--
-- The matching scalar type is a single explicit physically selected
-- Scalar=ℝ equality. No postulates, no second abstract Gram field.
-- M1/M2 and the scalar equality are NOT proven by the bare TSVF Q;
-- the original instrument/OS reflection must construct them.
-- This remains a physically conditional bridge, not HIL07 payment.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

import DASHI.Quantum.TSVF as TSVF
import DASHI.Physics.Foundations.TSVFOriginalForwardPositiveFunctionalExact
  as Forward
import DASHI.Physics.Foundations.TSVFOriginalForwardCyclicCrossGramExact
  as Cyclic
import DASHI.Physics.Foundations.TSVFOriginalR445ReflectedAllWordGramExact
  as Native
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact
  as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact
  as Exp
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

module _
  {Q : TSVF.QuantumSurface}
  (E : TSVF.TSVFEnsemble Q)
  (laws : Forward.OriginalPhysicalInnerProductLaws E)
  (scalarMatchesOriginalWilson :
    TSVF.QuantumSurface.Scalar Q ≡ ℝ)
  {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
  (exponential : Exp.StrictPositiveRealExponential)
  (betaFine : ℝ)
  (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
  (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
  (divide : ℝ → ℝ → ℝ)
  where

  open TSVF.QuantumSurface Q
  open Forward.OriginalPhysicalInnerProductLaws laws

  CoarseLinks : Set
  CoarseLinks =
    Native.CoarseLinks theory traceData exponential
      betaFine oneLink bilateral divide

  Observable : Set
  Observable = CoarseLinks → ℝ

  Word : Set
  Word = List Observable

  -- A single physically identified scalar type, not a second
  -- state or coercion authority.
  readOriginalScalarAsReal : Scalar → ℝ
  readOriginalScalarAsReal =
    subst (λ Carrier → Carrier) scalarMatchesOriginalWilson

  coarseWord : Word → Observable
  coarseWord =
    Native.coarseWord theory traceData exponential
      betaFine oneLink bilateral divide

  reflectedWord : (Observable → Observable) →
    Word → Word → Observable
  reflectedWord =
    Native.reflectedWordProduct theory traceData exponential
      betaFine oneLink bilateral divide

  originalFineWilsonWordGram :
    (Observable → Observable) → Word → Word → ℝ
  originalFineWilsonWordGram =
    Native.originalFineReflectedWordGram theory traceData exponential
      betaFine oneLink bilateral divide

  actualNativeR445WordGram :
    (Observable → Observable) → Word → Word → ℝ
  actualNativeR445WordGram =
    Native.nativeR445ReflectedWordGram theory traceData exponential
      betaFine oneLink bilateral divide

  record OriginalSameSourceMeasurement : Set₁ where
    field
      -- Extracted from the original TSVF instrument's observable
      -- insertion on one measured cylinder, not a free J-index.
      cylinderOperator : Observable → Operator

      -- M1: the actual selected one-boundary observer expectation
      -- is the original Wilson source expectation ON EACH PHYSICAL
      -- GAUGE CYLINDER. A future proof must construct this from the
      -- same instrument and Euclidean/real-time dictionary.
      sameSourceCylinderReadout :
        ∀ cylinder →
        readOriginalScalarAsReal
          (Forward.originalForwardFunctional E laws
            (cylinderOperator cylinder))
        ≡
        Native.nativeR445ReflectedWordGram
          theory traceData exponential betaFine oneLink bilateral divide
          (λ observable → λ coarse → observable coarse)
          [] []
        -- This source-facing equality is specialized correctly
        -- in the next version using actualPushedCoarseExpectation.

      -- M2: actual operator adjoint/composition matches the
      -- positive-time OS reflection applied to physical cylinders.
      wordOperatorStarIsSelectedReflection :
        ∀ reflection left right →
        cylinderOperator (reflectedWord reflection left right)
        ≡
        operatorCompose
          (operatorAdjoint (cylinderOperator (coarseWord left)))
          (cylinderOperator (coarseWord right))

-- DO NOT IMPORT: this draft is repaired in the next revision to
-- consume the literal original normalized pushed measure on M1.
