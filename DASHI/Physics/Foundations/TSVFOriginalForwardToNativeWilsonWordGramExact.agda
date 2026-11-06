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
-- The observer Scalar can be complex. A physically calibrated real
-- readout is explicit, so no unjustified Scalar=ℝ equality is used.
-- M1/M2 and that readout are NOT proven by the bare TSVF Q;
-- the original instrument/OS reflection must construct them.
-- This remains a physically conditional bridge, not HIL07 payment.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
  using (cong; sym; trans)

import DASHI.Quantum.TSVF as TSVF
import DASHI.Physics.Foundations.TSVFOriginalForwardPositiveFunctionalExact
  as Forward
import DASHI.Physics.Foundations.TSVFOriginalForwardCyclicCrossGramExact
  as Cyclic
import DASHI.Physics.Foundations.TSVFOriginalR445ReflectedAllWordGramExact
  as Native
import DASHI.Physics.YangMills.YMClaySUNR445BlockedPushforwardR320CovarianceExact as R445
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact
  as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact
  as Exp
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)

module _
  {Q : TSVF.QuantumSurface}
  (E : TSVF.TSVFEnsemble Q)
  (laws : Forward.OriginalPhysicalInnerProductLaws E)
  (actualObserverRealReadout :
    TSVF.QuantumSurface.Scalar Q → ℝ)
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

  -- A complex physical observer supplies a calibrated real
  -- expectation readout of its scalar pairing. This is NOT an
  -- equality of the original complex scalar with Wilson ℝ.
  readOriginalScalarAsReal : Scalar → ℝ
  readOriginalScalarAsReal = actualObserverRealReadout

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

      -- ONE actual physical time-reflection on the selected
      -- gauge-invariant positive-time cylinder algebra. The previous
      -- forall-reflection M2b would force all distinct cylinder
      -- insertions to coincide by choosing arbitrary constant maps.
      selectedPhysicalReflection : Observable → Observable

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
        R445.actualPushedCoarseExpectation
          theory traceData exponential betaFine
          oneLink bilateral divide cylinder

      -- M2a: the actual physical cylinder insertion preserves
      -- pointwise multiplication and original operator composition.
      originalCylinderProductIsOperatorComposition :
        ∀ left right →
        cylinderOperator (λ coarse → left coarse *ℝ right coarse)
        ≡
        operatorCompose (cylinderOperator left)
          (cylinderOperator right)

      -- M2b: the physical selected reflection IS original adjoint
      -- on a single admissible cylinder, not an all-word Gram axiom.
      originalCylinderReflectionIsOperatorAdjoint :
        ∀ cylinder →
        cylinderOperator (selectedPhysicalReflection cylinder)
        ≡ operatorAdjoint (cylinderOperator cylinder)

  open OriginalSameSourceMeasurement public

  -- Every ordered word-pair star/reflection law now follows from
  -- two locally source-testable product and adjoint laws.
  originalAllWordReflectedProductIsObserverStar :
    (source : OriginalSameSourceMeasurement)
    (left right : Word) →
    cylinderOperator source
      (reflectedWord (selectedPhysicalReflection source) left right)
    ≡
    operatorCompose
      (operatorAdjoint (cylinderOperator source (coarseWord left)))
      (cylinderOperator source (coarseWord right))
  originalAllWordReflectedProductIsObserverStar
      source left right =
    trans
      (originalCylinderProductIsOperatorComposition source
        (selectedPhysicalReflection source (coarseWord left))
        (coarseWord right))
      (cong
        (λ op →
          operatorCompose op
            (cylinderOperator source (coarseWord right)))
        (originalCylinderReflectionIsOperatorAdjoint
          source (coarseWord left)))

  originalMeasuredObserverCrossWordGram :
    (source : OriginalSameSourceMeasurement)
    (left right : Word) → ℝ
  originalMeasuredObserverCrossWordGram
      source left right =
    readOriginalScalarAsReal
      (Cyclic.originalObserverCrossGram E laws
        (cylinderOperator source (coarseWord left))
        (cylinderOperator source (coarseWord right)))

  -- No all-pairs Gram matching is a field: it is derived from
  -- single-observable Born/Wilson equality M1 and the operational
  -- two source-local product and adjoint laws M2a/M2b, both on SAME selected source.
  originalMeasuredAllWordCrossGramEqualsNativeR445 :
    (source : OriginalSameSourceMeasurement)
    (reflection : Observable → Observable)
    (left right : Word) →
    originalMeasuredObserverCrossWordGram
      source left right
    ≡ actualNativeR445WordGram
      (selectedPhysicalReflection source) left right
  originalMeasuredAllWordCrossGramEqualsNativeR445
      source left right =
    trans
      (cong
        (λ op →
          readOriginalScalarAsReal
            (Forward.originalForwardFunctional E laws op))
        (sym
          (originalAllWordReflectedProductIsObserverStar
            source left right)))
      (sameSourceCylinderReadout source
        (reflectedWord (selectedPhysicalReflection source)
          left right))

  -- The actual original 1024-link fine Wilson-Gibbs measure is
  -- recovered too, by the SAME native block pushforward theorem.
  originalMeasuredAllWordCrossGramEqualsFineWilson :
    (source : OriginalSameSourceMeasurement)
    (reflection : Observable → Observable)
    (left right : Word) →
    originalMeasuredObserverCrossWordGram
      source left right
    ≡ originalFineWilsonWordGram
      (selectedPhysicalReflection source) left right
  originalMeasuredAllWordCrossGramEqualsFineWilson
      source reflection left right =
    trans
      (originalMeasuredAllWordCrossGramEqualsNativeR445
        source left right)
      (sym
        (Native.actualNativeR445AllReflectedWordGrams
          theory traceData exponential betaFine
          oneLink bilateral divide
          (selectedPhysicalReflection source) left right))

  -- The original operator-state cyclic vectors themselves (not a
  -- parallel abstract Gram) have the same native word-pair Gram.
  originalSelectedCyclicKetAllWordGramEqualsNativeR445 :
    (source : OriginalSameSourceMeasurement)
    (reflection : Observable → Observable)
    (left right : Word) →
    readOriginalScalarAsReal
      (Cyclic.originalSelectedCyclicPair E laws
        (cylinderOperator source (coarseWord left))
        (cylinderOperator source (coarseWord right)))
    ≡ actualNativeR445WordGram
      (selectedPhysicalReflection source) left right
  originalSelectedCyclicKetAllWordGramEqualsNativeR445
      source left right =
    trans
      (cong readOriginalScalarAsReal
        (sym
          (Cyclic.originalCyclicCrossGramIsActualOperatorPair
            E laws
            (cylinderOperator source (coarseWord left))
            (cylinderOperator source (coarseWord right)))))
      (originalMeasuredAllWordCrossGramEqualsNativeR445
        source left right)

-- Two physical same-source producer obligations are now isolated:
-- (M1) calibrated REAL COMPONENT of one-cylinder original observer
--      readout = original native
--      Wilson-Gibbs expectation, and (M2) original observer * on
--      compiled words = Wilson positive-time reflection product.
-- These are not proved by the abstract QuantumSurface. Nor does
-- this file construct a continuum OS space, observer GNS completion,
-- Stone Hamiltonian, KK metric or original Kubo propagation.
