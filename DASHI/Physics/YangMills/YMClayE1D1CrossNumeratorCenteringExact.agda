module DASHI.Physics.YangMills.YMClayE1D1CrossNumeratorCenteringExact where

------------------------------------------------------------------------
-- P0 E1/D1: actual ORIGINAL Wilson R445 weighted cross-numerator
-- is insensitive to any scalar constant-mode shift.
--
-- True fine side-four interacting Wilson Gibbs and native two-link
-- SU(N) block; true independent bare side-two Wilson Gibbs.
-- Uses their proved finite product-Haar numerator add/scale/unit
-- identities, and existing ordered real ring identities only.
--
-- The selected RealAnalysisAxioms authority does not expose the
-- equation x-c = x+(-c)*1 as a named lemma. Accordingly we prove
-- unconditional algebraic centering for F + c*1, and expose that
-- exact scalar identity as an explicit *argument* for spelling the
-- result using subtraction. No new postulate is added.
--
-- This is NOT a quantitative nonconstant RG estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; -ℝ_; _<ℝ_; _≤ℝ_;
   +-identityʳ; subSelf; subAddDistributes;
   *-assoc; *-comm; mulOneʳ; *-distribʳ-+)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact as Push
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact as Original
import DASHI.Physics.YangMills.YMClayE1A3OriginalR445WeightedCrossNumeratorExact as Cross
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.YMClayE1D1OriginalVariablePlaquetteWordsExact as Words

-- Pure scalar identity: constant-mode cross-numerator terms cancel.
-- Note that all multiplication is the selected real-ring operation.
weightedCrossShiftCancellation :
  (fine bare finePartition barePartition scalar : ℝ) →
  (((fine +ℝ scalar *ℝ finePartition) *ℝ barePartition)
    -ℝ ((bare +ℝ scalar *ℝ barePartition) *ℝ finePartition))
  ≡
  ((fine *ℝ barePartition) -ℝ (bare *ℝ finePartition))
weightedCrossShiftCancellation fine bare zf zb scalar =
  trans
    (cong₂ _-ℝ_
      (*-distribʳ-+ fine (scalar *ℝ zf) zb)
      (*-distribʳ-+ bare (scalar *ℝ zb) zf))
    (trans
      (subAddDistributes
        (fine *ℝ zb) ((scalar *ℝ zf) *ℝ zb)
        (bare *ℝ zf) ((scalar *ℝ zb) *ℝ zf))
      (trans
        (cong
          (λ rest →
            ((fine *ℝ zb) -ℝ (bare *ℝ zf)) +ℝ rest)
          (trans
            (cong
              (λ value → ((scalar *ℝ zf) *ℝ zb) -ℝ value)
              (trans
                (*-assoc scalar zb zf)
                (trans
                  (cong (λ value → scalar *ℝ value)
                    (*-comm zb zf))
                  (sym (*-assoc scalar zf zb)))))
            (subSelf ((scalar *ℝ zf) *ℝ zb))))
        (+-identityʳ
          ((fine *ℝ zb) -ℝ (bare *ℝ zf)))))

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value)
  where

  CoarseTest : Set
  CoarseTest =
    Cross.CoarseTest
      theory traceData exponential beta oneLink bilateral divide

  fineNumerator : CoarseTest → ℝ
  fineNumerator =
    Cross.fineBlockedNumerator
      theory traceData exponential beta oneLink bilateral divide

  bareNumerator : CoarseTest → ℝ
  bareNumerator =
    Cross.bareCoarseNumerator
      theory traceData exponential beta oneLink bilateral divide

  zFine : ℝ
  zFine =
    Cross.finePartition
      theory traceData exponential beta oneLink bilateral divide

  zBare : ℝ
  zBare =
    Cross.bareCoarsePartition
      theory traceData exponential beta oneLink bilateral divide

  X : CoarseTest → ℝ
  X =
    Cross.originalWilsonR445CrossNumerator
      theory traceData exponential beta oneLink bilateral divide

  constantMode : ℝ → CoarseTest
  constantMode scalar _ = scalar *ℝ 1ℝ

  shiftByConstant : CoarseTest → ℝ → CoarseTest
  shiftByConstant test scalar coarse =
    test coarse +ℝ constantMode scalar coarse

  fineConstantNumerator :
    (scalar : ℝ) →
    fineNumerator (constantMode scalar) ≡ scalar *ℝ zFine
  fineConstantNumerator scalar =
    trans
      (Push.actualPushforwardNumeratorScale
        theory traceData exponential (beta 3) oneLink bilateral divide
        ordered strictToWeak scalar (λ _ → 1ℝ))
      (cong (λ value → scalar *ℝ value)
        (Push.actualPushforwardNumeratorOne
          theory traceData exponential (beta 3) oneLink bilateral divide
          ordered strictToWeak))

  bareConstantNumerator :
    (scalar : ℝ) →
    bareNumerator (constantMode scalar) ≡ scalar *ℝ zBare
  bareConstantNumerator scalar =
    trans
      (Finite.numeratorScale
        (Original.originalWilsonFiniteIntegrationLaws
          theory traceData exponential beta oneLink bilateral divide
          ordered strictToWeak 1)
        scalar (λ _ → 1ℝ))
      (cong (λ value → scalar *ℝ value)
        (Original.originalWilsonUnitNumeratorIsPartition
          theory traceData exponential beta oneLink bilateral divide
          ordered strictToWeak 1))

  fineShiftNumerator :
    (test : CoarseTest) (scalar : ℝ) →
    fineNumerator (shiftByConstant test scalar)
      ≡ fineNumerator test +ℝ scalar *ℝ zFine
  fineShiftNumerator test scalar =
    trans
      (Push.actualPushforwardNumeratorAdd
        theory traceData exponential (beta 3) oneLink bilateral divide
        ordered strictToWeak test (constantMode scalar))
      (cong (λ value → fineNumerator test +ℝ value)
        (fineConstantNumerator scalar))

  bareShiftNumerator :
    (test : CoarseTest) (scalar : ℝ) →
    bareNumerator (shiftByConstant test scalar)
      ≡ bareNumerator test +ℝ scalar *ℝ zBare
  bareShiftNumerator test scalar =
    trans
      (Finite.numeratorAdd
        (Original.originalWilsonFiniteIntegrationLaws
          theory traceData exponential beta oneLink bilateral divide
          ordered strictToWeak 1)
        test (constantMode scalar))
      (cong (λ value → bareNumerator test +ℝ value)
        (bareConstantNumerator scalar))

  originalWilsonCrossNumeratorConstantShift :
    (test : CoarseTest) (scalar : ℝ) →
    X (shiftByConstant test scalar) ≡ X test
  originalWilsonCrossNumeratorConstantShift test scalar =
    trans
      (cong₂ (λ fine bare →
        (fine *ℝ zBare) -ℝ (bare *ℝ zFine))
        (fineShiftNumerator test scalar)
        (bareShiftNumerator test scalar))
      (weightedCrossShiftCancellation
        (fineNumerator test) (bareNumerator test)
        zFine zBare scalar)

  -- Centering with a *negative scalar* is unconditional; to identify
  -- it with pointwise subtraction x - c requires the original scalar
  -- carrier's subtraction-as-additive-inverse law.
  originalWilsonCrossNumeratorNegativeCentering :
    (test : CoarseTest) (center : ℝ) →
    X (shiftByConstant test (-ℝ center)) ≡ X test
  originalWilsonCrossNumeratorNegativeCentering test center =
    originalWilsonCrossNumeratorConstantShift test (-ℝ center)

  fineNumeratorCongruent :
    (left right : CoarseTest) →
    (∀ coarse → left coarse ≡ right coarse) →
    fineNumerator left ≡ fineNumerator right
  fineNumeratorCongruent left right pointwise =
    Finite.haarIntegralCongruent
      (Push.originalFineIntegrationLaws
        theory traceData exponential (beta 3) oneLink bilateral divide
        ordered strictToWeak)
      (λ fine →
        Physical.density
          (Push.originalFineGibbsMeasure
            theory traceData exponential (beta 3) oneLink bilateral divide)
          fine
        *ℝ left
          (Push.actualBlockedLinkMap
            theory traceData exponential (beta 3) oneLink bilateral divide
            fine))
      (λ fine →
        Physical.density
          (Push.originalFineGibbsMeasure
            theory traceData exponential (beta 3) oneLink bilateral divide)
          fine
        *ℝ right
          (Push.actualBlockedLinkMap
            theory traceData exponential (beta 3) oneLink bilateral divide
            fine))
      (λ fine →
        cong
          (λ value →
            Physical.density
              (Push.originalFineGibbsMeasure
                theory traceData exponential (beta 3) oneLink bilateral divide)
              fine *ℝ value)
          (pointwise
            (Push.actualBlockedLinkMap
              theory traceData exponential (beta 3) oneLink bilateral divide
              fine)))

  bareNumeratorCongruent :
    (left right : CoarseTest) →
    (∀ coarse → left coarse ≡ right coarse) →
    bareNumerator left ≡ bareNumerator right
  bareNumeratorCongruent left right pointwise =
    Finite.haarIntegralCongruent
      (Original.originalWilsonFiniteIntegrationLaws
        theory traceData exponential beta oneLink bilateral divide
        ordered strictToWeak 1)
      (λ coarse →
        Physical.density
          (Original.originalWilsonMeasure
            theory traceData exponential beta oneLink bilateral divide 1)
          coarse *ℝ left coarse)
      (λ coarse →
        Physical.density
          (Original.originalWilsonMeasure
            theory traceData exponential beta oneLink bilateral divide 1)
          coarse *ℝ right coarse)
      (λ coarse →
        cong
          (λ value →
            Physical.density
              (Original.originalWilsonMeasure
                theory traceData exponential beta oneLink bilateral divide 1)
              coarse *ℝ value)
          (pointwise coarse))

  crossNumeratorCongruent :
    (left right : CoarseTest) →
    (∀ coarse → left coarse ≡ right coarse) →
    X left ≡ X right
  crossNumeratorCongruent left right pointwise =
    cong₂
      (λ fine bare →
        (fine *ℝ zBare) -ℝ (bare *ℝ zFine))
      (fineNumeratorCongruent left right pointwise)
      (bareNumeratorCongruent left right pointwise)

  originalWilsonCrossNumeratorSubtractionCentering :
    (test : CoarseTest) (center : ℝ) →
    (scalarSubtract :
      ∀ value → value -ℝ center ≡ value +ℝ (-ℝ center) *ℝ 1ℝ) →
    X (λ coarse → test coarse -ℝ center) ≡ X test
  originalWilsonCrossNumeratorSubtractionCentering
    test center scalarSubtract =
    trans
      (crossNumeratorCongruent
        (λ coarse → test coarse -ℝ center)
        (shiftByConstant test (-ℝ center))
        (λ coarse → scalarSubtract (test coarse)))
      (originalWilsonCrossNumeratorNegativeCentering test center)

  -- Literal original side-two plaquette test, not an abstract chosen
  -- observable. We retain its actual normalized real SU(N) trace and
  -- signed original Wilson holonomy; no [0,1] trace bound is assumed.
  originalCoarsePlaquetteTrace :
    Plaquette.PeriodicPlaquette 1 → CoarseTest
  originalCoarsePlaquetteTrace plaquette =
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide
      1 (plaquette ∷ [])

  originalPlaquetteCrossNumeratorConstantShift :
    (plaquette : Plaquette.PeriodicPlaquette 1)
    (scalar : ℝ) →
    X (shiftByConstant (originalCoarsePlaquetteTrace plaquette) scalar)
    ≡ X (originalCoarsePlaquetteTrace plaquette)
  originalPlaquetteCrossNumeratorConstantShift plaquette scalar =
    originalWilsonCrossNumeratorConstantShift
      (originalCoarsePlaquetteTrace plaquette) scalar

  originalPlaquetteCrossNumeratorSubtractionCentering :
    (plaquette : Plaquette.PeriodicPlaquette 1)
    (center : ℝ) →
    (scalarSubtract :
      ∀ value → value -ℝ center ≡ value +ℝ (-ℝ center) *ℝ 1ℝ) →
    X (λ coarse →
      originalCoarsePlaquetteTrace plaquette coarse -ℝ center)
    ≡ X (originalCoarsePlaquetteTrace plaquette)
  originalPlaquetteCrossNumeratorSubtractionCentering
    plaquette center scalarSubtract =
    originalWilsonCrossNumeratorSubtractionCentering
      (originalCoarsePlaquetteTrace plaquette)
      center scalarSubtract
