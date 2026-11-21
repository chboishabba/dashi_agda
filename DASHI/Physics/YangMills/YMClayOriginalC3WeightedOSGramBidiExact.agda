module DASHI.Physics.YangMills.YMClayOriginalC3WeightedOSGramBidiExact where

------------------------------------------------------------------------
-- YM P0: SAME ORIGINAL weighted Wilson C3 -> reflected-Gram zero fibre.
-- Source owners are imported, NOT replaced:
--   YMClayOriginalWilsonC3WeightedHaarTransferExact (original Gibbs).
--   YMClayNativeSideFourC3VectorWeldExact (1024 native bonds).
--   YMClaySUNMatrixProductHaarC3Exact (original product Haar).
-- Original Wilson RP: YMClayOriginalR445PublishedWilsonRPWordWeldExact.
-- Same E1/OS endpoint: YangMillsClayPinnedCMP119OSReconstructionExact.
--
-- This consumes the REAL ORIGINAL side-four SU(N) Gibbs density, not
-- the Q8 diagnostic. Actual weighted C3 density invariance and actual
-- canonical-label equality remain explicit. To preserve a reflected
-- form, original time reflection must commute with the SAME spatial C3.
-- This is finite REAL Gram invariance, NOT full complex OS2, nor
-- actual continuum OS quotient, same-H semigroup, or physical gap.
-- Eisenstein C3 characters are only a representation-algebra donor.
-- Agda kernel NOT RUN. Wilson, Haar, OS, Balaban retain attribution.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; trans; sym)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Single
import DASHI.Physics.YangMills.YMClayNativeSideFourC3VectorWeldExact as C3
import DASHI.Physics.YangMills.YMClayNativeC3AdjacentSortProgramExact as Sort
import DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarC3Exact as Congruence
import DASHI.Physics.YangMills.YMClayOriginalWilsonC3WeightedHaarTransferExact as WilsonC3

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (divide : ℝ → ℝ → ℝ)
  where

  OriginalVec : Set
  OriginalVec = Vec.Vec (SUN.SUNMatrixElement theory) Single.Count

  OriginalObservable : Set
  OriginalObservable = OriginalVec → ℝ

  -- Definitionally the original selected Wilson weighted expectation.
  originalExpectation : OriginalObservable → ℝ
  originalExpectation =
    WilsonC3.actualOriginalFineNormalized
      theory traceData exponential betaFine oneLink divide

  originalDensity : OriginalVec → ℝ
  originalDensity =
    WilsonC3.actualOriginalFineWilsonDensity
      theory traceData exponential betaFine oneLink divide

  -- Literal CMP119 spatial C3 permutation of the original native bonds.
  rotate : OriginalObservable → OriginalObservable
  rotate observable links = observable (C3.forwardVector links)

  originalC3ObservableOrderThree :
    ∀ observable links →
      rotate (rotate (rotate observable)) links ≡ observable links
  originalC3ObservableOrderThree observable links =
    cong observable (C3.forwardVectorOrderThree links)

  -- Pointwise integrand equality on the very same ORIGINAL density
  -- and ORIGINAL normalization; no function extensionality assumed.
  originalExpectationPointwiseCongruence :
    ∀ (left right : OriginalObservable) →
      (∀ links → left links ≡ right links) →
      originalExpectation left ≡ originalExpectation right
  originalExpectationPointwiseCongruence left right same =
    cong
      (λ numerator →
        divide numerator
          (WilsonC3.actualOriginalFinePartition
            theory traceData exponential betaFine oneLink divide))
      (Congruence.productIntegralCongruent oneLink _ _
        (λ links →
          cong (λ value → originalDensity links *ℝ value)
               (same links)))

  originalWeightedC3ExpectationSymmetry :
    Sort.constructedNativeC3CanonicalLabelGoal →
    WilsonC3.ActualOriginalC3GibbsActionInvariant
      theory traceData exponential betaFine oneLink divide →
    ∀ observable →
      originalExpectation (rotate observable)
      ≡ originalExpectation observable
  originalWeightedC3ExpectationSymmetry canonical density observable =
    WilsonC3.actualOriginalWeightedC3NormalizedInvariant
      theory traceData exponential betaFine oneLink divide
      canonical density observable

  -- Real source-level reflected entry; NOT an OS positive complex
  -- Gram until the actual gauge-invariant positive-time domain and
  -- published Wilson reflection positivity are identified.
  originalReflectedGramEntry :
    (OriginalVec → OriginalVec) →
    OriginalObservable → OriginalObservable → ℝ
  originalReflectedGramEntry reflect left right =
    originalExpectation (λ links →
      left (reflect links) *ℝ right links)

  ReflectionCommutesWithOriginalSpatialC3 :
    (OriginalVec → OriginalVec) → Set
  ReflectionCommutesWithOriginalSpatialC3 reflect =
    ∀ links →
      reflect (C3.forwardVector links)
      ≡ C3.forwardVector (reflect links)

  -- Key same-source weld:
  -- ORIGINAL Gibbs weighted C3 + ORIGINAL temporal-reflection
  -- compatibility ==> ORIGINAL reflected-form C3 invariance.
  originalReflectedGramC3Invariant :
    (reflect : OriginalVec → OriginalVec) →
    ReflectionCommutesWithOriginalSpatialC3 reflect →
    Sort.constructedNativeC3CanonicalLabelGoal →
    WilsonC3.ActualOriginalC3GibbsActionInvariant
      theory traceData exponential betaFine oneLink divide →
    ∀ left right →
      originalReflectedGramEntry reflect
        (rotate left) (rotate right)
      ≡ originalReflectedGramEntry reflect left right
  originalReflectedGramC3Invariant
      reflect reflectC3 canonical density left right =
    trans
      (originalExpectationPointwiseCongruence
        (λ links →
          left (C3.forwardVector (reflect links))
          *ℝ right (C3.forwardVector links))
        (rotate (λ links →
          left (reflect links) *ℝ right links))
        (λ links →
          cong₂ _*ℝ_
            (cong left (sym (reflectC3 links))) refl))
      (originalWeightedC3ExpectationSymmetry
        canonical density
        (λ links → left (reflect links) *ℝ right links))

  -- Original reflected-semimorm-zero predicate. This zero is
  -- NOT phase exponent 0 (=unity), an elliptic kernel, or energy 0.
  OriginalReflectedNull :
    (OriginalVec → OriginalVec) → OriginalObservable → Set
  OriginalReflectedNull reflect observable =
    originalReflectedGramEntry reflect observable observable ≡ 0ℝ

  originalC3PreservesReflectedNull :
    (reflect : OriginalVec → OriginalVec) →
    ReflectionCommutesWithOriginalSpatialC3 reflect →
    Sort.constructedNativeC3CanonicalLabelGoal →
    WilsonC3.ActualOriginalC3GibbsActionInvariant
      theory traceData exponential betaFine oneLink divide →
    ∀ observable →
      OriginalReflectedNull reflect observable →
      OriginalReflectedNull reflect (rotate observable)
  originalC3PreservesReflectedNull
      reflect reflectC3 canonical density observable isNull =
    trans
      (originalReflectedGramC3Invariant
        reflect reflectC3 canonical density observable observable)
      isNull

------------------------------------------------------------------------
-- P0 remains: inhabit source Gibbs density C3, actual original time
-- reflection compatibility, full complex Gram OS2 / positive-time
-- cylinder domain, same-E1 continuum, OS completion, unitary U_C3,
-- U_C3*T(t)=T(t)*U_C3, and all three C3-sector common decay rate.
------------------------------------------------------------------------
