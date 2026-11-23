module DASHI.Physics.YangMills.YMClayOriginalC3FullFiniteComplexCoefficientGramBidiExact where

------------------------------------------------------------------------
-- ORIGINAL Wilson SU(N), full finite C3 Gram with COMPLEX COEFFICIENTS.
--
-- This consumes the existing original weighted real Wilson expectation,
-- native C3, original reflection compatibility, and the ORIGINAL
-- BalabanClayT5PhysicalMeasureGramContinuityExact double-sum machinery.
-- It never substitutes a finite Q8 diagnostic for product SU(N) Haar.
--
-- The Wilson insertion basis here is REAL-valued. Arbitrary Scalar
-- coefficients may carry complex conjugation, but the function Scalar
-- (and Real -> Scalar) must be instantiated by an ACTUAL complex algebra.
-- No complex-valued original cylinder algebra or reflection positivity
-- is silently asserted. In particular, the existing test metadata
-- PositiveTimeSupported/GaugeInvariantObservable is only a Set label;
-- its preservation as a label is NOT an admissibility proof.
--
-- Genuine positive-time Wilson word support, gauge invariance after
-- rotation, same physical reflection, full E1 OS limit, C3 action on
-- the completed Hilbert space and D1/D2 physical rate remain OPEN.
--
-- SOURCE-WRITTEN; Agda kernel pending. Prior owners Wilson, Haar,
-- Osterwalder-Schrader, Menotti-Pelissetto, Balaban, DASHI native C3.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)

import Data.Vec.Base as Vec
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Single
import DASHI.Physics.YangMills.YMClayNativeC3AdjacentSortProgramExact as Sort
import DASHI.Physics.YangMills.YMClayOriginalWilsonC3WeightedHaarTransferExact as WilsonC3
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClayOriginalWilsonSpatialC3TimeMirrorBIDIExact as NativeMirror
import DASHI.Physics.YangMills.YMClayOriginalC3WeightedOSGramBidiExact as Source
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (divide : ℝ → ℝ → ℝ)
    (Scalar : Set)
    (zero : Scalar)
    (add multiply : Scalar → Scalar → Scalar)
    (conjugate : Scalar → Scalar)
    (embedReal : ℝ → Scalar)
  where

  OriginalVec : Set
  OriginalVec = Vec.Vec (SUN.SUNMatrixElement theory) Single.Count

  Observable : Set
  Observable = OriginalVec → ℝ

  Test : Set₁
  Test = Gram.PhysicalPositiveTimeCylinderTest Observable Scalar

  Family : Set₁
  Family = Gram.PhysicalOSFiniteTestFamily Observable Scalar

  rotate : Observable → Observable
  rotate = Source.rotate theory traceData exponential betaFine oneLink divide

  -- The ONLY expected measure is original SUN Wilson normalized Gibbs.
  -- Complex coefficients are attached outside this real expectation.
  originalOperations : (OriginalVec → OriginalVec) →
    Gram.PhysicalOSOperations ⊤ Observable Scalar
  originalOperations reflect = record
    { Gram.PhysicalOSOperations.zero = zero
    ; Gram.PhysicalOSOperations.add = add
    ; Gram.PhysicalOSOperations.multiply = multiply
    ; Gram.PhysicalOSOperations.conjugate = conjugate
    ; Gram.PhysicalOSOperations.reflectObservable =
        λ observable links → observable (reflect links)
    ; Gram.PhysicalOSOperations.multiplyObservable =
        λ left right links → left links *ℝ right links
    ; Gram.PhysicalOSOperations.expectation =
        λ _ observable →
          embedReal
            (Source.originalExpectation
              theory traceData exponential betaFine oneLink divide
              observable)
    }

  -- Rotating metadata is a structural relabeling only. An actual
  -- positive-time/gauge support transport is STILL an open source proof.
  rotateTest : Test → Test
  rotateTest test = record
    { Gram.PhysicalPositiveTimeCylinderTest.observable =
        rotate (Gram.observable test)
    ; Gram.PhysicalPositiveTimeCylinderTest.coefficient =
        Gram.coefficient test
    ; Gram.PhysicalPositiveTimeCylinderTest.PositiveTimeSupported =
        Gram.PositiveTimeSupported test
    ; Gram.PhysicalPositiveTimeCylinderTest.GaugeInvariantObservable =
        Gram.GaugeInvariantObservable test
    }

  rotateTests : List Test → List Test
  rotateTests [] = []
  rotateTests (test ∷ rest) = rotateTest test ∷ rotateTests rest

  rotateFamily : Family → Family
  rotateFamily family = record
    { Gram.PhysicalOSFiniteTestFamily.tests =
        rotateTests (Gram.tests family)
    }

  originalEntryIsSourceGram : ∀ reflect left right →
    Gram.physicalReflectedGramEntry (originalOperations reflect) tt left right
    ≡
    multiply
      (multiply (conjugate (Gram.coefficient left))
                (Gram.coefficient right))
      (embedReal
        (Source.originalReflectedGramEntry
          theory traceData exponential betaFine oneLink divide
          reflect (Gram.observable left) (Gram.observable right)))
  originalEntryIsSourceGram reflect left right = refl

  -- Every i,j term in the COMPLEX-coefficient finite Gram is C3 fixed,
  -- on the identical original Wilson source, if the original density
  -- and temporal reflection are genuinely C3 compatible.
  originalEntryC3 : ∀ reflect →
    Source.ReflectionCommutesWithOriginalSpatialC3
      theory traceData exponential betaFine oneLink divide reflect →
    Sort.constructedNativeC3CanonicalLabelGoal →
    WilsonC3.ActualOriginalC3GibbsActionInvariant
      theory traceData exponential betaFine oneLink divide →
    ∀ left right →
    Gram.physicalReflectedGramEntry
      (originalOperations reflect) tt (rotateTest left) (rotateTest right)
    ≡
    Gram.physicalReflectedGramEntry
      (originalOperations reflect) tt left right
  originalEntryC3 reflect commute canonical density left right =
    cong
      (λ value →
        multiply
          (multiply (conjugate (Gram.coefficient left))
                    (Gram.coefficient right))
          (embedReal value))
      (Source.originalReflectedGramC3Invariant
        theory traceData exponential betaFine oneLink divide
        reflect commute canonical density
        (Gram.observable left) (Gram.observable right))

  -- Existing full-double-sum owner is Gram.physicalReflectedGramQuadraticForm.
  -- This list reindexing lemma carries ALL mixed entries (not diagonals).
  sumRotate :
    ∀ (family : List Test) (f g : Test → Scalar) →
      (∀ test → f (rotateTest test) ≡ g test) →
      Gram.sumList add zero (rotateTests family) f
      ≡ Gram.sumList add zero family g
  sumRotate [] f g matches = refl
  sumRotate (test ∷ rest) f g matches =
    cong₂ add (matches test) (sumRotate rest f g matches)

  -- Nonvacuous finite target: C3 invariance of the ORIGINAL weighted
  -- full Gram quadratic for arbitrary finite complex coefficient lists.
  -- This uses the existing original double-sum definition verbatim.
  originalFiniteFullGramC3 :
    ∀ reflect →
    Source.ReflectionCommutesWithOriginalSpatialC3
      theory traceData exponential betaFine oneLink divide reflect →
    Sort.constructedNativeC3CanonicalLabelGoal →
    WilsonC3.ActualOriginalC3GibbsActionInvariant
      theory traceData exponential betaFine oneLink divide →
    ∀ family →
      Gram.physicalReflectedGramQuadraticForm
        (originalOperations reflect) tt (rotateFamily family)
      ≡
      Gram.physicalReflectedGramQuadraticForm
        (originalOperations reflect) tt family
  originalFiniteFullGramC3 reflect commute canonical density family =
    sumRotate
      (Gram.tests family)
      (λ leftRot →
        Gram.sumList add zero (rotateTests (Gram.tests family))
          (λ rightRot →
            Gram.physicalReflectedGramEntry
              (originalOperations reflect) tt leftRot rightRot))
      (λ left →
        Gram.sumList add zero (Gram.tests family)
          (λ right →
            Gram.physicalReflectedGramEntry
              (originalOperations reflect) tt left right))
      (λ left →
        sumRotate (Gram.tests family)
          (λ rightRot →
            Gram.physicalReflectedGramEntry
              (originalOperations reflect) tt
              (rotateTest left) rightRot)
          (λ right →
            Gram.physicalReflectedGramEntry
              (originalOperations reflect) tt left right)
          (λ right →
            originalEntryC3 reflect commute canonical density left right))

  -- Stronger SAME-source consumer: the original native Wilson/R445
  -- time mirror is ALREADY source-proved to commute with this native C3.
  -- The old generic reflection-commutation socket is discharged here,
  -- not reintroduced as an independent uninhabited hypothesis.
  originalNativeMirrorFullFiniteGramC3 :
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink) →
    Sort.constructedNativeC3CanonicalLabelGoal →
    WilsonC3.ActualOriginalC3GibbsActionInvariant
      theory traceData exponential betaFine oneLink divide →
    ∀ family →
      Gram.physicalReflectedGramQuadraticForm
        (originalOperations
          (NativeMirror.mirrorVector
            theory traceData exponential betaFine oneLink bilateral divide))
        tt (rotateFamily family)
      ≡
      Gram.physicalReflectedGramQuadraticForm
        (originalOperations
          (NativeMirror.mirrorVector
            theory traceData exponential betaFine oneLink bilateral divide))
        tt family
  originalNativeMirrorFullFiniteGramC3 bilateral canonical density family =
    originalFiniteFullGramC3
      (NativeMirror.mirrorVector
        theory traceData exponential betaFine oneLink bilateral divide)
      (NativeMirror.actualOriginalMirrorC3Vector
        theory traceData exponential betaFine oneLink bilateral divide)
      canonical density family

------------------------------------------------------------------------
-- NEXT physical attachments: prove the original positive-time/gauge
-- support predicates on rotated real Wilson words, supply original
-- complex linear closure and finite RP, extend C3 to ALL changing
-- cutoffs in the genuine E1 family, prove the same Gram limit action
-- descends to the OS quotient and commutes with its time semigroup.
-- Then and only then address common-rate D1 and dense full D2.
------------------------------------------------------------------------
