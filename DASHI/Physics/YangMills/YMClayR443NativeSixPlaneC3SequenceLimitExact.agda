{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayR443NativeSixPlaneC3SequenceLimitExact where

------------------------------------------------------------------------
-- EXACT PHYSICAL-FINITE R443 -> R431 -> FINITE NORMALIZED -> SELECTED LIMIT.
--
-- Source 6-positive-plane C3 is now proved for the SAME n=3 rational SU2
-- bond-data carrier. At each finite cutoff, only the ACTUAL Gibbs-density
-- equality and compact Haar C3 pullback are externally required; R431 and
-- normalization/limit transport come from previously owned source compilers.
--
-- This is a legitimate same-carrier expectation implication, not an
-- unconditional continuum YM construction: n=3 fixes a side-four lattice.
-- Making a continuum limit out of this fixed graph requires an additional
-- scale/refinement/cylinder-inclusion identification NOT claimed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
import DASHI.Physics.YangMills.YMClayR443NativeSixPlaneHaarNumeratorExact as NativeR443
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as Gibbs
import DASHI.Physics.YangMills.YangMillsFiniteHaarActionNumeratorInvariantRound431Exact as R431
import DASHI.Physics.YangMills.YangMillsFiniteNormalizedExpectationSymmetryExact as Normalized
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureSymmetryLimitExact as LimitSym
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

-- The SAME selected n=3 group-valued carrier is retained at every cutoff.
-- No independent finite numerator/normalization witness is introduced.
nativeC3FiniteNumeratorSource :
  ∀ {sequenceLimit limitLaws quotient division}
    (family : Limit.FinitePhysicalNormalizedFamily
      NativeR443.NativeConfiguration
      {sequenceLimit = sequenceLimit} limitLaws quotient division)
    (boundary : ∀ cutoff →
      NativeR443.NativeSixPlaneHaarBoundary
        (Limit.finiteMeasure family cutoff)
        (Limit.integrationLaws family cutoff)) →
  Normalized.FiniteNumeratorActionInvariant
    family NativeR443.nativeC3Observable
nativeC3FiniteNumeratorSource family boundary =
  R431.familyNumeratorActionInvariant
    family NativeR443.nativeC3Observable
    (λ cutoff →
      Gibbs.asFiniteHaarMeasurePreservingAction
        (NativeR443.nativeSixPlaneR443 (boundary cutoff)))
    (λ cutoff action observable configuration → refl)

nativeC3NormalizedExpectationAtEveryCutoff :
  ∀ {sequenceLimit limitLaws quotient division}
    (family : Limit.FinitePhysicalNormalizedFamily
      NativeR443.NativeConfiguration
      {sequenceLimit = sequenceLimit} limitLaws quotient division)
    (boundary : ∀ cutoff →
      NativeR443.NativeSixPlaneHaarBoundary
        (Limit.finiteMeasure family cutoff)
        (Limit.integrationLaws family cutoff))
    cutoff observable →
  Limit.finiteExpectation family cutoff
    (NativeR443.nativeC3Observable NativeR443.c3 observable)
  ≡ Limit.finiteExpectation family cutoff observable
nativeC3NormalizedExpectationAtEveryCutoff family boundary cutoff observable =
  Normalized.finiteNormalizedExpectationInvariantFromNumerator
    family NativeR443.nativeC3Observable
    (nativeC3FiniteNumeratorSource family boundary)
    cutoff NativeR443.c3 observable

-- Once the ORIGINAL selected sequence limit exists and has its original
-- convergence/uniqueness laws, no second C3 limit witness is needed.
nativeC3SelectedSequenceLimitInvariant :
  ∀ {sequenceLimit limitLaws quotient division}
    (family : Limit.FinitePhysicalNormalizedFamily
      NativeR443.NativeConfiguration
      {sequenceLimit = sequenceLimit} limitLaws quotient division)
    (boundary : ∀ cutoff →
      NativeR443.NativeSixPlaneHaarBoundary
        (Limit.finiteMeasure family cutoff)
        (Limit.integrationLaws family cutoff))
    observable →
  Limit.limitExpectation family
    (NativeR443.nativeC3Observable NativeR443.c3 observable)
  ≡ Limit.limitExpectation family observable
nativeC3SelectedSequenceLimitInvariant family boundary observable =
  LimitSym.continuumExpectationInvariant
    (record
      { LimitSym.FinitePhysicalSymmetryLimitInputs.act =
          NativeR443.nativeC3Observable
      ; LimitSym.FinitePhysicalSymmetryLimitInputs.finiteExpectationInvariant =
          λ cutoff action obs →
            Normalized.finiteNormalizedExpectationInvariantFromNumerator
              family NativeR443.nativeC3Observable
              (nativeC3FiniteNumeratorSource family boundary)
              cutoff action obs
      })
    NativeR443.c3 observable
