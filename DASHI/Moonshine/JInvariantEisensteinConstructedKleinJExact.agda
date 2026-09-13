module DASHI.Moonshine.JInvariantEisensteinConstructedKleinJExact where

------------------------------------------------------------------------
-- FINITE EISENSTEIN q-SERIES -> CONSTRUCTED COMPLEX KLEIN-j
--
-- This weld uses the exact finite E4/E6 recurrence and the proof-relevant
-- complex quotient.  It deliberately distinguishes:
--
--   direct runtime form:
--     1728 E4_N^3 / (E4_N^3 - E6_N^2)
--
--   source-facing Klein construction form:
--     g2_N^3 / Delta_N
--
-- with the renderer normalization
--     g2_N    = E4_N
--     Delta_N = (E4_N^3 - E6_N^2) / 1728.
--
-- Equality of the two evaluation routes is an explicit normalization receipt;
-- it is not manufactured from insufficient inverse laws.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Q
import DASHI.Moonshine.JInvariantConstructedComplexKleinJBackendExact as CKlein
import DASHI.Moonshine.JInvariantProofRelevantKleinJExact as Klein

private
  ComplexCarrier :
    (C : Complex.ConstructedComplexPackage) → Set
  ComplexCarrier C =
    Complex.ComplexPair (Real.real (Complex.realPackage C))

scalar1728 :
  (C : Complex.ConstructedComplexPackage) →
  ComplexCarrier C
scalar1728 C = Q.scaleNatC 1728 Complex.oneC

record EisensteinNormalizationData
  (C : Complex.ConstructedComplexPackage)
  (D : Polar.RealDivisionAndSquareRoot
        (Real.real (Complex.realPackage C)))
  (F : Polar.ComplexFieldAuthority
        (Real.real (Complex.realPackage C)) D) : Set where
  constructor eisenstein-normalization-data
  field
    scalar1728Nonzero : Polar.NonzeroC F (scalar1728 C)

open EisensteinNormalizationData public

record CertifiedFiniteEisensteinPoint
  (C : Complex.ConstructedComplexPackage)
  (D : Polar.RealDivisionAndSquareRoot
        (Real.real (Complex.realPackage C)))
  (F : Polar.ComplexFieldAuthority
        (Real.real (Complex.realPackage C)) D)
  (kernel : Q.DivisorPowerKernel)
  (terms : Nat)
  (normalization : EisensteinNormalizationData C D F) : Set where
  constructor certified-finite-eisenstein-point
  field
    tau : ComplexCarrier C

    discriminantNumeratorNonzero :
      Polar.NonzeroC F
        (Q.discriminantNumeratorTruncated C kernel terms tau)

    normalizedDeltaNonzero :
      Polar.NonzeroC F
        (CKlein.quotientC F
          (Q.discriminantNumeratorTruncated C kernel terms tau)
          (scalar1728 C)
          (scalar1728Nonzero normalization))

open CertifiedFiniteEisensteinPoint public

normalizedDelta :
  (C : Complex.ConstructedComplexPackage) →
  (D : Polar.RealDivisionAndSquareRoot
        (Real.real (Complex.realPackage C))) →
  (F : Polar.ComplexFieldAuthority
        (Real.real (Complex.realPackage C)) D) →
  (kernel : Q.DivisorPowerKernel) →
  (terms : Nat) →
  (normalization : EisensteinNormalizationData C D F) →
  CertifiedFiniteEisensteinPoint C D F kernel terms normalization →
  ComplexCarrier C
normalizedDelta C D F kernel terms normalization point =
  CKlein.quotientC F
    (Q.discriminantNumeratorTruncated C kernel terms (tau point))
    (scalar1728 C)
    (scalar1728Nonzero normalization)

eisensteinKleinData :
  (C : Complex.ConstructedComplexPackage) →
  (D : Polar.RealDivisionAndSquareRoot
        (Real.real (Complex.realPackage C))) →
  (F : Polar.ComplexFieldAuthority
        (Real.real (Complex.realPackage C)) D) →
  (kernel : Q.DivisorPowerKernel) →
  (terms : Nat) →
  (normalization : EisensteinNormalizationData C D F) →
  CKlein.ConstructedComplexKleinData C D F
eisensteinKleinData C D F kernel terms normalization =
  record
    { CKlein.Point =
        CertifiedFiniteEisensteinPoint C D F kernel terms normalization
    ; CKlein.tau = tau
    ; CKlein.g2 =
        λ point → Q.e4Truncated C kernel terms (tau point)
    ; CKlein.delta =
        normalizedDelta C D F kernel terms normalization
    ; CKlein.deltaNonzero = normalizedDeltaNonzero
    }

eisensteinKlein :
  (C : Complex.ConstructedComplexPackage) →
  (D : Polar.RealDivisionAndSquareRoot
        (Real.real (Complex.realPackage C))) →
  (F : Polar.ComplexFieldAuthority
        (Real.real (Complex.realPackage C)) D) →
  (kernel : Q.DivisorPowerKernel) →
  (terms : Nat) →
  (normalization : EisensteinNormalizationData C D F) →
  Klein.ProofRelevantKleinJAlgebra
eisensteinKlein C D F kernel terms normalization =
  CKlein.constructedComplexKleinJ C D F
    (eisensteinKleinData C D F kernel terms normalization)

------------------------------------------------------------------------
-- Direct evaluator used by the existing Python numerical kernel.
------------------------------------------------------------------------

directJTruncated :
  (C : Complex.ConstructedComplexPackage) →
  (D : Polar.RealDivisionAndSquareRoot
        (Real.real (Complex.realPackage C))) →
  (F : Polar.ComplexFieldAuthority
        (Real.real (Complex.realPackage C)) D) →
  (kernel : Q.DivisorPowerKernel) →
  (terms : Nat) →
  (normalization : EisensteinNormalizationData C D F) →
  CertifiedFiniteEisensteinPoint C D F kernel terms normalization →
  ComplexCarrier C
directJTruncated C D F kernel terms normalization point =
  Q.scaleNatC 1728
    (CKlein.quotientC F
      (Q.cubeC (Q.e4Truncated C kernel terms (tau point)))
      (Q.discriminantNumeratorTruncated C kernel terms (tau point))
      (discriminantNumeratorNonzero point))

record EisensteinKleinNormalizationAgreement
  (C : Complex.ConstructedComplexPackage)
  (D : Polar.RealDivisionAndSquareRoot
        (Real.real (Complex.realPackage C)))
  (F : Polar.ComplexFieldAuthority
        (Real.real (Complex.realPackage C)) D)
  (kernel : Q.DivisorPowerKernel)
  (terms : Nat)
  (normalization : EisensteinNormalizationData C D F) : Set₁ where
  constructor eisenstein-klein-normalization-agreement
  field
    routesAgree :
      (point : CertifiedFiniteEisensteinPoint C D F kernel terms normalization) →
      Klein.KleinJ (eisensteinKlein C D F kernel terms normalization) point
      ≡ directJTruncated C D F kernel terms normalization point

open EisensteinKleinNormalizationAgreement public

------------------------------------------------------------------------
-- Frontier.
------------------------------------------------------------------------

record EisensteinConstructedKleinFrontier : Set where
  constructor eisenstein-constructed-klein-frontier
  field
    finiteE4Attached : Bool
    finiteE6Attached : Bool
    normalizedDeltaAttached : Bool
    discriminantNonzeroProofRequired : Bool
    sourceFacingKleinConstructionInstantiated : Bool
    directRuntimeFormulaRepresented : Bool
    routeNormalizationAgreementAutomatic : Bool
    finiteEqualsInfiniteAnalyticJ : Bool

canonicalEisensteinConstructedKleinFrontier : EisensteinConstructedKleinFrontier
canonicalEisensteinConstructedKleinFrontier =
  eisenstein-constructed-klein-frontier
    true true true true true true false false
