module DASHI.Moonshine.DeltaConstructedComplexReflectionCutsetExact where

------------------------------------------------------------------------
-- CONSTRUCTED-COMPLEX / EISENSTEIN SAME-OBJECT CUTSET
--
-- Repo archaeology shows that the complex side is already present:
--
-- * ConcreteComplex owns the literal pair carrier and conjugation;
-- * OrdinaryComplexPolar owns proof-relevant principal argument;
-- * JInvariantConstructedComplexKleinJBackendExact owns a literal Klein-j
--   backend over that concrete complex carrier;
-- * ConcreteComplexConjugationProductExact derives conjugation
--   multiplicativity from ordinary real-ring laws.
--
-- Therefore the live Delta reflection blocker is NOT "construct complex
-- numbers" or "construct arg".  It is the same-object weld between the
-- abstract EisensteinAnalyticModel carrying the all-SL2(Z) theorem and this
-- concrete complex/Klein backend.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Analysis.ConcreteComplexConjugationProductExact as ConjProduct
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact as Disc
import DASHI.Moonshine.DeltaNormalizedWeight12SameObjectExact as Delta12
import DASHI.Moonshine.JInvariantConstructedComplexKleinJBackendExact as KleinBackend
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as FiniteEisenstein
import DASHI.Moonshine.JInvariantEisensteinConstructedKleinJExact as FiniteKlein
import DASHI.Moonshine.EisensteinTruncationConvergenceCompilerExact as LimitCompiler
import DASHI.Moonshine.EisensteinUpperHalfPlaneQDiskExact as QDisk
import DASHI.Moonshine.EisensteinCoefficientMajorantExact as Majorant

------------------------------------------------------------------------
-- 1. Explicit bidirectional same-object bridge.
--
-- We use maps + roundtrips rather than silently transporting along a guessed
-- equality.  A later literal carrier equality may make these maps identities.
------------------------------------------------------------------------

record ConstructedComplexEisensteinSameObject
    (C : Complex.ConstructedComplexPackage)
    (D : Polar.RealDivisionAndSquareRoot
          (Real.real (Complex.realPackage C)))
    (F : Polar.ComplexFieldAuthority
          (Real.real (Complex.realPackage C)) D)
    (K : KleinBackend.ConstructedComplexKleinData C D F)
    (M : Eisenstein.EisensteinAnalyticModel)
    (A : Disc.DiscriminantAlgebra M)
    (N : Delta12.WeightCompatibleNormalization M) : Set₁ where

  private
    R = Real.real (Complex.realPackage C)

  field
    scalarToConcrete :
      Eisenstein.Scalar M → Complex.ComplexPair R

    concreteToScalar :
      Complex.ComplexPair R → Eisenstein.Scalar M

    scalarConcreteRoundTrip :
      (x : Eisenstein.Scalar M) →
      concreteToScalar (scalarToConcrete x) ≡ x

    concreteScalarRoundTrip :
      (z : Complex.ComplexPair R) →
      scalarToConcrete (concreteToScalar z) ≡ z

    parameterToKleinPoint :
      Eisenstein.Parameter M → KleinBackend.Point K

    kleinPointToParameter :
      KleinBackend.Point K → Eisenstein.Parameter M

    parameterKleinRoundTrip :
      (tau : Eisenstein.Parameter M) →
      kleinPointToParameter (parameterToKleinPoint tau) ≡ tau

    kleinParameterRoundTrip :
      (z : KleinBackend.Point K) →
      parameterToKleinPoint (kleinPointToParameter z) ≡ z

    parameterAsConcrete :
      Eisenstein.Parameter M → Complex.ComplexPair R

    parameterAsConcreteAgreesWithKleinTau :
      (tau : Eisenstein.Parameter M) →
      parameterAsConcrete tau
      ≡ KleinBackend.tau K (parameterToKleinPoint tau)

    multiplicationSameObject :
      (x y : Eisenstein.Scalar M) →
      scalarToConcrete (Eisenstein._*ˢ_ M x y)
      ≡ Complex._*C_ (scalarToConcrete x) (scalarToConcrete y)

    normalizedDeltaSameObject :
      (tau : Eisenstein.Parameter M) →
      scalarToConcrete (Delta12.normalizedDelta M A N tau)
      ≡ KleinBackend.delta K (parameterToKleinPoint tau)

open ConstructedComplexEisensteinSameObject public

------------------------------------------------------------------------
-- 2. Concrete analytic reflection obligations after the carrier weld.
--
-- These are intentionally the smallest remaining statements.  Complex
-- conjugation itself and principal argument are already owned elsewhere.
------------------------------------------------------------------------

record ConstructedComplexReflectionLeaves
    (C : Complex.ConstructedComplexPackage)
    (D : Polar.RealDivisionAndSquareRoot
          (Real.real (Complex.realPackage C)))
    (F : Polar.ComplexFieldAuthority
          (Real.real (Complex.realPackage C)) D)
    (K : KleinBackend.ConstructedComplexKleinData C D F) : Set₁ where

  private
    R = Real.real (Complex.realPackage C)

  field
    negConjugatePoint :
      KleinBackend.Point K → KleinBackend.Point K

    reciprocalConjugatePoint :
      KleinBackend.Point K → KleinBackend.Point K

    deltaNegConjugation :
      (z : KleinBackend.Point K) →
      KleinBackend.delta K (negConjugatePoint z)
      ≡ Complex.conjugateC (KleinBackend.delta K z)

    unitCircleFixed :
      KleinBackend.Point K → Set

    unitCircleImpliesReciprocalConjugateFixed :
      (z : KleinBackend.Point K) →
      unitCircleFixed z →
      reciprocalConjugatePoint z ≡ z

open ConstructedComplexReflectionLeaves public

------------------------------------------------------------------------
-- 3. Principal phase is already a repo object.
------------------------------------------------------------------------

record ConstructedComplexPhaseAttachment
    (C : Complex.ConstructedComplexPackage)
    (D : Polar.RealDivisionAndSquareRoot
          (Real.real (Complex.realPackage C)))
    (F : Polar.ComplexFieldAuthority
          (Real.real (Complex.realPackage C)) D) : Set₁ where
  private
    R = Real.real (Complex.realPackage C)
  field
    polar : Polar.OrdinaryPolarData C D F

    deltaArgumentDomain :
      Complex.ComplexPair R → Set

    argumentDomainIntoPolarDomain :
      (z : Complex.ComplexPair R) →
      deltaArgumentDomain z →
      Polar.Domain polar z

open ConstructedComplexPhaseAttachment public

------------------------------------------------------------------------
-- 4. Frontier.
------------------------------------------------------------------------

record DeltaConstructedComplexReflectionCutsetBoundary : Set where
  constructor delta-constructed-complex-reflection-cutset-boundary
  field
    concreteComplexCarrierAlreadyOwned : Bool
    concreteConjugationAlreadyOwned : Bool
    conjugationMultiplicativityReducedToExistingRealRingLeaf : Bool
    proofRelevantPrincipalArgumentAlreadyOwned : Bool
    concreteKleinJBackendAlreadyOwned : Bool
    finiteConstructedE4E6DeltaJRouteAlreadyOwned : Bool
    finiteToInfiniteDeltaLimitCompilerOwned : Bool
    sigma3Sigma5GrowthAndQDiskReductionOwned : Bool
    coefficientMajorantReductionOwned : Bool
    finiteRouteEqualsInfiniteAnalyticRoute : Bool

    abstractEisensteinScalarWeldedToConcreteComplex : Bool
    abstractEisensteinParameterWeldedToConcreteKleinPoint : Bool
    normalizedDeltaWeldedToConcreteKleinDelta : Bool
    infiniteDeltaNegConjugationClosed : Bool
    unitCircleFixedPointSemanticsClosed : Bool

    nextResidual : String

open DeltaConstructedComplexReflectionCutsetBoundary public

canonicalDeltaConstructedComplexReflectionCutsetBoundary :
  DeltaConstructedComplexReflectionCutsetBoundary
canonicalDeltaConstructedComplexReflectionCutsetBoundary =
  delta-constructed-complex-reflection-cutset-boundary
    true true true true true
    true true true true false
    false false false false false
    "finite E4/E6, internal sigma3/sigma5 bounds, upper-half-plane q-disk reduction, complex-term polynomial-geometric majorants, and the Delta/j limit compiler now exist. Close the selected backend norm/q laws and the eventual polynomial-geometric successor ratios, transport to literal E4_N/E6_N convergence, then prove the same-object identification with EisensteinAnalyticModel before attaching S/conjugation and the unit-circle fixed-point law"
