module DASHI.Moonshine.JInvariantEisensteinAgdaLeanRealExtractionExact where

------------------------------------------------------------------------
-- REAL/TRANSCENDENTAL EXTRACTION -> COMPLEX EXTRACTION
--
-- This lowers the route-B cross-prover seam one level further.
--
-- Instead of asking for an arbitrary map
--
--     ComplexPair R -> target complex
--
-- preserving all complex operations, it is enough to provide a real map
--
--     Real R -> target real
--
-- preserving the real ring operations together with exp/sin/cos/pi.
--
-- The source ConcreteComplex exponential already owns the Cartesian identity,
-- so the induced componentwise complex map automatically preserves:
--
--   0, 1, i, +, -, *, pi, exp.
--
-- The actual qOf/E4_N/E6_N transport then follows from
-- JInvariantEisensteinAgdaLeanExtractionExact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl; cong; trans)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Q
import DASHI.Moonshine.JInvariantEisensteinAgdaLeanExtractionExact as Extraction

------------------------------------------------------------------------
-- Target real/transcendental algebra.
------------------------------------------------------------------------

record TargetRealTranscendental : Set₁ where
  field
    CarrierR : Set

    zeroR oneR piR : CarrierR
    addR subR mulR : CarrierR → CarrierR → CarrierR
    negR : CarrierR → CarrierR

    expR sinR cosR : CarrierR → CarrierR

open TargetRealTranscendental public

------------------------------------------------------------------------
-- Cartesian complex carrier over the target real.
------------------------------------------------------------------------

record TargetComplexPair (T : TargetRealTranscendental) : Set where
  constructor targetComplex
  field
    reT imT : CarrierR T

open TargetComplexPair public

targetZeroC :
  ∀ {T} → TargetComplexPair T
targetZeroC {T} = targetComplex (zeroR T) (zeroR T)

targetOneC :
  ∀ {T} → TargetComplexPair T
targetOneC {T} = targetComplex (oneR T) (zeroR T)

targetIC :
  ∀ {T} → TargetComplexPair T
targetIC {T} = targetComplex (zeroR T) (oneR T)

targetPiC :
  ∀ {T} → TargetComplexPair T
targetPiC {T} = targetComplex (piR T) (zeroR T)

targetAddC :
  ∀ {T} → TargetComplexPair T → TargetComplexPair T → TargetComplexPair T
targetAddC {T} (targetComplex a b) (targetComplex c d) =
  targetComplex (addR T a c) (addR T b d)

targetSubC :
  ∀ {T} → TargetComplexPair T → TargetComplexPair T → TargetComplexPair T
targetSubC {T} (targetComplex a b) (targetComplex c d) =
  targetComplex (subR T a c) (subR T b d)

targetMulC :
  ∀ {T} → TargetComplexPair T → TargetComplexPair T → TargetComplexPair T
targetMulC {T} (targetComplex a b) (targetComplex c d) =
  targetComplex
    (subR T (mulR T a c) (mulR T b d))
    (addR T (mulR T a d) (mulR T b c))

targetExpC :
  ∀ {T} → TargetComplexPair T → TargetComplexPair T
targetExpC {T} (targetComplex x y) =
  targetComplex
    (mulR T (expR T x) (cosR T y))
    (mulR T (expR T x) (sinR T y))

cartesianTargetComplexAlgebra :
  (T : TargetRealTranscendental) →
  Extraction.TargetComplexAlgebra
cartesianTargetComplexAlgebra T =
  record
    { Extraction.Carrier = TargetComplexPair T
    ; Extraction.zeroT = targetZeroC
    ; Extraction.oneT = targetOneC
    ; Extraction.imaginaryUnitT = targetIC
    ; Extraction.piT = targetPiC
    ; Extraction.addT = targetAddC
    ; Extraction.subT = targetSubC
    ; Extraction.mulT = targetMulC
    ; Extraction.expT = targetExpC
    }

------------------------------------------------------------------------
-- Primitive real/transcendental extraction.
------------------------------------------------------------------------

record RealTranscendentalExtraction
    (C : Complex.ConstructedComplexPackage)
    (T : TargetRealTranscendental) : Set₁ where

  private
    R = Real.real (Complex.realPackage C)
    CE = Complex.complexExponential C
    E = Real.exponential (Complex.realPackage C)

  field
    mapR : Real.Real R → CarrierR T

    preservesZeroR :
      mapR (Real.zero R) ≡ zeroR T

    preservesOneR :
      mapR (Real.one R) ≡ oneR T

    preservesAddR :
      ∀ x y →
      mapR (Real._+_ R x y)
      ≡ addR T (mapR x) (mapR y)

    preservesSubR :
      ∀ x y →
      mapR (Real._-_ R x y)
      ≡ subR T (mapR x) (mapR y)

    preservesMulR :
      ∀ x y →
      mapR (Real._*_ R x y)
      ≡ mulR T (mapR x) (mapR y)

    preservesNegR :
      ∀ x →
      mapR (Real.neg R x)
      ≡ negR T (mapR x)

    preservesRealExp :
      ∀ x →
      mapR (Real.exp E x)
      ≡ expR T (mapR x)

    preservesSin :
      ∀ x →
      mapR (Complex.sin CE x)
      ≡ sinR T (mapR x)

    preservesCos :
      ∀ x →
      mapR (Complex.cos CE x)
      ≡ cosR T (mapR x)

    preservesPi :
      mapR (Complex.pi CE)
      ≡ piR T

open RealTranscendentalExtraction public

------------------------------------------------------------------------
-- Componentwise complex map.
------------------------------------------------------------------------

mapComplex :
  ∀ {C T} →
  RealTranscendentalExtraction C T →
  Complex.ComplexPair
    (Real.real (Complex.realPackage C)) →
  TargetComplexPair T
mapComplex E (Complex.complex x y) =
  targetComplex (mapR E x) (mapR E y)

mapComplexZero :
  ∀ {C T}
    (E : RealTranscendentalExtraction C T) →
  mapComplex E Complex.zeroC
  ≡ targetZeroC
mapComplexZero E
  rewrite preservesZeroR E = refl

mapComplexOne :
  ∀ {C T}
    (E : RealTranscendentalExtraction C T) →
  mapComplex E Complex.oneC
  ≡ targetOneC
mapComplexOne E
  rewrite preservesOneR E
        | preservesZeroR E = refl

mapComplexI :
  ∀ {C T}
    (E : RealTranscendentalExtraction C T) →
  mapComplex E Complex.imaginaryUnit
  ≡ targetIC
mapComplexI E
  rewrite preservesZeroR E
        | preservesOneR E = refl

mapComplexPi :
  ∀ {C T}
    (E : RealTranscendentalExtraction C T) →
  mapComplex E
    (Complex.complex
      (Complex.pi (Complex.complexExponential C))
      (Real.zero (Real.real (Complex.realPackage C))))
  ≡ targetPiC
mapComplexPi E
  rewrite preservesPi E
        | preservesZeroR E = refl

mapComplexAdd :
  ∀ {C T}
    (E : RealTranscendentalExtraction C T)
    (x y :
      Complex.ComplexPair
        (Real.real (Complex.realPackage C))) →
  mapComplex E (Complex._+C_ x y)
  ≡ targetAddC (mapComplex E x) (mapComplex E y)
mapComplexAdd E
  (Complex.complex xr xi)
  (Complex.complex yr yi)
  rewrite preservesAddR E xr yr
        | preservesAddR E xi yi = refl

mapComplexSub :
  ∀ {C T}
    (E : RealTranscendentalExtraction C T)
    (x y :
      Complex.ComplexPair
        (Real.real (Complex.realPackage C))) →
  mapComplex E (Complex._-C_ x y)
  ≡ targetSubC (mapComplex E x) (mapComplex E y)
mapComplexSub E
  (Complex.complex xr xi)
  (Complex.complex yr yi)
  rewrite preservesSubR E xr yr
        | preservesSubR E xi yi = refl

mapComplexMul :
  ∀ {C T}
    (E : RealTranscendentalExtraction C T)
    (x y :
      Complex.ComplexPair
        (Real.real (Complex.realPackage C))) →
  mapComplex E (Complex._*C_ x y)
  ≡ targetMulC (mapComplex E x) (mapComplex E y)
mapComplexMul E
  (Complex.complex xr xi)
  (Complex.complex yr yi)
  rewrite preservesSubR E
            (Real._*_ (Real.real (Complex.realPackage C)) xr yr)
            (Real._*_ (Real.real (Complex.realPackage C)) xi yi)
        | preservesMulR E xr yr
        | preservesMulR E xi yi
        | preservesAddR E
            (Real._*_ (Real.real (Complex.realPackage C)) xr yi)
            (Real._*_ (Real.real (Complex.realPackage C)) xi yr)
        | preservesMulR E xr yi
        | preservesMulR E xi yr = refl

------------------------------------------------------------------------
-- Complex exponential preservation follows from the source Cartesian theorem.
------------------------------------------------------------------------

mapComplexExp :
  ∀ {C T}
    (E : RealTranscendentalExtraction C T)
    (z :
      Complex.ComplexPair
        (Real.real (Complex.realPackage C))) →
  mapComplex E
    (Complex.expC (Complex.complexExponential C) z)
  ≡
  targetExpC (mapComplex E z)
mapComplexExp {C} E (Complex.complex x y)
  rewrite Complex.expCartesian
            (Complex.complexExponential C) x y
        | preservesMulR E
            (Real.exp
              (Real.exponential (Complex.realPackage C)) x)
            (Complex.cos (Complex.complexExponential C) y)
        | preservesRealExp E x
        | preservesCos E y
        | preservesMulR E
            (Real.exp
              (Real.exponential (Complex.realPackage C)) x)
            (Complex.sin (Complex.complexExponential C) y)
        | preservesRealExp E x
        | preservesSin E y = refl

------------------------------------------------------------------------
-- Therefore the generic complex extraction is constructed automatically.
------------------------------------------------------------------------

complexExtractionFromReal :
  ∀ {C T} →
  RealTranscendentalExtraction C T →
  Extraction.ComplexExtraction
    C
    (cartesianTargetComplexAlgebra T)
complexExtractionFromReal E =
  record
    { Extraction.mapC = mapComplex E
    ; Extraction.preservesZero = mapComplexZero E
    ; Extraction.preservesOne = mapComplexOne E
    ; Extraction.preservesImaginaryUnit = mapComplexI E
    ; Extraction.preservesPiComplex = mapComplexPi E
    ; Extraction.preservesAdd = mapComplexAdd E
    ; Extraction.preservesSub = mapComplexSub E
    ; Extraction.preservesMul = mapComplexMul E
    ; Extraction.preservesExp = mapComplexExp E
    }

------------------------------------------------------------------------
-- Direct route-B corollaries for the actual q/E4/E6 definitions.
------------------------------------------------------------------------

actualQTransportFromRealExtraction :
  ∀ {C T}
    (E : RealTranscendentalExtraction C T)
    (tau :
      Complex.ComplexPair
        (Real.real (Complex.realPackage C))) →
  Extraction.mapC (complexExtractionFromReal E)
    (Q.qOf C tau)
  ≡
  Extraction.targetQ
    (cartesianTargetComplexAlgebra T)
    (mapComplex E tau)
actualQTransportFromRealExtraction E tau =
  Extraction.mapQOf (complexExtractionFromReal E) tau

actualE4TransportFromRealExtraction :
  ∀ {C T}
    (E : RealTranscendentalExtraction C T)
    (kernel : Q.DivisorPowerKernel)
    (terms : Nat)
    (tau :
      Complex.ComplexPair
        (Real.real (Complex.realPackage C))) →
  Extraction.mapC (complexExtractionFromReal E)
    (Q.e4Truncated C kernel terms tau)
  ≡
  Extraction.targetE4Truncated
    (cartesianTargetComplexAlgebra T)
    kernel
    terms
    (Extraction.targetQ
      (cartesianTargetComplexAlgebra T)
      (mapComplex E tau))
actualE4TransportFromRealExtraction E kernel terms tau =
  Extraction.mapE4TruncatedCanonicalQ
    (complexExtractionFromReal E) kernel terms tau

actualE6TransportFromRealExtraction :
  ∀ {C T}
    (E : RealTranscendentalExtraction C T)
    (kernel : Q.DivisorPowerKernel)
    (terms : Nat)
    (tau :
      Complex.ComplexPair
        (Real.real (Complex.realPackage C))) →
  Extraction.mapC (complexExtractionFromReal E)
    (Q.e6Truncated C kernel terms tau)
  ≡
  Extraction.targetE6Truncated
    (cartesianTargetComplexAlgebra T)
    kernel
    terms
    (Extraction.targetQ
      (cartesianTargetComplexAlgebra T)
      (mapComplex E tau))
actualE6TransportFromRealExtraction E kernel terms tau =
  Extraction.mapE6TruncatedCanonicalQ
    (complexExtractionFromReal E) kernel terms tau

actualDiscriminantNumeratorTransportFromRealExtraction :
  ∀ {C T}
    (E : RealTranscendentalExtraction C T)
    (kernel : Q.DivisorPowerKernel)
    (terms : Nat)
    (tau :
      Complex.ComplexPair
        (Real.real (Complex.realPackage C))) →
  Extraction.mapC (complexExtractionFromReal E)
    (Q.discriminantNumeratorTruncated C kernel terms tau)
  ≡
  Extraction.targetDiscriminantNumeratorTruncated
    (cartesianTargetComplexAlgebra T)
    kernel
    terms
    (Extraction.targetQ
      (cartesianTargetComplexAlgebra T)
      (mapComplex E tau))
actualDiscriminantNumeratorTransportFromRealExtraction E kernel terms tau =
  Extraction.mapDiscriminantNumeratorCanonicalQ
    (complexExtractionFromReal E) kernel terms tau

------------------------------------------------------------------------
-- Frontier.
------------------------------------------------------------------------

record AgdaLeanRealExtractionBoundary : Set where
  constructor agda-lean-real-extraction-boundary
  field
    complexMapDerivedComponentwise : Bool
    complexRingPreservationDerivedFromRealLaws : Bool
    complexExpPreservationDerivedFromCartesianLaw : Bool
    actualQTransportDerived : Bool
    actualE4TransportDerived : Bool
    actualE6TransportDerived : Bool
    actualDiscriminantNumeratorTransportDerived : Bool

    faithfulMapToLeanRealInhabited : Bool
    leanSinCosPiExpCompatibilityInhabited : Bool
    selectedAgdaRealCarrierIdentifiedWithLeanReal : Bool

canonicalAgdaLeanRealExtractionBoundary :
  AgdaLeanRealExtractionBoundary
canonicalAgdaLeanRealExtractionBoundary =
  agda-lean-real-extraction-boundary
    true true true true true true true
    false false false
