module DASHI.Moonshine.JInvariantConstructedComplexKleinJBackendExact where

------------------------------------------------------------------------
-- CONSTRUCTED-COMPLEX INSTANTIATION OF PROOF-RELEVANT KLEIN-j
--
-- This is the literal bridge from DASHI.Analysis.ConcreteComplex /
-- OrdinaryComplexPolar's proof-relevant complex field into the Klein-j
-- construction.  The only analytic inputs left abstract here are the actual
-- g2/Delta functions and proof that Delta is nonzero on the chosen point
-- carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantProofRelevantKleinJExact as Klein

------------------------------------------------------------------------
-- Point may be the upper half-plane itself or a more strongly certified chart.
-- tau embeds it into the concrete complex carrier.
------------------------------------------------------------------------

record ConstructedComplexKleinData
  (C : Complex.ConstructedComplexPackage)
  (D : Polar.RealDivisionAndSquareRoot
        (Real.real (Complex.realPackage C)))
  (F : Polar.ComplexFieldAuthority
        (Real.real (Complex.realPackage C)) D) : Set₁ where
  private
    R = Real.real (Complex.realPackage C)
  field
    Point : Set
    tau : Point → Complex.ComplexPair R

    g2 : Point → Complex.ComplexPair R
    delta : Point → Complex.ComplexPair R
    deltaNonzero :
      (z : Point) → Polar.NonzeroC F (delta z)

open ConstructedComplexKleinData public

cubeC :
  ∀ {R : Real.ConstructedOrderedCompleteReal} →
  Complex.ComplexPair R → Complex.ComplexPair R
cubeC z = Complex._*C_ (Complex._*C_ z z) z

quotientC :
  ∀ {R : Real.ConstructedOrderedCompleteReal}
    {D : Polar.RealDivisionAndSquareRoot R}
    (F : Polar.ComplexFieldAuthority R D) →
    (numerator denominator : Complex.ComplexPair R) →
    Polar.NonzeroC F denominator →
    Complex.ComplexPair R
quotientC F numerator denominator nz =
  Complex._*C_ numerator (Polar.inverseC F denominator nz)

constructedComplexKleinJ :
  (C : Complex.ConstructedComplexPackage) →
  (D : Polar.RealDivisionAndSquareRoot
        (Real.real (Complex.realPackage C))) →
  (F : Polar.ComplexFieldAuthority
        (Real.real (Complex.realPackage C)) D) →
  ConstructedComplexKleinData C D F →
  Klein.ProofRelevantKleinJAlgebra
constructedComplexKleinJ C D F data =
  Klein.proof-relevant-klein-j-algebra
    (Point data)
    (Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (g2 data)
    (delta data)
    cubeC
    (Polar.NonzeroC F)
    (deltaNonzero data)
    (quotientC F)

------------------------------------------------------------------------
-- The construction now genuinely uses the repo's concrete complex inverse.
------------------------------------------------------------------------

record ConstructedComplexKleinFrontier : Set where
  constructor constructed-complex-klein-frontier
  field
    concreteComplexCarrierUsed : Bool
    proofRelevantInverseUsed : Bool
    deltaNonzeroRequiredPerPoint : Bool
    e4e6QSeriesAlreadyAttached : Bool
    upperHalfPlaneDeltaNonvanishingAlreadyProved : Bool
    principalArgumentAlreadyAttached : Bool

canonicalConstructedComplexKleinFrontier : ConstructedComplexKleinFrontier
canonicalConstructedComplexKleinFrontier =
  constructed-complex-klein-frontier
    true true true false false false
