module DASHI.Physics.Closure.NSTriadKNR571HermitianStateDifferenceEnvelopeExact where

------------------------------------------------------------------------
-- R571 GATE-A / EXACT HERMITIAN G2 SQUARED REDUCTION
--
-- On the literal rational C3 carrier used by G0', the scalar state values are
--
--   g(X;D) = Re <X,D>.
--
-- Hence
--
--   g(X+) - g(X-) = Re <X+ - X-, D>,
--
-- and exact rational Hermitian Cauchy gives the radical-free estimate
--
--   (g+ - g-)^2
--     <= ||X+ - X-||^2 ||D||^2.
--
-- This pays the scalarization part of G2 on the SAME G0' carrier.  It does not
-- yet bound the vector state difference by physical displacement; that is now
-- the sole state-variation analytic leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNRationalComplex3HermitianCauchyRound74Exact as Cauchy
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as G0

F : C3.RealField _
F = Rational.rationalRealField

stateDifference :
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
stateDifference = C3.complex3Subtract

------------------------------------------------------------------------
-- 1. Same-object scalar difference.
------------------------------------------------------------------------

hermitianScalarDifferenceExact :
  (XPlus XMinus D : C3.Complex3 F) →
  G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D
  ≡ G0.hermitianScalar (stateDifference XPlus XMinus) D
hermitianScalarDifferenceExact
    (C3.complex3
      (C3.complex pxr pxi) (C3.complex pyr pyi) (C3.complex pzr pzi))
    (C3.complex3
      (C3.complex mxr mxi) (C3.complex myr myi) (C3.complex mzr mzi))
    (C3.complex3
      (C3.complex dxr dxi) (C3.complex dyr dyi) (C3.complex dzr dzi)) =
  solve
    ( pxr ∷ pxi ∷ pyr ∷ pyi ∷ pzr ∷ pzi
    ∷ mxr ∷ mxi ∷ myr ∷ myi ∷ mzr ∷ mzi
    ∷ dxr ∷ dxi ∷ dyr ∷ dyi ∷ dzr ∷ dzi
    ∷ [])

realHermitianCrossIsPairingReal :
  (X D : C3.Complex3 F) →
  R179.realHermitianCross X D
  ≡ C3.real (C3.hermitianPairing3 X D)
realHermitianCrossIsPairingReal
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi))
    (C3.complex3
      (C3.complex dr di) (C3.complex er ei) (C3.complex fr fi)) =
  solve (xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ dr ∷ di ∷ er ∷ ei ∷ fr ∷ fi ∷ [])

------------------------------------------------------------------------
-- 2. Real-part square is below the full complex modulus square.
------------------------------------------------------------------------

realPartSquareBelowModulusSquared :
  (z : C3.Complex F) →
  Rational.square (C3.real z)
  ≤ L2.complexModulusSquared z
realPartSquareBelowModulusSquared (C3.complex real imaginary) =
  let
    imaginaryNN : 0ℚ ≤ Rational.square imaginary
    imaginaryNN = Rational.squareNonnegative imaginary

    addImaginary :
      Rational.square real
      ≤ Rational.square real + Rational.square imaginary
    addImaginary =
      subst
        (λ lower →
          lower ≤ Rational.square real + Rational.square imaginary)
        (ℚP.+-identityʳ (Rational.square real))
        (ℚP.+-monoʳ-≤ (Rational.square real) imaginaryNN)
  in
  addImaginary

------------------------------------------------------------------------
-- 3. Exact squared G2 scalarization.
------------------------------------------------------------------------

hermitianScalarDifferenceSquaredBelowStateDifferenceMass :
  (XPlus XMinus D : C3.Complex3 F) →
  Rational.square
    (G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D)
  ≤
  L2.complex3NormSquared (stateDifference XPlus XMinus)
    * L2.complex3NormSquared D
hermitianScalarDifferenceSquaredBelowStateDifferenceMass
    XPlus XMinus D =
  let
    delta = stateDifference XPlus XMinus

    scalarIdentity :
      G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D
      ≡ C3.real (C3.hermitianPairing3 delta D)
    scalarIdentity =
      trans
        (hermitianScalarDifferenceExact XPlus XMinus D)
        (realHermitianCrossIsPairingReal delta D)

    realBelowComplex :
      Rational.square
        (C3.real (C3.hermitianPairing3 delta D))
      ≤
      L2.complexModulusSquared (C3.hermitianPairing3 delta D)
    realBelowComplex =
      realPartSquareBelowModulusSquared
        (C3.hermitianPairing3 delta D)

    fullCauchy :
      L2.complexModulusSquared (C3.hermitianPairing3 delta D)
      ≤
      L2.complex3NormSquared delta * L2.complex3NormSquared D
    fullCauchy =
      Cauchy.rationalComplex3HermitianCauchy delta D
  in
  subst
    (λ scalar →
      Rational.square scalar
      ≤ L2.complex3NormSquared delta * L2.complex3NormSquared D)
    (sym scalarIdentity)
    (ℚP.≤-trans realBelowComplex fullCauchy)

------------------------------------------------------------------------
-- 4. If the literal vector difference has a displacement-squared envelope,
--    the Hermitian scalar difference inherits it with only spectator mass.
------------------------------------------------------------------------

record VectorStateDifferenceSquaredEnvelope
    (XPlus XMinus : C3.Complex3 F) : Set where
  field
    displacementSquared gradientEnergy : ℚ
    displacementSquaredNonnegative : 0ℚ ≤ displacementSquared
    gradientEnergyNonnegative : 0ℚ ≤ gradientEnergy

    stateDifferenceBound :
      L2.complex3NormSquared (stateDifference XPlus XMinus)
      ≤ displacementSquared * gradientEnergy

open VectorStateDifferenceSquaredEnvelope public

hermitianG2SquaredFromVectorEnvelope :
  (XPlus XMinus D : C3.Complex3 F) →
  (envelope : VectorStateDifferenceSquaredEnvelope XPlus XMinus) →
  Rational.square
    (G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D)
  ≤
  displacementSquared envelope
    * (gradientEnergy envelope * L2.complex3NormSquared D)
hermitianG2SquaredFromVectorEnvelope XPlus XMinus D envelope =
  let
    deltaMass =
      L2.complex3NormSquared (stateDifference XPlus XMinus)
    spectatorMass = L2.complex3NormSquared D
    vectorBudget =
      displacementSquared envelope * gradientEnergy envelope

    spectatorNN : 0ℚ ≤ spectatorMass
    spectatorNN = Separation.complex3NormSquaredNonnegative D

    scaledVectorBudget :
      deltaMass * spectatorMass
      ≤ vectorBudget * spectatorMass
    scaledVectorBudget =
      Rational.nonnegativeProductMonotone
        (Separation.complex3NormSquaredNonnegative
          (stateDifference XPlus XMinus))
        spectatorNN
        (Rational.addNonnegative
          0ℚ≤displacementGradient
          ℚP.≤-refl)
        spectatorNN
        (stateDifferenceBound envelope)
        ℚP.≤-refl
      where
      0ℚ≤displacementGradient :
        0ℚ ≤ vectorBudget
      0ℚ≤displacementGradient =
        let
          instance dNN =
            Data.Rational.Base.nonNegative
              (displacementSquaredNonnegative envelope)
          instance gNN =
            Data.Rational.Base.nonNegative
              (gradientEnergyNonnegative envelope)
        in
        ℚP.nonNegative⁻¹
          (displacementSquared envelope * gradientEnergy envelope)

    base =
      hermitianScalarDifferenceSquaredBelowStateDifferenceMass
        XPlus XMinus D
  in
  subst
    (λ rhs →
      Rational.square
        (G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D)
      ≤ rhs)
    (solve
      ( displacementSquared envelope
      ∷ gradientEnergy envelope
      ∷ spectatorMass
      ∷ []))
    (ℚP.≤-trans base scaledVectorBudget)

------------------------------------------------------------------------
-- 5. Status.
------------------------------------------------------------------------

r571HermitianScalarDifferenceSameObjectClosed : Bool
r571HermitianScalarDifferenceSameObjectClosed = true

r571HermitianG2SquaredScalarizationClosed : Bool
r571HermitianG2SquaredScalarizationClosed = true

r571VectorStateDifferencePhysicalGradientClosedHere : Bool
r571VectorStateDifferencePhysicalGradientClosedHere = false

r571FullLinearG2EnvelopeClosedHere : Bool
r571FullLinearG2EnvelopeClosedHere = false

r571HermitianG2SquaredScalarizationClosedIsTrue :
  r571HermitianG2SquaredScalarizationClosed ≡ true
r571HermitianG2SquaredScalarizationClosedIsTrue = refl

r571VectorStateDifferencePhysicalGradientClosedHereIsFalse :
  r571VectorStateDifferencePhysicalGradientClosedHere ≡ false
r571VectorStateDifferencePhysicalGradientClosedHereIsFalse = refl
