module DASHI.Physics.Closure.NSTriadKNR290HermitianG2StateDifferenceExact where

------------------------------------------------------------------------
-- B / G2 SAME-OBJECT RECUT: HERMITIAN STATE DIFFERENCE
--
-- The unresolved R571/R290 state-side quantity is
--
--   g_+ - g_-,
--   g(X;D) = Re <X,D>.
--
-- This owner proves on the literal rational C^3 carrier that this is EXACTLY
-- one Hermitian test of the physical vector difference:
--
--   g(X_+;D) - g(X_-;D)
--     = g(X_+ - X_-; D).
--
-- Therefore G2 is no longer a mysterious scalar-state regularity condition.
-- It is precisely a vector path-difference problem on the same X+/X- samples.
-- The local Hermitian Young theorem then gives a checked non-square-root
-- magnitude envelope.  The still-open hard step is to make
--
--   ||X_+ - X_-||^2
--
-- inherit the required displacement/gradient gain from the physical path
-- geometry without reintroducing a fibre-cardinality factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _-_; _≤_; ∣_∣)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as G0
import DASHI.Physics.Closure.NSTriadKNRationalHermitianYoungRound579Exact as R579

F = G0.Weld.F

hermitianStateDifferenceExact :
  (XPlus XMinus D : C3.Complex3 F) →
  G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D
  ≡
  G0.hermitianScalar (C3.complex3Subtract XPlus XMinus) D
hermitianStateDifferenceExact
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

hermitianStateDifferenceMagnitudeBound :
  (XPlus XMinus D : C3.Complex3 F) →
  ∣ G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D ∣
  ≤
  L2.complex3NormSquared (C3.complex3Subtract XPlus XMinus)
  + L2.complex3NormSquared D
hermitianStateDifferenceMagnitudeBound XPlus XMinus D =
  let
    exact = hermitianStateDifferenceExact XPlus XMinus D
    local =
      R579.rationalRealHermitianYoung
        (C3.complex3Subtract XPlus XMinus) D
  in
  subst
    (λ selected →
      ∣ selected ∣
      ≤
      L2.complex3NormSquared (C3.complex3Subtract XPlus XMinus)
      + L2.complex3NormSquared D)
    (sym exact)
    local
  where
  open import Relation.Binary.PropositionalEquality using (subst; sym)

record PhysicalG2VectorDifferencePayment
    (XPlus XMinus : C3.Complex3 F)
    (displacement gradientEnvelope : ℚ) : Set where
  field
    vectorDifferencePayment :
      L2.complex3NormSquared (C3.complex3Subtract XPlus XMinus)
      ≤ displacement * gradientEnvelope

open PhysicalG2VectorDifferencePayment public

------------------------------------------------------------------------
-- The exact scalar weld is closed.  The path/gradient producer is deliberately
-- kept separate because the existing finite-path theorem is a donor, not yet
-- the literal X+/X- physical same-object theorem.
------------------------------------------------------------------------

r290HermitianG2ScalarToVectorDifferenceWeldClosed : Bool
r290HermitianG2ScalarToVectorDifferenceWeldClosed = true

r290HermitianG2LocalMagnitudeBoundClosed : Bool
r290HermitianG2LocalMagnitudeBoundClosed = true

r290PhysicalVectorDifferenceToPathGradientClosedHere : Bool
r290PhysicalVectorDifferenceToPathGradientClosedHere = false

r290CutoffUniformG2ClosedHere : Bool
r290CutoffUniformG2ClosedHere = false

signedSecondMomentAggregationClosedHere : Bool
signedSecondMomentAggregationClosedHere = false

clayPromotion : Bool
clayPromotion = false

r290HermitianG2ScalarToVectorDifferenceWeldClosedIsTrue :
  r290HermitianG2ScalarToVectorDifferenceWeldClosed ≡ true
r290HermitianG2ScalarToVectorDifferenceWeldClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
