{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR571HermitianStateDifferenceRound613Exact where

------------------------------------------------------------------------
-- ROUND613 / R571 G2 SCALAR DIFFERENCE = ONE VECTOR-DIFFERENCE PAIRING
--
-- G0' scalarizes a literal rational C^3 sample X against the spectator D by
--
--   g(X;D) = Re <X,D>.
--
-- The state-side G2 term in the paired second-moment carrier is
--
--   |g(X+;D) - g(X-;D)|.
--
-- On the exact rational C^3 carrier this is definitionally finite-dimensional
-- linear algebra:
--
--   g(X+;D) - g(X-;D)
--     = Re <X+ - X-, D>.
--
-- Thus G2 has no independent scalarization debt.  The remaining physical
-- theorem is only the displacement/gradient control of the literal vector
-- difference X+ - X-.  No norm inequality or path estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _-_; ∣_∣)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as G0

F = G0.Weld.F

hermitianStateDifferenceExact :
  (XPlus XMinus D : C3.Complex3 F) →
  G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D
  ≡
  G0.hermitianScalar (C3.complex3Subtract XPlus XMinus) D
hermitianStateDifferenceExact
    (C3.complex3
      (C3.complex px pxi) (C3.complex py pyi) (C3.complex pz pzi))
    (C3.complex3
      (C3.complex mx mxi) (C3.complex my myi) (C3.complex mz mzi))
    (C3.complex3
      (C3.complex dx dxi) (C3.complex dy dyi) (C3.complex dz dzi)) =
  solve
    ( px ∷ pxi ∷ py ∷ pyi ∷ pz ∷ pzi
    ∷ mx ∷ mxi ∷ my ∷ myi ∷ mz ∷ mzi
    ∷ dx ∷ dxi ∷ dy ∷ dyi ∷ dz ∷ dzi
    ∷ [])

hermitianStateDifferenceMagnitudeExact :
  (XPlus XMinus D : C3.Complex3 F) →
  ∣ G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D ∣
  ≡
  ∣ G0.hermitianScalar (C3.complex3Subtract XPlus XMinus) D ∣
hermitianStateDifferenceMagnitudeExact XPlus XMinus D =
  cong ∣_∣ (hermitianStateDifferenceExact XPlus XMinus D)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round613G2ScalarDifferenceSameObjectClosed : Bool
round613G2ScalarDifferenceSameObjectClosed = true

round613G2ReducedToLiteralVectorDifference : Bool
round613G2ReducedToLiteralVectorDifference = true

round613PhysicalPathGradientEstimateClosed : Bool
round613PhysicalPathGradientEstimateClosed = false

round613CutoffUniformG2EnvelopeClosed : Bool
round613CutoffUniformG2EnvelopeClosed = false

round613IntroducesAnalyticEstimate : Bool
round613IntroducesAnalyticEstimate = false

round613G2ScalarDifferenceSameObjectClosedIsTrue :
  round613G2ScalarDifferenceSameObjectClosed ≡ true
round613G2ScalarDifferenceSameObjectClosedIsTrue = refl

round613G2ReducedToLiteralVectorDifferenceIsTrue :
  round613G2ReducedToLiteralVectorDifference ≡ true
round613G2ReducedToLiteralVectorDifferenceIsTrue = refl

round613PhysicalPathGradientEstimateClosedIsFalse :
  round613PhysicalPathGradientEstimateClosed ≡ false
round613PhysicalPathGradientEstimateClosedIsFalse = refl

round613IntroducesAnalyticEstimateIsFalse :
  round613IntroducesAnalyticEstimate ≡ false
round613IntroducesAnalyticEstimateIsFalse = refl
