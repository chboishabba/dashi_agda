module DASHI.Physics.Closure.NSTriadKNCoherentWorkHermitianScalarizationExact where

------------------------------------------------------------------------
-- PERIODIC B / COHERENT WORK DIFFERENCE = TWO HERMITIAN STATE DIFFERENCES
--
-- The covariance owner uses
--
--   work_M(X) = 2 Re <M,X>.
--
-- The R571 state envelope uses
--
--   g_D(X) = Re <X,D>.
--
-- Real-Hermitian symmetry identifies these on the SAME vectors.  Taking
-- D = M gives
--
--   work_M(X) = 2 g_M(X),
--
-- and therefore
--
--   work_M(X_alpha) - work_M(X_beta)
--     = 2 (g_M(X_alpha) - g_M(X_beta)).
--
-- This is the exact same-object scalarization needed to feed the literal
-- fixed-output coherent covariance into the physical centered-covariance M2
-- sample.  No estimate or absolute value enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as G0
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287

F = G0.Weld.F

coherentWorkIsTwoHermitianScalar :
  (mixed value : C3.Complex3 F) →
  Work.coherentWork mixed value
  ≡ Work.two * G0.hermitianScalar value mixed
coherentWorkIsTwoHermitianScalar mixed value =
  trans
    (cong (Work.two *_) (R287.realHermitianCrossSymmetric mixed value))
    refl

coherentWorkDifferenceIsTwoHermitianDifference :
  (mixed left right : C3.Complex3 F) →
  Work.coherentWork mixed left - Work.coherentWork mixed right
  ≡ Work.two
      * (G0.hermitianScalar left mixed - G0.hermitianScalar right mixed)
coherentWorkDifferenceIsTwoHermitianDifference mixed left right =
  trans
    (cong₂ _-_
      (coherentWorkIsTwoHermitianScalar mixed left)
      (coherentWorkIsTwoHermitianScalar mixed right))
    (solve
      ( G0.hermitianScalar left mixed
      ∷ G0.hermitianScalar right mixed
      ∷ []))

coherentWorkScalarizationClosed : Bool
coherentWorkScalarizationClosed = true

coherentWorkScalarizationIntroducesEstimate : Bool
coherentWorkScalarizationIntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false
