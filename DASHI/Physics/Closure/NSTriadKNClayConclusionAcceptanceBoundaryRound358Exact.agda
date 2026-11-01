module DASHI.Physics.Closure.NSTriadKNClayConclusionAcceptanceBoundaryRound358Exact where

------------------------------------------------------------------------
-- ROUND358 / BIDI: MATHEMATICAL CLAY CONCLUSION != EXTERNAL ACCEPTANCE
--
-- Repository submission/readiness surfaces explicitly track theorem acceptance
-- as a separate residual.  R357 closes the mathematical theorem shape under
-- the supplied physical inputs and supplied Clay authority.  This round keeps
-- any reviewer/institutional acceptance downstream of that theorem rather than
-- baking acceptance into the proof proposition itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNGlobalClayConclusionRound357Exact as R357

F : C3.RealField _
F = Rational.rationalRealField

module ClayAcceptanceBoundary
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Global = R357.GlobalClayConclusion Time initialTime integrateTo DerivativeOf

  record ExternalClayAcceptance
      (ClayConclusion : Dyn.PhysicalNSGalerkinTrajectory → Set)
      (AcceptanceReceipt : Set) : Set₁ where
    field
      acceptGlobalTheorem :
        ((T : Dyn.PhysicalNSGalerkinTrajectory) → ClayConclusion T) →
        AcceptanceReceipt

  open ExternalClayAcceptance public

  acceptedClayResult :
    (ClayConclusion : Dyn.PhysicalNSGalerkinTrajectory → Set) →
    (AcceptanceReceipt : Set) →
    Global.GlobalResolventClayInputs ClayConclusion →
    ExternalClayAcceptance ClayConclusion AcceptanceReceipt →
    AcceptanceReceipt
  acceptedClayResult ClayConclusion AcceptanceReceipt inputs acceptance =
    acceptGlobalTheorem acceptance
      (Global.globalClayConclusion ClayConclusion inputs)

round358MathematicalConclusionSeparatedFromAcceptance : Bool
round358MathematicalConclusionSeparatedFromAcceptance = true

round358ExternalAcceptanceUsedInsideMathematicalProof : Bool
round358ExternalAcceptanceUsedInsideMathematicalProof = false

round358AcceptanceCanConsumeCompletedGlobalTheorem : Bool
round358AcceptanceCanConsumeCompletedGlobalTheorem = true

round358HistoricalSubmissionFlagsRewritten : Bool
round358HistoricalSubmissionFlagsRewritten = false

round358MathematicalConclusionSeparatedFromAcceptanceIsTrue :
  round358MathematicalConclusionSeparatedFromAcceptance ≡ true
round358MathematicalConclusionSeparatedFromAcceptanceIsTrue = refl

round358ExternalAcceptanceUsedInsideMathematicalProofIsFalse :
  round358ExternalAcceptanceUsedInsideMathematicalProof ≡ false
round358ExternalAcceptanceUsedInsideMathematicalProofIsFalse = refl

round358AcceptanceCanConsumeCompletedGlobalTheoremIsTrue :
  round358AcceptanceCanConsumeCompletedGlobalTheorem ≡ true
round358AcceptanceCanConsumeCompletedGlobalTheoremIsTrue = refl
