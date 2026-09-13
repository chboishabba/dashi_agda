module DASHI.Physics.Closure.NSTriadKNLiveIntegratedDiagonalReducedNormalFormRound557Exact where

------------------------------------------------------------------------
-- ROUND557 / LIVE INTEGRATED R406 DIAGONAL-REDUCED NORMAL FORM
--
-- R556 gives the pointwise identity on the literal live R406 trajectory.
-- R552 proves that R495's minimal integration transport is enough to lift it.
-- No FTC, order, endpoint estimate, or new NS estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _-_; _*_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNIntegratedDiagonalReducedNormalFormRound552Exact as R552
import DASHI.Physics.Closure.NSTriadKNLiveR406DiagonalReducedNormalFormRound556Exact as R556

F : C3.RealField _
F = Rational.rationalRealField

module LiveIntegrated
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Flux = R406.FixedLiveFlux
    Time initialTime integrateTo DerivativeOf
  module Live = R556.LiveReduced
    Time initialTime integrateTo DerivativeOf
  module Int = R552.Integrated Time integrateTo integration

  literalRemainder :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  literalRemainder T R cutoff time =
    Flux.At.weightedRemainder T R cutoff time

  factoredFull :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  factoredFull T R cutoff time =
    Live.At.liveFactoredFull T R cutoff time

  selfGram :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  selfGram T R cutoff time =
    Live.At.liveSelfGram T R cutoff time

  selfFluxTangent :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  selfFluxTangent T R cutoff time =
    Live.At.liveSelfFluxTangent T R cutoff time

  liveIntegratedReducedNormalForm :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    R539.two * integrateTo (literalRemainder T R cutoff) terminal
    ≡
    (integrateTo (factoredFull T R cutoff) terminal
      - integrateTo (selfGram T R cutoff) terminal)
      - integrateTo (selfFluxTangent T R cutoff) terminal
  liveIntegratedReducedNormalForm T R cutoff terminal =
    Int.integratedReducedNormalForm
      (literalRemainder T R cutoff)
      (factoredFull T R cutoff)
      (selfGram T R cutoff)
      (selfFluxTangent T R cutoff)
      (λ time →
        Live.At.twoLiteralR406RemainderIsReducedNormalForm
          T R cutoff time)
      terminal

round557LiveIntegratedNormalFormClosed : Bool
round557LiveIntegratedNormalFormClosed = true

round557UsesOnlyR495Transport : Bool
round557UsesOnlyR495Transport = true

round557FTCIntroduced : Bool
round557FTCIntroduced = false

round557FactoredFullSpacetimeBoundClosed : Bool
round557FactoredFullSpacetimeBoundClosed = false

round557ClayPromotion : Bool
round557ClayPromotion = false

round557LiveIntegratedNormalFormClosedIsTrue :
  round557LiveIntegratedNormalFormClosed ≡ true
round557LiveIntegratedNormalFormClosedIsTrue = refl

round557ClayPromotionIsFalse : round557ClayPromotion ≡ false
round557ClayPromotionIsFalse = refl
