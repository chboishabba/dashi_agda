module DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact where

------------------------------------------------------------------------
-- ROUND500 / INTEGRATE THE DIRECT NONSEPARABLE COMPANION
--
-- R499 proves pointwise on the literal live trajectory
--
--   R406.weightedRemainder(N,t) = 4 * C_direct(N,t).
--
-- The dynamics keeps `integrateTo` abstract, so this file takes only R495's
-- standard transport authority as a producer premise.  No scalar-linearity law
-- is assumed: multiplication by four is derived from congruence + repeated
-- finite additivity.
--
-- Result:
--
--   literalR406RemainderIntegral(N,T)
--     = 4 * integrateTo(C_direct(N,-),T).
--
-- This is a representation theorem only.  It introduces no Navier--Stokes
-- estimate and no Laplace/heat factorization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossToR410Round415Exact as R415
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNDirectResolventTrajectoryCompanionRound499Exact as R499

F : C3.RealField _
F = Rational.rationalRealField

module IntegratedDirect
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
  module Heat = R415.SignedHeatCross
    Time initialTime integrateTo DerivativeOf
  module Direct = R499.DirectTrajectory
    Time initialTime integrateTo DerivativeOf

  integratedDirectCompanion :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedDirectCompanion T R cutoff terminal =
    integrateTo
      (Direct.instantaneousDirectCompanion T R cutoff)
      terminal

  integrateFour :
    (f : Time → ℚ) →
    (terminal : Time) →
    integrateTo (λ t → R299.four * f t) terminal
    ≡ R299.four * integrateTo f terminal
  integrateFour f terminal =
    let
      twice : Time → ℚ
      twice t = f t + f t
      thrice : Time → ℚ
      thrice t = f t + twice t
      fourCopies : Time → ℚ
      fourCopies t = f t + thrice t

      fourIsCopies :
        (t : Time) →
        R299.four * f t ≡ fourCopies t
      fourIsCopies t = solve (f t ∷ [])

      scaleToCopies :
        integrateTo (λ t → R299.four * f t) terminal
        ≡ integrateTo fourCopies terminal
      scaleToCopies =
        R495.integrateCongruent integration
          (λ t → R299.four * f t)
          fourCopies
          fourIsCopies
          terminal

      twiceIntegrated :
        integrateTo twice terminal
        ≡ integrateTo f terminal + integrateTo f terminal
      twiceIntegrated = R495.integrateAdd integration f f terminal

      thriceIntegrated :
        integrateTo thrice terminal
        ≡ integrateTo f terminal
            + (integrateTo f terminal + integrateTo f terminal)
      thriceIntegrated =
        trans
          (R495.integrateAdd integration f twice terminal)
          (cong (integrateTo f terminal +_) twiceIntegrated)

      fourCopiesIntegrated :
        integrateTo fourCopies terminal
        ≡ integrateTo f terminal
            + (integrateTo f terminal
              + (integrateTo f terminal + integrateTo f terminal))
      fourCopiesIntegrated =
        trans
          (R495.integrateAdd integration f thrice terminal)
          (cong (integrateTo f terminal +_) thriceIntegrated)
    in
    trans scaleToCopies
      (trans fourCopiesIntegrated (solve (integrateTo f terminal ∷ [])))

  literalR406IntegralIsFourIntegratedDirectCompanion :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    Heat.literalRemainderIntegral T R cutoff terminal
    ≡ R299.four * integratedDirectCompanion T R cutoff terminal
  literalR406IntegralIsFourIntegratedDirectCompanion
      T R cutoff terminal =
    let
      remainder : Time → ℚ
      remainder t = Direct.Flux.At.weightedRemainder T R cutoff t
      companion : Time → ℚ
      companion = Direct.instantaneousDirectCompanion T R cutoff

      pointwise :
        (t : Time) →
        remainder t ≡ R299.four * companion t
      pointwise t =
        Direct.literalInstantaneousRemainderIsFourDirectCompanion
          T R cutoff t

      transport :
        integrateTo remainder terminal
        ≡ integrateTo (λ t → R299.four * companion t) terminal
      transport =
        R495.integrateCongruent integration
          remainder
          (λ t → R299.four * companion t)
          pointwise
          terminal
    in
    trans transport (integrateFour companion terminal)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

round500PointwiseR499SameObjectReused : Bool
round500PointwiseR499SameObjectReused = true

round500OnlyStandardIntegrationTransportUsed : Bool
round500OnlyStandardIntegrationTransportUsed = true

round500ScalarLinearityAssumed : Bool
round500ScalarLinearityAssumed = false

round500LaplaceRequired : Bool
round500LaplaceRequired = false

round500IntegratedDirectCompanionWeldClosedModuloIntegrationAuthority : Bool
round500IntegratedDirectCompanionWeldClosedModuloIntegrationAuthority = true

round500SignedSpacetimeEstimateClosed : Bool
round500SignedSpacetimeEstimateClosed = false

round500ClayPromotion : Bool
round500ClayPromotion = false

round500IntegratedDirectCompanionWeldClosedModuloIntegrationAuthorityIsTrue :
  round500IntegratedDirectCompanionWeldClosedModuloIntegrationAuthority ≡ true
round500IntegratedDirectCompanionWeldClosedModuloIntegrationAuthorityIsTrue = refl

round500ScalarLinearityAssumedIsFalse :
  round500ScalarLinearityAssumed ≡ false
round500ScalarLinearityAssumedIsFalse = refl

round500ClayPromotionIsFalse : round500ClayPromotion ≡ false
round500ClayPromotionIsFalse = refl
