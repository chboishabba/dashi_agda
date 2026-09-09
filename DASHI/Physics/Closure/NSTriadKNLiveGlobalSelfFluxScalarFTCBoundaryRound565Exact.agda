module DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxScalarFTCBoundaryRound565Exact where

------------------------------------------------------------------------
-- ROUND565 / LIVE GLOBAL SELF-FLUX DERIVATIVE -> ORDINARY SCALAR FTC SOCKET
--
-- R564 has already constructed the exact derivative relation
--
--   ScalarDerivativeOf(globalSelfFlux, globalSelfFluxTangent)
--
-- on the literal R408/R240 trajectory and the canonical nonzero output list.
-- Nothing Navier--Stokes-specific remains in the endpoint step.  The only
-- missing authority is the ordinary scalar fundamental theorem of calculus
-- for the SAME derivative relation and SAME integrateTo operator.
--
-- R393 contains the desired endpoint equality as a record FIELD; it does not
-- manufacture that field from ScalarDerivativeOf.  Likewise the Marx exterior
-- calculus uses a different finite-factorisation derivative semantics.  This
-- owner therefore keeps the last analysis receipt explicit and weak: one rule
-- from the already-selected ScalarDerivativeOf to the already-selected
-- integrateTo endpoint identity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _-_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxDerivativeRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

record ScalarFTCAuthority565
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set) : Set₁ where
  field
    derivativeIntegratesToEndpoint565 :
      ∀ {f df} →
      ScalarDerivativeOf f df →
      (terminal : Time) →
      integrateTo df terminal ≡ f terminal - f initialTime

open ScalarFTCAuthority565 public

module LiveGlobalFTC
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) →
      (Time → ℚ) → Set)
    (projectedCrossCalculus :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo VectorDerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo VectorDerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo VectorDerivativeOf D))
    (cutoff : Nat)
    (FTC : ScalarFTCAuthority565
      Time initialTime integrateTo ScalarDerivativeOf) where

  module Global = R564.LiveGlobalDerivative
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCrossCalculus vectorAlgebra hermitianCalculus
    constantCalculus scalarAlgebra D R cutoff

  literalGlobalSelfFluxEndpointFTC565 :
    (terminal : Time) →
    integrateTo Global.globalSelfFluxTangent terminal
    ≡ Global.globalSelfFlux terminal - Global.globalSelfFlux initialTime
  literalGlobalSelfFluxEndpointFTC565 terminal =
    derivativeIntegratesToEndpoint565 FTC
      Global.literalGlobalSelfFluxDerivative terminal

------------------------------------------------------------------------
-- Proof-search boundary.
------------------------------------------------------------------------

data R565Residual : Set where
  missingConcreteScalarFTCAuthority565 : R565Residual
  missingFactoredFullSpacetimeBound565 : R565Residual
  literalLeafAFromNormalFormClosed565 : R565Residual

currentR565Residual : R565Residual
currentR565Residual = missingConcreteScalarFTCAuthority565

round565LiteralGlobalSelfFluxDerivativeReused : Bool
round565LiteralGlobalSelfFluxDerivativeReused =
  R564.round564GlobalSelfFluxDerivativeClosed

round565IntroducesNewDerivativeInterface : Bool
round565IntroducesNewDerivativeInterface = false

round565R393FieldMistakenForFTCDerivation : Bool
round565R393FieldMistakenForFTCDerivation = false

round565ConcreteScalarFTCAuthorityClosed : Bool
round565ConcreteScalarFTCAuthorityClosed = false

round565EndpointIdentityClosedGivenScalarFTC : Bool
round565EndpointIdentityClosedGivenScalarFTC = true

round565FactoredFullSpacetimeBoundClosed : Bool
round565FactoredFullSpacetimeBoundClosed = false

round565CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round565CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round565ClayPromotion : Bool
round565ClayPromotion = false

round565EndpointIdentityClosedGivenScalarFTCIsTrue :
  round565EndpointIdentityClosedGivenScalarFTC ≡ true
round565EndpointIdentityClosedGivenScalarFTCIsTrue = refl

round565ConcreteScalarFTCAuthorityClosedIsFalse :
  round565ConcreteScalarFTCAuthorityClosed ≡ false
round565ConcreteScalarFTCAuthorityClosedIsFalse = refl

round565ClayPromotionIsFalse : round565ClayPromotion ≡ false
round565ClayPromotionIsFalse = refl
