module DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact where

------------------------------------------------------------------------
-- ROUND564 / LITERAL SELF-FLUX DERIVATIVE -> ENDPOINT FTC, FAIL-CLOSED
--
-- R563 now constructs the exact scalar derivative relation for the literal
-- time-indexed self-flux on one physical output fibre.  R393's temporal record
-- contains the endpoint fundamental theorem as a FIELD; it does not derive that
-- field from a derivative relation.  Therefore the remaining analytic authority
-- must stay explicit.
--
-- The weakest reusable producer is the ordinary scalar FTC schema
--
--   ScalarDerivativeOf f df
--     -> integrateTo df T = f(T) - f(initialTime).
--
-- Given that authority, R563 immediately yields the desired endpoint identity
-- for the exact self-flux carrier.  No new Navier--Stokes estimate, alternate
-- flux, or alternate integration functional is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _-_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNSelfPairFixedResolventTrajectoryRound561Exact as R561
import DASHI.Physics.Closure.NSTriadKNLiteralSelfFluxFiniteFamilyRound563Exact as R563
import DASHI.Physics.Closure.NSTriadKNLiteralR378TemporalIntegrationBoundaryRound393Exact as R393
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

record ScalarFundamentalTheorem564
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set) : Set₁ where
  field
    scalarEndpointFTC564 :
      ∀ {f df} →
      ScalarDerivativeOf f df →
      (terminal : Time) →
      integrateTo df terminal ≡ f terminal - f initialTime

open ScalarFundamentalTheorem564 public

module LiteralSelfFluxFTC
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross : R426.ProjectedCrossDerivativeCalculus Time DerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time DerivativeOf)
    (hermitianCalculus : R417.HermitianDerivativeCalculus
      Time DerivativeOf ScalarDerivativeOf)
    (scalarScaleCalculus : R416.ScalarConstantDerivativeCalculus
      Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra : R412.ScalarDerivativeAlgebra
      Time ScalarDerivativeOf)
    (FTC : ScalarFundamentalTheorem564
      Time initialTime integrateTo ScalarDerivativeOf) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Fixed = R561.FixedSelfPair
    Time initialTime integrateTo DerivativeOf
  module Self = R563.LiteralFixedOutputSelfFlux
    Time initialTime integrateTo DerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra hermitianCalculus
    scalarScaleCalculus scalarDerivativeAlgebra

  literalSelfFluxEndpointFTC564 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (Fixed.trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (terminal : Time) →
    integrateTo
      (Self.literalSelfFluxTangent563
        D R S cutoff output outputNonzero)
      terminal
    ≡
    Self.literalSelfFlux563 D R S cutoff output outputNonzero terminal
      - Self.literalSelfFlux563 D R S cutoff output outputNonzero initialTime
  literalSelfFluxEndpointFTC564
      D R S cutoff output outputNonzero terminal =
    scalarEndpointFTC564 FTC
      (Self.literalSelfFluxDerivative563
        D R S cutoff output outputNonzero)
      terminal

------------------------------------------------------------------------
-- R393 parity: the equality above is the exact content carried by R393's
-- `offDiagonalFundamentalTheorem` after same-object identification.  R393 itself
-- remains a consumer/interface for that authority, not its producer.
------------------------------------------------------------------------

round564R563LiteralDerivativeReused : Bool
round564R563LiteralDerivativeReused = true

round564R393FundamentalTheoremIsRecordField : Bool
round564R393FundamentalTheoremIsRecordField = true

round564R393ConstructsFTCFromDerivative : Bool
round564R393ConstructsFTCFromDerivative = false

round564EndpointIdentityClosedGivenScalarFTC : Bool
round564EndpointIdentityClosedGivenScalarFTC = true

round564ConcreteScalarFTCInhabitantInstalled : Bool
round564ConcreteScalarFTCInhabitantInstalled = false

data R564Residual : Set where
  missingConcreteScalarFTCInhabitant564 : R564Residual
  missingGlobalSelfFluxFiniteAggregation564 : R564Residual
  missingFactoredCommutatorSpacetimeBound564 : R564Residual
  literalLeafAClosed564 : R564Residual

currentR564Residual : R564Residual
currentR564Residual = missingConcreteScalarFTCInhabitant564

round564LiteralR406SignedCrossPaymentClosed : Bool
round564LiteralR406SignedCrossPaymentClosed = false

round564CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round564CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round564ClayPromotion : Bool
round564ClayPromotion = false

round564EndpointIdentityClosedGivenScalarFTCIsTrue :
  round564EndpointIdentityClosedGivenScalarFTC ≡ true
round564EndpointIdentityClosedGivenScalarFTCIsTrue = refl

round564R393ConstructsFTCFromDerivativeIsFalse :
  round564R393ConstructsFTCFromDerivative ≡ false
round564R393ConstructsFTCFromDerivativeIsFalse = refl

round564ConcreteScalarFTCInhabitantInstalledIsFalse :
  round564ConcreteScalarFTCInhabitantInstalled ≡ false
round564ConcreteScalarFTCInhabitantInstalledIsFalse = refl

round564ClayPromotionIsFalse : round564ClayPromotion ≡ false
round564ClayPromotionIsFalse = refl
