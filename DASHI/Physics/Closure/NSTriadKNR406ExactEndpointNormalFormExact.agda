module DASHI.Physics.Closure.NSTriadKNR406ExactEndpointNormalFormExact where

------------------------------------------------------------------------
-- H2 / EXACT LIVE R406 ENDPOINT NORMAL FORM
--
-- R557 proves on the literal live R406 carrier
--
--   2 * ∫ R406
--     = (∫ FactoredFull - ∫ SelfGram) - ∫ SelfFluxTangent.
--
-- R570 proves that the final tangent is the derivative of the SAME global
-- self-flux observable on the canonical output list, hence ordinary scalar FTC
-- gives
--
--   ∫ SelfFluxTangent = SelfFlux(T) - SelfFlux(0).
--
-- This owner composes those two existing exact theorems.  It introduces no
-- nonlinear estimate and no A3 identification.  Consequently the remaining
-- A3-facing same-object seam is now explicit:
--
--   (FactoredFull - SelfGram)  <->  A3 signed pair-difference carrier.
--
-- That seam must respect the division-free normalization proved separately in
-- NSTriadKNA3D1bDivisionFreeTransportExact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _-_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as FTC564
import DASHI.Physics.Closure.NSTriadKNLiveIntegratedDiagonalReducedNormalFormRound557Exact as R557
import DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxTangentWeldRound570Exact as R570

F : C3.RealField _
F = Rational.rationalRealField

module ExactEndpoint
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
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
    (integration : R495.IntegrationTransportAuthority Time integrateTo)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo VectorDerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo VectorDerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo VectorDerivativeOf D))
    (cutoff : Nat) where

  module Literal = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf

  module Integrated = R557.LiveIntegrated
    Time initialTime integrateTo VectorDerivativeOf integration

  module Tangent = R570.TangentWeld
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCrossCalculus vectorAlgebra hermitianCalculus
    constantCalculus scalarAlgebra integration D R cutoff

  T = Literal.literalPhysicalTrajectory D

  literalR406IntegralExactEndpointNormalForm :
    FTC564.ScalarFundamentalTheorem564
      Time initialTime integrateTo ScalarDerivativeOf →
    (terminal : Time) →
    R539.two
      * integrateTo (Integrated.literalRemainder T R cutoff) terminal
    ≡
    ( integrateTo (Integrated.factoredFull T R cutoff) terminal
      - integrateTo (Integrated.selfGram T R cutoff) terminal )
      -
      ( Tangent.Global.globalSelfFlux terminal
      - Tangent.Global.globalSelfFlux initialTime )
  literalR406IntegralExactEndpointNormalForm FTC terminal =
    trans
      (Integrated.liveIntegratedReducedNormalForm T R cutoff terminal)
      (cong
        (λ tangent →
          ( integrateTo (Integrated.factoredFull T R cutoff) terminal
          - integrateTo (Integrated.selfGram T R cutoff) terminal )
          - tangent)
        (Tangent.exactReducedTangentEndpointFTC570 FTC terminal))

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

r406ExactEndpointNormalFormClosedGivenScalarFTC : Bool
r406ExactEndpointNormalFormClosedGivenScalarFTC = true

r406EndpointNormalFormUsesLiteralR408Trajectory : Bool
r406EndpointNormalFormUsesLiteralR408Trajectory = true

r406EndpointNormalFormIntroducesNewNSEstimate : Bool
r406EndpointNormalFormIntroducesNewNSEstimate = false

factoredFullMinusSelfGramToA3SameObjectAttachmentClosed : Bool
factoredFullMinusSelfGramToA3SameObjectAttachmentClosed = false

unitCoefficientEndpointPlusA3IdentityProved : Bool
unitCoefficientEndpointPlusA3IdentityProved = false

r406ExactEndpointNormalFormClosedGivenScalarFTCIsTrue :
  r406ExactEndpointNormalFormClosedGivenScalarFTC ≡ true
r406ExactEndpointNormalFormClosedGivenScalarFTCIsTrue = refl

r406EndpointNormalFormUsesLiteralR408TrajectoryIsTrue :
  r406EndpointNormalFormUsesLiteralR408Trajectory ≡ true
r406EndpointNormalFormUsesLiteralR408TrajectoryIsTrue = refl

r406EndpointNormalFormIntroducesNewNSEstimateIsFalse :
  r406EndpointNormalFormIntroducesNewNSEstimate ≡ false
r406EndpointNormalFormIntroducesNewNSEstimateIsFalse = refl

factoredFullMinusSelfGramToA3SameObjectAttachmentClosedIsFalse :
  factoredFullMinusSelfGramToA3SameObjectAttachmentClosed ≡ false
factoredFullMinusSelfGramToA3SameObjectAttachmentClosedIsFalse = refl

unitCoefficientEndpointPlusA3IdentityProvedIsFalse :
  unitCoefficientEndpointPlusA3IdentityProved ≡ false
unitCoefficientEndpointPlusA3IdentityProvedIsFalse = refl
