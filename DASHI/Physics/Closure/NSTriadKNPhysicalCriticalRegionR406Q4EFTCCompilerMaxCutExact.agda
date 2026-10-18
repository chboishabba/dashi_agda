module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4EFTCCompilerMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B7 Q4+E / REMOVE THE STANDARD FTC SEAM
--
-- The literal global off-diagonal R406 flux derivative is constructed from the
-- exact R396 unordered pair family.  Given ordinary scalar FTC, the Q4+E
-- producer therefore needs only TWO analytic bounds:
--
--   (Q4) cutoff-uniform integrated off-diagonal Gram,
--   (E)  cutoff-uniform weighted-flux endpoint increment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_; _-_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxDerivativeBoundaryRound409Exact as R409
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNDirectResolventGramFluxNormalFormExact as Q4E
import DASHI.Physics.Closure.NSTriadKNLiteralGlobalOffDiagonalFluxDerivativeMaxCutExact as Global

F : C3.RealField _
F = Rational.rationalRealField

module Q4EFTCCompiler
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross : R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (integration : R495.IntegrationTransportAuthority Time integrateTo)
    (FTC : R564.ScalarFundamentalTheorem564
      Time initialTime integrateTo ScalarDerivativeOf)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo VectorDerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo VectorDerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo VectorDerivativeOf D)) where

  module Literal = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf
  module Boundary = R409.Boundary
    Time initialTime integrateTo VectorDerivativeOf ScalarDerivativeOf
  module DerivativeAt (cutoff : Nat) = Global.GlobalOffDiagonalDerivative
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra hermitianCalculus
    constantCalculus scalarAlgebra D R cutoff
  module LiveQ4E = Q4E.LiveNormalForm
    Time initialTime integrateTo VectorDerivativeOf integration

  T = Literal.literalPhysicalTrajectory D

  offDiagonalFluxFTC :
    (cutoff : Nat) (terminal : Time) →
    LiveQ4E.integratedOffDiagonalFluxTangent T R cutoff terminal
    ≡ LiveQ4E.offDiagonalFluxAt T R cutoff terminal
        - LiveQ4E.offDiagonalFluxAt T R cutoff initialTime
  offDiagonalFluxFTC cutoff terminal =
    R564.scalarEndpointFTC564 FTC
      (Boundary.derivativeIsExactR406Tangent
        (DerivativeAt.exactR406FluxDerivative cutoff))
      terminal

  record Q4EAnalyticBounds : Set₁ where
    field
      cutoffIndependentGramBound : Time → ℚ
      integratedGramBudget :
        (cutoff : Nat) (terminal : Time) →
        LiveQ4E.integratedOffDiagonalGram T R cutoff terminal
        ≤ cutoffIndependentGramBound terminal

      cutoffIndependentFluxEndpointBound : Time → ℚ
      fluxEndpointBudget :
        (cutoff : Nat) (terminal : Time) →
        LiveQ4E.offDiagonalFluxAt T R cutoff terminal
          - LiveQ4E.offDiagonalFluxAt T R cutoff initialTime
        ≤ cutoffIndependentFluxEndpointBound terminal

  open Q4EAnalyticBounds public

  analyticBoundsBuildDirectGramFluxBudget :
    Q4EAnalyticBounds → LiveQ4E.DirectGramFluxBudget T R
  analyticBoundsBuildDirectGramFluxBudget B = record
    { LiveQ4E.cutoffIndependentGramBound = cutoffIndependentGramBound B
    ; LiveQ4E.integratedGramBudget = integratedGramBudget B
    ; LiveQ4E.cutoffIndependentFluxEndpointBound =
        cutoffIndependentFluxEndpointBound B
    ; LiveQ4E.offDiagonalFluxFTC = offDiagonalFluxFTC
    ; LiveQ4E.fluxEndpointBudget = fluxEndpointBudget B
    }

q4eLiteralOffDiagonalDerivativeCompilerClosed : Bool
q4eLiteralOffDiagonalDerivativeCompilerClosed = true

q4eEndpointFTCClosedGivenOrdinaryScalarFTC : Bool
q4eEndpointFTCClosedGivenOrdinaryScalarFTC = true

q4eResearchLeavesReducedToTwoAnalyticBounds : Bool
q4eResearchLeavesReducedToTwoAnalyticBounds = true

q4eCompilerIntroducesNSEstimate : Bool
q4eCompilerIntroducesNSEstimate = false

clayPromotion : Bool
clayPromotion = false

q4eLiteralOffDiagonalDerivativeCompilerClosedIsTrue :
  q4eLiteralOffDiagonalDerivativeCompilerClosed ≡ true
q4eLiteralOffDiagonalDerivativeCompilerClosedIsTrue = refl

q4eEndpointFTCClosedGivenOrdinaryScalarFTCIsTrue :
  q4eEndpointFTCClosedGivenOrdinaryScalarFTC ≡ true
q4eEndpointFTCClosedGivenOrdinaryScalarFTCIsTrue = refl

q4eResearchLeavesReducedToTwoAnalyticBoundsIsTrue :
  q4eResearchLeavesReducedToTwoAnalyticBounds ≡ true
q4eResearchLeavesReducedToTwoAnalyticBoundsIsTrue = refl
