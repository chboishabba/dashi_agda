module DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxTangentWeldRound570Exact where

------------------------------------------------------------------------
-- ROUND570 / R564 GLOBAL DERIVATIVE TANGENT = R557 REDUCED-NORMAL-FORM TANGENT
--
-- R565 gives FTC for the global self-flux derivative built by R564.  R557's
-- integrated reduced normal form subtracts the independently assembled R555/
-- R556 global self-flux tangent.  Both are finite sums of the SAME R550 literal
-- self-pair tangent on the SAME canonical nonzero output list.
--
-- This owner closes that final temporal same-object seam before FTC is allowed
-- to enter the R553 favourable-sign inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNGlobalDiagonalReducedNormalFormRound555Exact as R555
import DASHI.Physics.Closure.NSTriadKNLiveR406DiagonalReducedNormalFormRound556Exact as R556
import DASHI.Physics.Closure.NSTriadKNLiveIntegratedDiagonalReducedNormalFormRound557Exact as R557
import DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxDerivativeRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNSelfFluxTemporalReconciliationRound565Exact as R565
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as FTC564
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module TangentWeld
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
    (scalarAlgebra : R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
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
  module Global = R564.LiveGlobalDerivative
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCrossCalculus vectorAlgebra hermitianCalculus
    constantCalculus scalarAlgebra D R cutoff
  module Reconciled = R565.Reconcile
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCrossCalculus vectorAlgebra hermitianCalculus
    constantCalculus scalarAlgebra D R cutoff
  module Reduced = R556.LiveReduced
    Time initialTime integrateTo VectorDerivativeOf
  module Integrated = R557.LiveIntegrated
    Time initialTime integrateTo VectorDerivativeOf integration

  T = Literal.literalPhysicalTrajectory D

  module At (time : Time) where
    module Slice = Reduced.At T R cutoff time

    buildOutputsNonzero :
      (selected : List Z3.FourierMode) →
      ((output : Z3.FourierMode) →
        output Cube.∈ selected → Z3.NonZeroMode output) →
      Slice.GR.OutputsNonzero selected
    buildOutputsNonzero [] allNonzero = Slice.GR.nonzeroNil
    buildOutputsNonzero (output ∷ rest) allNonzero =
      Slice.GR.nonzeroCons
        (allNonzero output (Cube.here refl))
        (buildOutputsNonzero rest
          (λ selected member → allNonzero selected (Cube.there member)))

    tangentSumExact :
      (selected : List Z3.FourierMode) →
      (allNonzero :
        (output : Z3.FourierMode) →
        output Cube.∈ selected → Z3.NonZeroMode output) →
      R412.sumCurves (Global.outputTangentCurves selected allNonzero) time
      ≡ Slice.GR.globalSelfFluxTangent
          cutoff selected (buildOutputsNonzero selected allNonzero)
    tangentSumExact [] allNonzero = refl
    tangentSumExact (output ∷ rest) allNonzero =
      cong₂ _+_ refl
        (tangentSumExact rest
          (λ selected member → allNonzero selected (Cube.there member)))

    globalTangentExact570 :
      Global.globalSelfFluxTangent time
      ≡ Integrated.selfFluxTangent T R cutoff time
    globalTangentExact570 =
      tangentSumExact Global.outputs Global.canonicalNonzero

  integratedGlobalTangentExact570 :
    (terminal : Time) →
    integrateTo Global.globalSelfFluxTangent terminal
    ≡ integrateTo (Integrated.selfFluxTangent T R cutoff) terminal
  integratedGlobalTangentExact570 terminal =
    R495.integrateCongruent integration
      Global.globalSelfFluxTangent
      (Integrated.selfFluxTangent T R cutoff)
      (λ time → At.globalTangentExact570 time)
      terminal

  exactReducedTangentEndpointFTC570 :
    FTC564.ScalarFundamentalTheorem564
      Time initialTime integrateTo ScalarDerivativeOf →
    (terminal : Time) →
    integrateTo (Integrated.selfFluxTangent T R cutoff) terminal
    ≡ Global.globalSelfFlux terminal - Global.globalSelfFlux initialTime
  exactReducedTangentEndpointFTC570 FTC terminal =
    trans
      (sym (integratedGlobalTangentExact570 terminal))
      (Reconciled.globalSelfFluxEndpointFTC565 FTC terminal)

round570GlobalSelfFluxTangentSameObjectWeldClosed : Bool
round570GlobalSelfFluxTangentSameObjectWeldClosed = true

round570IntegratedTangentTransportUsesR495Only : Bool
round570IntegratedTangentTransportUsesR495Only = true

round570FTCStillExternalScalarAuthority : Bool
round570FTCStillExternalScalarAuthority = true

round570NewNavierStokesEstimateIntroduced : Bool
round570NewNavierStokesEstimateIntroduced = false

round570CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round570CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round570ClayPromotion : Bool
round570ClayPromotion = false

round570GlobalSelfFluxTangentSameObjectWeldClosedIsTrue :
  round570GlobalSelfFluxTangentSameObjectWeldClosed ≡ true
round570GlobalSelfFluxTangentSameObjectWeldClosedIsTrue = refl

round570ClayPromotionIsFalse : round570ClayPromotion ≡ false
round570ClayPromotionIsFalse = refl
