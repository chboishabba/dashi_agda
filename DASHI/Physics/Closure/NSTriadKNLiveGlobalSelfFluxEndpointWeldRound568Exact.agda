module DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxEndpointWeldRound568Exact where

------------------------------------------------------------------------
-- ROUND568 / SAME GLOBAL SELF-FLUX: R564 TEMPORAL CARRIER = R558 ENDPOINT
--
-- R564 constructs the actual global derivative of the finite self-flux by
-- summing the R563 per-output derivatives over `nonzeroCutoffModes cutoff`.
-- R558 independently owns nonnegativity and the no-output-cardinality endpoint
-- bound for the global self-flux on that SAME canonical output list.
--
-- This owner proves those are one observable at the initial endpoint.  Hence
-- the favourable R553 reduction may consume R558's endpoint theorem without a
-- caller-selected replacement flux or a proof-irrelevance shortcut.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedDoubleMixedMassRound456Exact as R456
import DASHI.Physics.Closure.NSTriadKNGlobalSelfFluxEndpointRound558Exact as R558
import DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxDerivativeRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module LiveEndpointWeld
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
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo VectorDerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo VectorDerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo VectorDerivativeOf D))
    (cutoff : Nat) where

  module Literal = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf
  module Dyn = R240.PhysicalNSDynamics
    Time initialTime integrateTo VectorDerivativeOf
  module Flux = R406.FixedLiveFlux
    Time initialTime integrateTo VectorDerivativeOf
  module Global = R564.LiveGlobalDerivative
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCrossCalculus vectorAlgebra hermitianCalculus
    constantCalculus scalarAlgebra D R cutoff

  T = Literal.literalPhysicalTrajectory D
  module Slice0 = Flux.At T R cutoff initialTime

  S = Dyn.Base.S (Dyn.forgetDynamics T)
  L = Dyn.Base.L (Dyn.forgetDynamics T)
  H = Dyn.Base.H (Dyn.forgetDynamics T)

  module WithEndpointGeometry
      (unitGap : R450.CanonicalFourierUnitGap Slice0.PS)
      (radiusCalibration :
        R456.PhysicalModeRadiusCalibration
          (Dyn.Base.E (Dyn.forgetDynamics T))
          (Dyn.Base.I (Dyn.forgetDynamics T)) S) where

    module Endpoint = R558.GlobalSelfFlux
      Slice0.PS S L H Slice0.P
      (Flux.Live.stateViscosityPositive T Slice0.support cutoff initialTime)
      unitGap radiusCalibration cutoff

    initialSumExact :
      (selected : List Z3.FourierMode) →
      (allNonzero :
        (output : Z3.FourierMode) →
        output Cube.∈ selected → Z3.NonZeroMode output) →
      R412.sumCurves (Global.outputFluxCurves selected allNonzero) initialTime
      ≡ Endpoint.outputListSelfFlux selected allNonzero
    initialSumExact [] allNonzero = refl
    initialSumExact (output ∷ rest) allNonzero =
      cong₂ _+_ refl
        (initialSumExact rest
          (λ selected member → allNonzero selected (Cube.there member)))

    globalInitialSelfFluxIsEndpoint568 :
      Global.globalSelfFlux initialTime ≡ Endpoint.globalSelfFlux
    globalInitialSelfFluxIsEndpoint568 =
      initialSumExact Global.outputs Global.canonicalNonzero

    globalInitialSelfFluxNonnegative568 :
      0ℚ ≤ Global.globalSelfFlux initialTime
    globalInitialSelfFluxNonnegative568 =
      subst (0ℚ ≤_) (sym globalInitialSelfFluxIsEndpoint568)
        Endpoint.globalSelfFluxNonnegative

    globalInitialSelfFluxEnergySquareEndpoint568 :
      Global.globalSelfFlux initialTime
      ≤ Endpoint.twoW *
          (DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact.fortyEight
            * Endpoint.Mass.energySquare)
    globalInitialSelfFluxEnergySquareEndpoint568 =
      subst
        (λ selected → selected ≤ Endpoint.twoW *
          (DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact.fortyEight
            * Endpoint.Mass.energySquare))
        (sym globalInitialSelfFluxIsEndpoint568)
        Endpoint.globalSelfFluxEnergySquareEndpoint

round568SameCanonicalOutputListUsed : Bool
round568SameCanonicalOutputListUsed = true

round568GlobalInitialSelfFluxSameObjectWeldClosed : Bool
round568GlobalInitialSelfFluxSameObjectWeldClosed = true

round568GlobalInitialSelfFluxNonnegativeClosed : Bool
round568GlobalInitialSelfFluxNonnegativeClosed = true

round568NoOutputCardinalityTaxIntroduced : Bool
round568NoOutputCardinalityTaxIntroduced = true

round568NewEndpointEstimateIntroduced : Bool
round568NewEndpointEstimateIntroduced = false

round568CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round568CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round568ClayPromotion : Bool
round568ClayPromotion = false

round568GlobalInitialSelfFluxSameObjectWeldClosedIsTrue :
  round568GlobalInitialSelfFluxSameObjectWeldClosed ≡ true
round568GlobalInitialSelfFluxSameObjectWeldClosedIsTrue = refl

round568ClayPromotionIsFalse : round568ClayPromotion ≡ false
round568ClayPromotionIsFalse = refl
