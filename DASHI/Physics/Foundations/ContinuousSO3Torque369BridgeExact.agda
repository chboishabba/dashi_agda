module DASHI.Physics.Foundations.ContinuousSO3Torque369BridgeExact where

------------------------------------------------------------------------
-- CONTINUOUS SO(3) / TORQUE HANDOFF FOR THE 369 ORIENTATION TRANCHE
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as SO3
import DASHI.Physics.Foundations.OrientedThreeAxisBracket369Exact as Finite
import DASHI.Physics.Foundations.R3HodgeCrossExact as Hodge3
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as V3
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Lie
import DASHI.Physics.YangMills.BalabanP33SU2EuclideanGeometryExact as Euclidean
import DASHI.Physics.Laws.GaugeInteractionLaws as GaugeLaws

ContinuousVector3 : Set
ContinuousVector3 = V3.SU2LieAlgebra

-- Repository normalization: [X,Y] = 2 X cross Y.
twiceCross : ContinuousVector3 → ContinuousVector3 → ContinuousVector3
twiceCross = Lie.lieBracket

twiceAngularMomentum : ContinuousVector3 → ContinuousVector3 → ContinuousVector3
twiceAngularMomentum position momentum = twiceCross position momentum

twiceTorque : ContinuousVector3 → ContinuousVector3 → ContinuousVector3
twiceTorque position force = twiceCross position force

record AngularMomentumTorqueDynamics : Set₁ where
  constructor angular-momentum-torque-dynamics
  field
    State : Set
    position momentum force : State → ContinuousVector3
    derivative : (State → ContinuousVector3) → State → ContinuousVector3

    twiceL : State → ContinuousVector3
    twiceL state = twiceAngularMomentum (position state) (momentum state)

    twiceTau : State → ContinuousVector3
    twiceTau state = twiceTorque (position state) (force state)

    angularMomentumBalance :
      ∀ state → derivative twiceL state ≡ twiceTau state

open AngularMomentumTorqueDynamics public

continuousSO3RightJacobianConvention : SO3.SO3RightJacobianConvention
continuousSO3RightJacobianConvention = SO3.canonicalSO3RightJacobianConvention

existingSO3ContinuousConventionReused : Bool
existingSO3ContinuousConventionReused = true

continuousThreeCoordinateLieCarrierReused : Bool
continuousThreeCoordinateLieCarrierReused = true

continuousEuclideanGramGeometryReused : Bool
continuousEuclideanGramGeometryReused = true

axisBasisVector : SO3.SU2Axis → ContinuousVector3
axisBasisVector Hyper.axis-low = Euclidean.basisX
axisBasisVector Hyper.axis-mid = Euclidean.basisY
axisBasisVector Hyper.axis-high = Euclidean.basisZ

finiteBracketContinuousInputs :
  Finite.BracketVoxel → ContinuousVector3 × ContinuousVector3
finiteBracketContinuousInputs voxel =
  axisBasisVector (Finite.leftAxis voxel)
  , axisBasisVector (Finite.rightAxis voxel)

finiteBracketContinuousOutputBasis :
  Finite.BracketVoxel → ContinuousVector3
finiteBracketContinuousOutputBasis voxel =
  axisBasisVector (Finite.outputAxis voxel)

finiteOrientationIsContinuousRotation : Bool
finiteOrientationIsContinuousRotation = false

finiteC3PhaseIsSO3GroupElement : Bool
finiteC3PhaseIsSO3GroupElement = false

finiteAxisChartEmbedsIntoContinuousBasis : Bool
finiteAxisChartEmbedsIntoContinuousBasis = true

repoHasContinuousHodgeLawInterface : Bool
repoHasContinuousHodgeLawInterface = true

r3BivectorHodgeCrossIdentificationClosedHere : Bool
r3BivectorHodgeCrossIdentificationClosedHere =
  Hodge3.r3HodgeWedgeCrossClosed

r3TorqueAsHodgeWedge : ∀ position force →
  Hodge3.hodgeStar3 (Hodge3.wedge3 position force)
  ≡ Hodge3.cross3 position force
r3TorqueAsHodgeWedge = Hodge3.hodgeWedgeEqualsCross

record ContinuousSO3Torque369Boundary : Set where
  constructor continuous-so3-torque-369-boundary
  field
    finite369OrientationReused : Bool
    continuousLieCarrierReused : Bool
    exactBracketNormalizationReused : Bool
    rightJacobianConventionReused : Bool
    finiteAxisBasisEmbeddingExplicit : Bool
    finiteOrientationPromotedToWholeSO3 : Bool
    angularMomentumDerivativeManufacturedFromFiniteChart : Bool
    genericHodgeInterfaceAvailable : Bool
    specificR3HodgeCrossTheoremPaid : Bool

canonicalContinuousSO3Torque369Boundary : ContinuousSO3Torque369Boundary
canonicalContinuousSO3Torque369Boundary =
  continuous-so3-torque-369-boundary
    true true true true true false false true true
