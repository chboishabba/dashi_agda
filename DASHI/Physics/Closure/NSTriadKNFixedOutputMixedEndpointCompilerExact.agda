module DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact where

------------------------------------------------------------------------
-- S2b2d1b / LITERAL FIXED-OUTPUT ENDPOINT COMPILER
--
-- The coherent-work decomposition leaves an endpoint/tangent term
--
--   W(M_k,T_k) = 2 Re <M_k,T_k>.
--
-- This file removes that term from the nonlinear PDE frontier.  On the exact
-- R408 trajectory:
--
--   * R427 differentiates every literal plus/minus mixed cell;
--   * finite vector addition differentiates the fixed-output coherent sum;
--   * R94 + R381 + R292 identify the literal R30 tangent with the SAME
--     damped-plus-network tangent used by d1a;
--   * R417 differentiates the real-Hermitian self energy;
--   * ordinary scalar FTC turns its tangent into an endpoint difference.
--
-- No covariance sign or estimate is introduced.  The only external analytic
-- authorities are derivative-of-zero for the empty finite fold and the same
-- standard scalar FTC already isolated elsewhere in the repository.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityCellDampedTangentRound292Exact as R292
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94Base
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNHelicalDampedProjectorLinearityRound381Exact as R381
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNLiteralTrajectoryMixedCellDerivativeRound427Exact as R427
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work

F : C3.RealField _
F = Rational.rationalRealField

oneHalf : ℚ
oneHalf = Int.+ 1 / 2

two : ℚ
two = Work.two

record VectorZeroDerivative
    (Time : Set)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) : Set₁ where
  field
    zeroVectorDerivative :
      DerivativeOf
        (λ _ → C3.complex3Zero F)
        (λ _ → C3.complex3Zero F)

open VectorZeroDerivative public

module Endpoint
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross : R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (zeroCalculus : VectorZeroDerivative Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (scalarScaleCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (FTC : R564.ScalarFundamentalTheorem564
      Time initialTime integrateTo ScalarDerivativeOf)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo VectorDerivativeOf) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf
  module Cell = R427.LiteralCellDynamics
    Time initialTime integrateTo VectorDerivativeOf projectedCross

  support = Live.support D
  state = Live.stateTrajectory support
  E = Live.Base.E state
  I = Live.Base.I state
  S = Live.Base.S state

  velocityAt : Nat → Time → Z3.FourierMode → C3.Complex3 F
  velocityAt cutoff time = Cell.liveVelocity D cutoff time

  physicalSystemAt : Nat → Time → R30.PhysicalFiniteComplex3GalerkinSystem F
  physicalSystemAt = Live.physicalSystemAt support

  rateAt : Nat → Time → Z3.FourierMode → ℚ
  rateAt cutoff time mode =
    R94.physicalDecayRate (physicalSystemAt cutoff time) mode

  forcingAt : Nat → Time → Z3.FourierMode → C3.Complex3 F
  forcingAt cutoff time =
    R94.physicalNetworkForcingMode (physicalSystemAt cutoff time)

  mixedCellCurve : Nat → Physical.PhysicalTriadIncidence → Time → C3.Complex3 F
  mixedCellCurve cutoff = Cell.literalMixedCellCurve D S cutoff

  actualCellTangent : Nat → Physical.PhysicalTriadIncidence → Time → C3.Complex3 F
  actualCellTangent cutoff = Cell.literalMixedCellTangentCurve D S cutoff

  dampedCellTangent : Nat → Physical.PhysicalTriadIncidence → Time → C3.Complex3 F
  dampedCellTangent cutoff tau time =
    D1a.dampedMixedTangentCell
      (rateAt cutoff time) S
      (velocityAt cutoff time)
      (forcingAt cutoff time) tau

  literalCellTangentIsDampedCellTangent :
    (cutoff : Nat) (tau : Physical.PhysicalTriadIncidence) (time : Time) →
    actualCellTangent cutoff tau time ≡ dampedCellTangent cutoff tau time
  literalCellTangentIsDampedCellTangent cutoff tau time =
    let
      sys = physicalSystemAt cutoff time
      velocity = velocityAt cutoff time
      forcing = forcingAt cutoff time
      rho = rateAt cutoff time
      p = Physical.p tau
      q = Physical.q tau
      coefficientAt :
        (mode : Z3.FourierMode) →
        R30.literalViscousQuadraticCoefficient sys mode
        ≡ R94Base.dampedPlusForcing
            (rho mode) (velocity mode) (forcing mode)
      coefficientAt = R94.literalCoefficientIsDampedPlusNetwork sys
      regroup =
        R292.mixedCellDampedTangent
          S (R381.canonicalHelicalDampedProjectorLinearity E I S)
          velocity forcing rho tau
      d1aRegroup =
        D1a.cellDampedTangentIsDecayPlusProductRule
          rho S velocity forcing tau
    in
    rewrite coefficientAt p | coefficientAt q
    = trans regroup (sym d1aRegroup)

  foldCurve :
    Nat → List Physical.PhysicalTriadIncidence → Time → C3.Complex3 F
  foldCurve cutoff items time =
    R224.foldVector
      (λ tau → mixedCellCurve cutoff tau time) items

  foldActualTangent :
    Nat → List Physical.PhysicalTriadIncidence → Time → C3.Complex3 F
  foldActualTangent cutoff items time =
    R224.foldVector
      (λ tau → actualCellTangent cutoff tau time) items

  foldDampedTangent :
    Nat → List Physical.PhysicalTriadIncidence → Time → C3.Complex3 F
  foldDampedTangent cutoff items time =
    R224.foldVector
      (λ tau → dampedCellTangent cutoff tau time) items

  foldTangentSameObject :
    (cutoff : Nat) (items : List Physical.PhysicalTriadIncidence) →
    (time : Time) →
    foldActualTangent cutoff items time ≡ foldDampedTangent cutoff items time
  foldTangentSameObject cutoff [] time = refl
  foldTangentSameObject cutoff (tau ∷ rest) time =
    cong₂ C3.complex3Add
      (literalCellTangentIsDampedCellTangent cutoff tau time)
      (foldTangentSameObject cutoff rest time)

  foldDerivative :
    (cutoff : Nat) (items : List Physical.PhysicalTriadIncidence) →
    VectorDerivativeOf
      (foldCurve cutoff items)
      (foldActualTangent cutoff items)
  foldDerivative cutoff [] = zeroVectorDerivative zeroCalculus
  foldDerivative cutoff (tau ∷ rest) =
    R425.addDerivative vectorAlgebra
      (Cell.round408BuildsActualMixedCellDerivative D S cutoff tau)
      (foldDerivative cutoff rest)

  fixedOutputMixedCurve :
    Nat → Z3.FourierMode → Time → C3.Complex3 F
  fixedOutputMixedCurve cutoff output =
    foldCurve cutoff (Output.physicalOutputFiber cutoff output)

  fixedOutputActualTangent :
    Nat → Z3.FourierMode → Time → C3.Complex3 F
  fixedOutputActualTangent cutoff output =
    foldActualTangent cutoff (Output.physicalOutputFiber cutoff output)

  fixedOutputDampedTangent :
    Nat → Z3.FourierMode → Time → C3.Complex3 F
  fixedOutputDampedTangent cutoff output =
    foldDampedTangent cutoff (Output.physicalOutputFiber cutoff output)

  fixedOutputMixedDerivative :
    (cutoff : Nat) (output : Z3.FourierMode) →
    VectorDerivativeOf
      (fixedOutputMixedCurve cutoff output)
      (fixedOutputActualTangent cutoff output)
  fixedOutputMixedDerivative cutoff output =
    foldDerivative cutoff (Output.physicalOutputFiber cutoff output)

  fixedOutputActualTangentIsDampedTangent :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    fixedOutputActualTangent cutoff output time
    ≡ fixedOutputDampedTangent cutoff output time
  fixedOutputActualTangentIsDampedTangent cutoff output =
    foldTangentSameObject cutoff (Output.physicalOutputFiber cutoff output)

  selfEnergy : Nat → Z3.FourierMode → Time → ℚ
  selfEnergy cutoff output time =
    R179.realHermitianCross
      (fixedOutputMixedCurve cutoff output time)
      (fixedOutputMixedCurve cutoff output time)

  coherentTangentWork : Nat → Z3.FourierMode → Time → ℚ
  coherentTangentWork cutoff output time =
    Work.coherentWork
      (fixedOutputMixedCurve cutoff output time)
      (fixedOutputActualTangent cutoff output time)

  selfEnergyDerivative :
    (cutoff : Nat) (output : Z3.FourierMode) →
    ScalarDerivativeOf
      (selfEnergy cutoff output)
      (coherentTangentWork cutoff output)
  selfEnergyDerivative cutoff output =
    let
      mixed = fixedOutputMixedCurve cutoff output
      tangent = fixedOutputActualTangent cutoff output
      dMixed = fixedOutputMixedDerivative cutoff output
      raw = R417.realHermitianGramProductRule
        hermitianCalculus dMixed dMixed
      scaled = R416.constantScaleDerivative scalarScaleCalculus oneHalf raw
      curveMeaning :
        (time : Time) →
        oneHalf * (two * R179.realHermitianCross (mixed time) (mixed time))
        ≡ selfEnergy cutoff output time
      curveMeaning time =
        solve (R179.realHermitianCross (mixed time) (mixed time) ∷ [])
      tangentMeaning :
        (time : Time) →
        oneHalf *
          (two *
            (R179.realHermitianCross (tangent time) (mixed time)
              + R179.realHermitianCross (mixed time) (tangent time)))
        ≡ coherentTangentWork cutoff output time
      tangentMeaning time
        rewrite R287.realHermitianCrossSymmetric
          (tangent time) (mixed time) =
        solve (R179.realHermitianCross (mixed time) (tangent time) ∷ [])
    in
    R416.transportDerivative scalarScaleCalculus
      curveMeaning tangentMeaning scaled

  fixedOutputEndpointIdentity :
    (cutoff : Nat) (output : Z3.FourierMode) (terminal : Time) →
    integrateTo (coherentTangentWork cutoff output) terminal
    ≡ selfEnergy cutoff output terminal - selfEnergy cutoff output initialTime
  fixedOutputEndpointIdentity cutoff output terminal =
    R564.scalarEndpointFTC564 FTC
      (selfEnergyDerivative cutoff output) terminal

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

literalRHSFixedOutputDampedTangentWeldClosed : Bool
literalRHSFixedOutputDampedTangentWeldClosed = true

fixedOutputMixedEndpointDerivativeCompilerClosed : Bool
fixedOutputMixedEndpointDerivativeCompilerClosed = true

fixedOutputEndpointIdentityClosedGivenCalculus : Bool
fixedOutputEndpointIdentityClosedGivenCalculus = true

concreteEndpointFTCInstalled : Bool
concreteEndpointFTCInstalled = false

quantitativeCoherentCovariancePaymentClosed : Bool
quantitativeCoherentCovariancePaymentClosed = false

literalRHSFixedOutputDampedTangentWeldClosedIsTrue :
  literalRHSFixedOutputDampedTangentWeldClosed ≡ true
literalRHSFixedOutputDampedTangentWeldClosedIsTrue = refl

fixedOutputMixedEndpointDerivativeCompilerClosedIsTrue :
  fixedOutputMixedEndpointDerivativeCompilerClosed ≡ true
fixedOutputMixedEndpointDerivativeCompilerClosedIsTrue = refl

fixedOutputEndpointIdentityClosedGivenCalculusIsTrue :
  fixedOutputEndpointIdentityClosedGivenCalculus ≡ true
fixedOutputEndpointIdentityClosedGivenCalculusIsTrue = refl

concreteEndpointFTCInstalledIsFalse :
  concreteEndpointFTCInstalled ≡ false
concreteEndpointFTCInstalledIsFalse = refl

quantitativeCoherentCovariancePaymentClosedIsFalse :
  quantitativeCoherentCovariancePaymentClosed ≡ false
quantitativeCoherentCovariancePaymentClosedIsFalse = refl
