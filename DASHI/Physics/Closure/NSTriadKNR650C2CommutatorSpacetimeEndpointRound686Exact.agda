{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650C2CommutatorSpacetimeEndpointRound686Exact where

------------------------------------------------------------------------
-- ROUND686 / SPACETIME C2 KERNEL = INTEGRATED COMMUTATOR - ENDPOINT
--
-- R685 proves pointwise on the literal physical fixed-output fibre
--
--   WeightedWork = CommutatorWork - TangentWork.
--
-- R661/Endpoint already prove that the tangent work is the actual derivative
-- of the coherent mixed self-energy.  Therefore ordinary integration
-- linearity + FTC give
--
--   integral WeightedWork
--     = integral CommutatorWork
--       - (E_M(T)-E_M(0)).
--
-- Thus after R684-R686 there is no independent local covariance/input-
-- Laplacian analytic debt: C2 is on forcing/commutator spacetime currency
-- plus an exact endpoint term.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNR650BadCollarRateWeightedWorkRound664Exact as R664
import DASHI.Physics.Closure.NSTriadKNR650RateKernelCommutatorEndpointRound685Exact as R685

F : C3.RealField _
F = Rational.rationalRealField

minusOne : ℚ
minusOne = 0ℚ - 1ℚ

module LiveSpacetime
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra :
      R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (zeroCalculus :
      Endpoint.VectorZeroDerivative Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (scalarScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf) where

  module W = R664.LiveWeightedWork
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC integrationLinearity D

  module End = Endpoint.Endpoint
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC D

  commutatorWorkAt :
    Nat → Z3.FourierMode → Time → ℚ
  commutatorWorkAt cutoff output time =
    Work.coherentWork
      (W.Sp.mixedAt cutoff output time)
      (Work.fixedOutputCommutator
        End.S
        (End.velocityAt cutoff time)
        (End.forcingAt cutoff time)
        cutoff output)

  tangentWorkAt :
    Nat → Z3.FourierMode → Time → ℚ
  tangentWorkAt = W.Sp.dampedTangentWorkAt

  pointwiseWeightedIsCommutatorMinusTangent :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    W.weightedWorkAt cutoff output time
    ≡ commutatorWorkAt cutoff output time - tangentWorkAt cutoff output time
  pointwiseWeightedIsCommutatorMinusTangent cutoff output time =
    R685.fixedOutputPhysicalRateKernelIsCommutatorMinusTangent
      (End.physicalSystemAt cutoff time)
      End.S
      output

  integratedWeighted :
    Nat → Z3.FourierMode → Time → ℚ
  integratedWeighted cutoff output terminal =
    integrateTo (W.weightedWorkAt cutoff output) terminal

  integratedCommutator :
    Nat → Z3.FourierMode → Time → ℚ
  integratedCommutator cutoff output terminal =
    integrateTo (commutatorWorkAt cutoff output) terminal

  integratedTangent :
    Nat → Z3.FourierMode → Time → ℚ
  integratedTangent cutoff output terminal =
    integrateTo (tangentWorkAt cutoff output) terminal

  integratePointwiseSplit :
    (cutoff : Nat) (output : Z3.FourierMode) (terminal : Time) →
    integratedWeighted cutoff output terminal
    ≡ integratedCommutator cutoff output terminal
      - integratedTangent cutoff output terminal
  integratePointwiseSplit cutoff output terminal =
    let
      weighted = W.weightedWorkAt cutoff output
      comm = commutatorWorkAt cutoff output
      tangent = tangentWorkAt cutoff output

      expose :
        integrateTo weighted terminal
        ≡ integrateTo (λ time → comm time + minusOne * tangent time) terminal
      expose =
        Energy.integrationCongruent integrationLinearity
          (λ time →
            trans
              (pointwiseWeightedIsCommutatorMinusTangent
                cutoff output time)
              (solve (comm time ∷ tangent time ∷ [])))
          terminal

      add =
        Energy.integrationAdditive integrationLinearity
          comm (λ time → minusOne * tangent time) terminal

      scale =
        Energy.integrationConstantScale integrationLinearity
          minusOne tangent terminal
    in
    trans expose
      (trans add
        (trans
          (cong
            (integrateTo comm terminal +_)
            scale)
          (solve
            ( integrateTo comm terminal
            ∷ integrateTo tangent terminal
            ∷ []))))

  integratedTangentIsEndpoint :
    (cutoff : Nat) (output : Z3.FourierMode) (terminal : Time) →
    integratedTangent cutoff output terminal
    ≡ End.selfEnergy cutoff output terminal
      - End.selfEnergy cutoff output initialTime
  integratedTangentIsEndpoint cutoff output terminal =
    trans
      (Energy.integrationCongruent integrationLinearity
        (W.Sp.dampedTangentWorkIsEndpointTangent cutoff output)
        terminal)
      (End.fixedOutputEndpointIdentity cutoff output terminal)

  c2KernelSpacetimeIsCommutatorMinusEndpoint :
    (cutoff : Nat) (output : Z3.FourierMode) (terminal : Time) →
    integratedWeighted cutoff output terminal
    ≡
    integratedCommutator cutoff output terminal
      -
      ( End.selfEnergy cutoff output terminal
      - End.selfEnergy cutoff output initialTime )
  c2KernelSpacetimeIsCommutatorMinusEndpoint cutoff output terminal =
    trans
      (integratePointwiseSplit cutoff output terminal)
      (cong
        (integratedCommutator cutoff output terminal -_)
        (integratedTangentIsEndpoint cutoff output terminal))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round686C2KernelSpacetimeIsCommutatorMinusEndpoint : Bool
round686C2KernelSpacetimeIsCommutatorMinusEndpoint = true

round686EndpointCalculusIsIndependentNonlinearLeaf : Bool
round686EndpointCalculusIsIndependentNonlinearLeaf = false

round686C2LocalNonlinearCurrencyMatchesCommutatorLane : Bool
round686C2LocalNonlinearCurrencyMatchesCommutatorLane = true

round686R568ResolventWeightedSquareControlsThisCommutator : Bool
round686R568ResolventWeightedSquareControlsThisCommutator = false

round686IntroducesEstimate : Bool
round686IntroducesEstimate = false

round686C2Closed : Bool
round686C2Closed = false

round686IntroducesNewClayLeaf : Bool
round686IntroducesNewClayLeaf = false

round686ClayPromotion : Bool
round686ClayPromotion = false

round686C2KernelSpacetimeIsCommutatorMinusEndpointIsTrue :
  round686C2KernelSpacetimeIsCommutatorMinusEndpoint ≡ true
round686C2KernelSpacetimeIsCommutatorMinusEndpointIsTrue = refl

round686EndpointCalculusIsIndependentNonlinearLeafIsFalse :
  round686EndpointCalculusIsIndependentNonlinearLeaf ≡ false
round686EndpointCalculusIsIndependentNonlinearLeafIsFalse = refl

round686C2LocalNonlinearCurrencyMatchesCommutatorLaneIsTrue :
  round686C2LocalNonlinearCurrencyMatchesCommutatorLane ≡ true
round686C2LocalNonlinearCurrencyMatchesCommutatorLaneIsTrue = refl

round686R568ResolventWeightedSquareControlsThisCommutatorIsFalse :
  round686R568ResolventWeightedSquareControlsThisCommutator ≡ false
round686R568ResolventWeightedSquareControlsThisCommutatorIsFalse = refl

round686IntroducesEstimateIsFalse :
  round686IntroducesEstimate ≡ false
round686IntroducesEstimateIsFalse = refl

round686C2ClosedIsFalse :
  round686C2Closed ≡ false
round686C2ClosedIsFalse = refl

round686IntroducesNewClayLeafIsFalse :
  round686IntroducesNewClayLeaf ≡ false
round686IntroducesNewClayLeafIsFalse = refl

round686ClayPromotionIsFalse :
  round686ClayPromotion ≡ false
round686ClayPromotionIsFalse = refl
