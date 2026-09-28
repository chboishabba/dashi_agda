{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650AugmentedDerivativeInputLaplacianRound738Exact where

------------------------------------------------------------------------
-- ROUND738 / POINTWISE GLOBAL BALANCE + R684 INPUT-LAPLACIAN SUBSTITUTION
--
-- R737 differentiates Q_+- exactly.
--
-- R685 gives on each output:
--
--   weighted_k = commutator_k - tangent_k.
--
-- Summing over the canonical nonzero output list yields pointwise
--
--   W_N(t) = C_N(t) - Qdot_N(t),
--
-- hence
--
--   Qdot_N(t) = C_N(t) - W_N(t).
--
-- R684 simultaneously identifies each weighted_k with
--
--   nu * Work(M_k, L_in,k).
--
-- This file performs both global finite sums before any estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNR650RateKernelInputLaplacianCollapseRound684Exact as R684
import DASHI.Physics.Closure.NSTriadKNR650AugmentedCriticalWeightedNormalFormRound734Exact as R734
import DASHI.Physics.Closure.NSTriadKNR650AugmentedObservableDerivativeRound737Exact as R737

F : C3.RealField _
F = Rational.rationalRealField

module PointwiseGlobal
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
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf)
    (C :
      ModeCarrier.LiteralModeCarrier.LiteralCutoffModeCarrier
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D))
    (R :
      R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D)) where

  module Der = R737.AugmentedDerivative
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Aug = Der.Aug
  module Upper = Der.Upper
  module Balance = Upper.Balance
  module Local = Balance.Local
  module W = Local.W
  module End = Local.End

  sumScalar :
    (Z3.FourierMode → ℚ) → List Z3.FourierMode → ℚ
  sumScalar value [] = 0ℚ
  sumScalar value (output ∷ rest) =
    value output + sumScalar value rest

  globalWeightedAt :
    Nat → Time → ℚ
  globalWeightedAt cutoff time =
    sumScalar
      (λ output → W.weightedWorkAt cutoff output time)
      (Canonical.nonzeroCutoffModes cutoff)

  globalCommutatorAt :
    Nat → Time → ℚ
  globalCommutatorAt cutoff time =
    sumScalar
      (λ output → Local.commutatorWorkAt cutoff output time)
      (Canonical.nonzeroCutoffModes cutoff)

  globalTangentAt :
    Nat → Time → ℚ
  globalTangentAt cutoff time =
    sumScalar
      (λ output → Local.tangentWorkAt cutoff output time)
      (Canonical.nonzeroCutoffModes cutoff)

  sumPointwiseBalance :
    (cutoff : Nat) (time : Time) (outputs : List Z3.FourierMode) →
    sumScalar
      (λ output → W.weightedWorkAt cutoff output time) outputs
    ≡
    sumScalar
      (λ output → Local.commutatorWorkAt cutoff output time) outputs
      -
    sumScalar
      (λ output → Local.tangentWorkAt cutoff output time) outputs
  sumPointwiseBalance cutoff time [] =
    solve []
  sumPointwiseBalance cutoff time (output ∷ rest) =
    let
      head =
        Local.pointwiseWeightedIsCommutatorMinusTangent
          cutoff output time
      tail =
        sumPointwiseBalance cutoff time rest
    in
    trans
      (cong₂ _+_ head tail)
      (solve
        ( Local.commutatorWorkAt cutoff output time
        ∷ Local.tangentWorkAt cutoff output time
        ∷ sumScalar
            (λ selected → Local.commutatorWorkAt cutoff selected time) rest
        ∷ sumScalar
            (λ selected → Local.tangentWorkAt cutoff selected time) rest
        ∷ []))

  globalPointwiseBalance :
    (cutoff : Nat) (time : Time) →
    globalWeightedAt cutoff time
    ≡ globalCommutatorAt cutoff time - globalTangentAt cutoff time
  globalPointwiseBalance cutoff time =
    sumPointwiseBalance
      cutoff time (Canonical.nonzeroCutoffModes cutoff)

  globalTangentIsR737QDot :
    (cutoff : Nat) (time : Time) →
    globalTangentAt cutoff time
    ≡ Der.globalQPlusMinusTangent cutoff time
  globalTangentIsR737QDot cutoff time = refl

  qDotIsCommutatorMinusWeighted :
    (cutoff : Nat) (time : Time) →
    Der.globalQPlusMinusTangent cutoff time
    ≡ globalCommutatorAt cutoff time - globalWeightedAt cutoff time
  qDotIsCommutatorMinusWeighted cutoff time =
    let
      w = globalWeightedAt cutoff time
      c = globalCommutatorAt cutoff time
      q = Der.globalQPlusMinusTangent cutoff time
      base : w ≡ c - q
      base =
        trans
          (globalPointwiseBalance cutoff time)
          (cong
            (λ tangent → c - tangent)
            (globalTangentIsR737QDot cutoff time))
    in
    trans
      (solve (w ∷ c ∷ q ∷ []))
      (sym base)

  localInputLaplacianWork :
    Nat → Time → Z3.FourierMode → ℚ
  localInputLaplacianWork cutoff time output =
    let
      physicalSystem = End.physicalSystemAt cutoff time
      I = End.I
      nu = End.nu
      velocity = End.velocityAt cutoff time
      items = Output.physicalOutputFiber cutoff output
      value = D1a.mixedProductCell End.S velocity
      mixed = R224.foldVector value items
    in
    nu * Work.coherentWork mixed
      (R684.inputLaplacianVector I value cutoff output)

  localWeightedIsInputLaplacian :
    (cutoff : Nat) (time : Time) (output : Z3.FourierMode) →
    W.weightedWorkAt cutoff output time
    ≡ localInputLaplacianWork cutoff time output
  localWeightedIsInputLaplacian cutoff time output =
    R684.fixedOutputPhysicalRateKernelIsInputLaplacianWork
      (End.physicalSystemAt cutoff time)
      End.S output

  globalInputLaplacianWorkAt :
    Nat → Time → ℚ
  globalInputLaplacianWorkAt cutoff time =
    sumScalar
      (localInputLaplacianWork cutoff time)
      (Canonical.nonzeroCutoffModes cutoff)

  sumWeightedIsInputLaplacian :
    (cutoff : Nat) (time : Time) (outputs : List Z3.FourierMode) →
    sumScalar
      (λ output → W.weightedWorkAt cutoff output time) outputs
    ≡
    sumScalar
      (localInputLaplacianWork cutoff time) outputs
  sumWeightedIsInputLaplacian cutoff time [] = refl
  sumWeightedIsInputLaplacian cutoff time (output ∷ rest) =
    cong₂ _+_
      (localWeightedIsInputLaplacian cutoff time output)
      (sumWeightedIsInputLaplacian cutoff time rest)

  globalWeightedIsInputLaplacian :
    (cutoff : Nat) (time : Time) →
    globalWeightedAt cutoff time
    ≡ globalInputLaplacianWorkAt cutoff time
  globalWeightedIsInputLaplacian cutoff time =
    sumWeightedIsInputLaplacian
      cutoff time (Canonical.nonzeroCutoffModes cutoff)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round738GlobalPointwiseWeightedBalanceClosed : Bool
round738GlobalPointwiseWeightedBalanceClosed = true

round738QDotIsCommutatorMinusWeightedClosed : Bool
round738QDotIsCommutatorMinusWeightedClosed = true

round738GlobalWeightedIsInputLaplacianClosed : Bool
round738GlobalWeightedIsInputLaplacianClosed = true

round738IntroducesEstimate : Bool
round738IntroducesEstimate = false

round738W2Closed : Bool
round738W2Closed = false

round738ClayPromotion : Bool
round738ClayPromotion = false

round738GlobalPointwiseWeightedBalanceClosedIsTrue :
  round738GlobalPointwiseWeightedBalanceClosed ≡ true
round738GlobalPointwiseWeightedBalanceClosedIsTrue = refl

round738QDotIsCommutatorMinusWeightedClosedIsTrue :
  round738QDotIsCommutatorMinusWeightedClosed ≡ true
round738QDotIsCommutatorMinusWeightedClosedIsTrue = refl

round738GlobalWeightedIsInputLaplacianClosedIsTrue :
  round738GlobalWeightedIsInputLaplacianClosed ≡ true
round738GlobalWeightedIsInputLaplacianClosedIsTrue = refl

round738IntroducesEstimateIsFalse :
  round738IntroducesEstimate ≡ false
round738IntroducesEstimateIsFalse = refl

round738W2ClosedIsFalse :
  round738W2Closed ≡ false
round738W2ClosedIsFalse = refl

round738ClayPromotionIsFalse :
  round738ClayPromotion ≡ false
round738ClayPromotionIsFalse = refl
