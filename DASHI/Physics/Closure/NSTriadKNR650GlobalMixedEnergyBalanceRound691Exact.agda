{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650GlobalMixedEnergyBalanceRound691Exact where

------------------------------------------------------------------------
-- ROUND691 / GLOBAL MIXED-PRODUCT ENERGY BALANCE
--
-- R686 proves at each fixed output k
--
--   integral WeightedWork_k
--     = integral CommutatorWork_k
--       - (E_M,k(T) - E_M,k(0)).
--
-- The R690 strategy says to sum outputs before any estimate.  This file does
-- exactly that on the literal canonical nonzero cutoff list:
--
--   sum_k integral WeightedWork_k
--     =
--   sum_k integral CommutatorWork_k
--     - sum_k (E_M,k(T)-E_M,k(0)).
--
-- Thus the globally summed input-Laplacian/rate work really is the dissipative
-- side of a higher (quartic mixed-product) energy identity, but it is NOT a
-- pure-sign term by algebra alone: the exact nonlinear remainder is the summed
-- coherent commutator work.  Any closure must control/cancel that SAME global
-- commutator without splitting away the signed structure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
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
import DASHI.Physics.Closure.NSTriadKNR650C2CommutatorSpacetimeEndpointRound686Exact as R686

F : C3.RealField _
F = Rational.rationalRealField

module GlobalMixedEnergy
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

  module Local = R686.LiveSpacetime
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus
    FTC integrationLinearity D

  endpointDelta :
    Nat → Z3.FourierMode → Time → ℚ
  endpointDelta cutoff output terminal =
    Local.End.selfEnergy cutoff output terminal
      - Local.End.selfEnergy cutoff output initialTime

  sumIntegratedWeighted :
    Nat → List Z3.FourierMode → Time → ℚ
  sumIntegratedWeighted cutoff [] terminal = 0ℚ
  sumIntegratedWeighted cutoff (output ∷ rest) terminal =
    Local.integratedWeighted cutoff output terminal
      + sumIntegratedWeighted cutoff rest terminal

  sumIntegratedCommutator :
    Nat → List Z3.FourierMode → Time → ℚ
  sumIntegratedCommutator cutoff [] terminal = 0ℚ
  sumIntegratedCommutator cutoff (output ∷ rest) terminal =
    Local.integratedCommutator cutoff output terminal
      + sumIntegratedCommutator cutoff rest terminal

  sumEndpointDelta :
    Nat → List Z3.FourierMode → Time → ℚ
  sumEndpointDelta cutoff [] terminal = 0ℚ
  sumEndpointDelta cutoff (output ∷ rest) terminal =
    endpointDelta cutoff output terminal
      + sumEndpointDelta cutoff rest terminal

  summedMixedEnergyBalance :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    (terminal : Time) →
    sumIntegratedWeighted cutoff outputs terminal
    ≡
    sumIntegratedCommutator cutoff outputs terminal
      - sumEndpointDelta cutoff outputs terminal
  summedMixedEnergyBalance cutoff [] terminal =
    solve []
  summedMixedEnergyBalance cutoff (output ∷ rest) terminal =
    let
      local =
        Local.c2KernelSpacetimeIsCommutatorMinusEndpoint
          cutoff output terminal
      tail =
        summedMixedEnergyBalance cutoff rest terminal
      comm = Local.integratedCommutator cutoff output terminal
      endpoint = endpointDelta cutoff output terminal
      commTail = sumIntegratedCommutator cutoff rest terminal
      endpointTail = sumEndpointDelta cutoff rest terminal
    in
    trans
      (cong₂ _+_ local tail)
      (solve (comm ∷ endpoint ∷ commTail ∷ endpointTail ∷ []))

  globalIntegratedWeighted :
    Nat → Time → ℚ
  globalIntegratedWeighted cutoff terminal =
    sumIntegratedWeighted
      cutoff (Canonical.nonzeroCutoffModes cutoff) terminal

  globalIntegratedCommutator :
    Nat → Time → ℚ
  globalIntegratedCommutator cutoff terminal =
    sumIntegratedCommutator
      cutoff (Canonical.nonzeroCutoffModes cutoff) terminal

  globalMixedEnergyEndpoint :
    Nat → Time → ℚ
  globalMixedEnergyEndpoint cutoff terminal =
    sumEndpointDelta
      cutoff (Canonical.nonzeroCutoffModes cutoff) terminal

  globalMixedEnergyBalance :
    (cutoff : Nat) (terminal : Time) →
    globalIntegratedWeighted cutoff terminal
    ≡ globalIntegratedCommutator cutoff terminal
      - globalMixedEnergyEndpoint cutoff terminal
  globalMixedEnergyBalance cutoff terminal =
    summedMixedEnergyBalance
      cutoff (Canonical.nonzeroCutoffModes cutoff) terminal

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round691FixedOutputEndpointIdentitiesSummedGlobally : Bool
round691FixedOutputEndpointIdentitiesSummedGlobally = true

round691GlobalRateWorkIsCommutatorMinusMixedEnergyEndpoint : Bool
round691GlobalRateWorkIsCommutatorMinusMixedEnergyEndpoint = true

round691GlobalInputLaplacianIsPureSignedDissipationByAlgebra : Bool
round691GlobalInputLaplacianIsPureSignedDissipationByAlgebra = false

round691RemainingGlobalNonlinearTermIsCoherentCommutator : Bool
round691RemainingGlobalNonlinearTermIsCoherentCommutator = true

round691GlobalCommutatorCancellationClosed : Bool
round691GlobalCommutatorCancellationClosed = false

round691GlobalCommutatorCutoffUniformPaymentClosed : Bool
round691GlobalCommutatorCutoffUniformPaymentClosed = false

round691IntroducesEstimate : Bool
round691IntroducesEstimate = false

round691C1Closed : Bool
round691C1Closed = false

round691C2Closed : Bool
round691C2Closed = false

round691ClayPromotion : Bool
round691ClayPromotion = false

round691FixedOutputEndpointIdentitiesSummedGloballyIsTrue :
  round691FixedOutputEndpointIdentitiesSummedGlobally ≡ true
round691FixedOutputEndpointIdentitiesSummedGloballyIsTrue = refl

round691GlobalRateWorkIsCommutatorMinusMixedEnergyEndpointIsTrue :
  round691GlobalRateWorkIsCommutatorMinusMixedEnergyEndpoint ≡ true
round691GlobalRateWorkIsCommutatorMinusMixedEnergyEndpointIsTrue = refl

round691GlobalInputLaplacianIsPureSignedDissipationByAlgebraIsFalse :
  round691GlobalInputLaplacianIsPureSignedDissipationByAlgebra ≡ false
round691GlobalInputLaplacianIsPureSignedDissipationByAlgebraIsFalse = refl

round691RemainingGlobalNonlinearTermIsCoherentCommutatorIsTrue :
  round691RemainingGlobalNonlinearTermIsCoherentCommutator ≡ true
round691RemainingGlobalNonlinearTermIsCoherentCommutatorIsTrue = refl

round691GlobalCommutatorCancellationClosedIsFalse :
  round691GlobalCommutatorCancellationClosed ≡ false
round691GlobalCommutatorCancellationClosedIsFalse = refl

round691GlobalCommutatorCutoffUniformPaymentClosedIsFalse :
  round691GlobalCommutatorCutoffUniformPaymentClosed ≡ false
round691GlobalCommutatorCutoffUniformPaymentClosedIsFalse = refl

round691IntroducesEstimateIsFalse :
  round691IntroducesEstimate ≡ false
round691IntroducesEstimateIsFalse = refl

round691C1ClosedIsFalse :
  round691C1Closed ≡ false
round691C1ClosedIsFalse = refl

round691C2ClosedIsFalse :
  round691C2Closed ≡ false
round691C2ClosedIsFalse = refl

round691ClayPromotionIsFalse :
  round691ClayPromotion ≡ false
round691ClayPromotionIsFalse = refl
