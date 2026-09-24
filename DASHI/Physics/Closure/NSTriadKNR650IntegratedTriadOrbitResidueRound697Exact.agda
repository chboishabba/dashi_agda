{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650IntegratedTriadOrbitResidueRound697Exact where

------------------------------------------------------------------------
-- ROUND697 / SPACETIME WELD: TRIAD-ORBIT RESIDUE = 3 * R691 COMMUTATOR
--
-- R696 is instantaneous:
--
--   sum_beta R_triangle(beta,t)
--     = 3 * sum_{k != 0} W(M_k(t), C_k(t)).
--
-- This owner transports that equality through the SAME integration authority
-- used by the R691 mixed-energy balance and proves
--
--   integral_0^T sum_beta R_triangle(beta,t) dt
--     = 3 * globalIntegratedCommutator_N(T).
--
-- The finite output sum is exchanged with integration only by the explicit
-- standard integration-additivity authority.  No Navier--Stokes inequality,
-- norm, absolute value, or cutoff factor is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNR650GlobalMixedEnergyBalanceRound691Exact as R691
import DASHI.Physics.Closure.NSTriadKNR650MaskedCompleteTriadOrbitResidueRound696Exact as R696

F : C3.RealField _
F = Rational.rationalRealField

module IntegratedOrbit
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
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf) where

  module Balance = R691.GlobalMixedEnergy
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus
    FTC integrationLinearity D

  sumCommutatorAt :
    Nat → List Z3.FourierMode → Time → ℚ
  sumCommutatorAt cutoff [] time = 0ℚ
  sumCommutatorAt cutoff (output ∷ rest) time =
    Balance.Local.commutatorWorkAt cutoff output time
      + sumCommutatorAt cutoff rest time

  sumCommutatorAtIntegratesToR691 :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    (terminal : Time) →
    integrateTo (sumCommutatorAt cutoff outputs) terminal
    ≡ Balance.sumIntegratedCommutator cutoff outputs terminal
  sumCommutatorAtIntegratesToR691 cutoff [] terminal =
    R495.integrateZero integrationTransport terminal
  sumCommutatorAtIntegratesToR691
      cutoff (output ∷ rest) terminal =
    trans
      (R495.integrateAdd integrationTransport
        (Balance.Local.commutatorWorkAt cutoff output)
        (sumCommutatorAt cutoff rest)
        terminal)
      (cong
        (Balance.Local.integratedCommutator cutoff output terminal +_)
        (sumCommutatorAtIntegratesToR691 cutoff rest terminal))

  module At
      (cutoff : Nat)
      (time : Time) where

    physicalSystem =
      Balance.Local.End.physicalSystemAt cutoff time

    module Orbit =
      R696.MaskedOrbit physicalSystem Balance.Local.End.S

    staticOutputCommutatorIsLive :
      (output : Z3.FourierMode) →
      Orbit.E.outputCoherentCommutatorWork output
      ≡ Balance.Local.commutatorWorkAt cutoff output time
    staticOutputCommutatorIsLive output = refl

    staticGlobalCommutatorIsLiveSum :
      (outputs : List Z3.FourierMode) →
      Orbit.E.sumOutputCommutatorWork outputs
      ≡ sumCommutatorAt cutoff outputs time
    staticGlobalCommutatorIsLiveSum [] = refl
    staticGlobalCommutatorIsLiveSum (output ∷ rest) =
      cong₂ _+_
        (staticOutputCommutatorIsLive output)
        (staticGlobalCommutatorIsLiveSum rest)

    selectedStaticGlobalIsLive :
      Orbit.E.nonzeroGlobalCommutatorWork
      ≡
      sumCommutatorAt cutoff
        (Canonical.nonzeroCutoffModes cutoff) time
    selectedStaticGlobalIsLive =
      staticGlobalCommutatorIsLiveSum
        (Canonical.nonzeroCutoffModes cutoff)

    orbitResidue : ℚ
    orbitResidue =
      R38.foldPower Orbit.triadOrbitResidue
        (Physical.physicalTriadEnumeration cutoff)

    orbitResidueIsThreeLiveCommutator :
      orbitResidue
      ≡
      R696.three *
        sumCommutatorAt cutoff
          (Canonical.nonzeroCutoffModes cutoff) time
    orbitResidueIsThreeLiveCommutator =
      trans
        Orbit.completeTriadOrbitResidueIsThreeCoherentCommutator
        (cong (R696.three *_) selectedStaticGlobalIsLive)

  orbitResidueAt :
    Nat → Time → ℚ
  orbitResidueAt cutoff time = At.orbitResidue cutoff time

  integratedOrbitResidue :
    Nat → Time → ℚ
  integratedOrbitResidue cutoff terminal =
    integrateTo (orbitResidueAt cutoff) terminal

  integratedOrbitResidueIsThreeR691Commutator :
    (cutoff : Nat) (terminal : Time) →
    integratedOrbitResidue cutoff terminal
    ≡ R696.three * Balance.globalIntegratedCommutator cutoff terminal
  integratedOrbitResidueIsThreeR691Commutator cutoff terminal =
    let
      outputs = Canonical.nonzeroCutoffModes cutoff
      liveSum = sumCommutatorAt cutoff outputs

      expose :
        integrateTo (orbitResidueAt cutoff) terminal
        ≡
        integrateTo
          (λ time → R696.three * liveSum time)
          terminal
      expose =
        Energy.integrationCongruent integrationLinearity
          (At.orbitResidueIsThreeLiveCommutator cutoff)
          terminal

      scale :
        integrateTo
          (λ time → R696.three * liveSum time)
          terminal
        ≡
        R696.three * integrateTo liveSum terminal
      scale =
        Energy.integrationConstantScale integrationLinearity
          R696.three liveSum terminal

      sumIntegral :
        integrateTo liveSum terminal
        ≡ Balance.globalIntegratedCommutator cutoff terminal
      sumIntegral =
        sumCommutatorAtIntegratesToR691 cutoff outputs terminal
    in
    trans expose
      (trans scale
        (cong (R696.three *_) sumIntegral))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round697MaskedOrbitResidueIntegratedOnSameR691Carrier : Bool
round697MaskedOrbitResidueIntegratedOnSameR691Carrier = true

round697IntegratedOrbitResidueIsThreeR691Commutator : Bool
round697IntegratedOrbitResidueIsThreeR691Commutator = true

round697FiniteOutputSumIntegrationUsesStandardAdditivityOnly : Bool
round697FiniteOutputSumIntegrationUsesStandardAdditivityOnly = true

round697IntroducesNSEstimate : Bool
round697IntroducesNSEstimate = false

round697CutoffUniformOrbitResiduePaymentClosed : Bool
round697CutoffUniformOrbitResiduePaymentClosed = false

round697R568R406ConsumerAttachmentClosed : Bool
round697R568R406ConsumerAttachmentClosed = false

round697ClayPromotion : Bool
round697ClayPromotion = false

round697MaskedOrbitResidueIntegratedOnSameR691CarrierIsTrue :
  round697MaskedOrbitResidueIntegratedOnSameR691Carrier ≡ true
round697MaskedOrbitResidueIntegratedOnSameR691CarrierIsTrue = refl

round697IntegratedOrbitResidueIsThreeR691CommutatorIsTrue :
  round697IntegratedOrbitResidueIsThreeR691Commutator ≡ true
round697IntegratedOrbitResidueIsThreeR691CommutatorIsTrue = refl

round697FiniteOutputSumIntegrationUsesStandardAdditivityOnlyIsTrue :
  round697FiniteOutputSumIntegrationUsesStandardAdditivityOnly ≡ true
round697FiniteOutputSumIntegrationUsesStandardAdditivityOnlyIsTrue = refl

round697IntroducesNSEstimateIsFalse :
  round697IntroducesNSEstimate ≡ false
round697IntroducesNSEstimateIsFalse = refl

round697CutoffUniformOrbitResiduePaymentClosedIsFalse :
  round697CutoffUniformOrbitResiduePaymentClosed ≡ false
round697CutoffUniformOrbitResiduePaymentClosedIsFalse = refl

round697R568R406ConsumerAttachmentClosedIsFalse :
  round697R568R406ConsumerAttachmentClosed ≡ false
round697R568R406ConsumerAttachmentClosedIsFalse = refl

round697ClayPromotionIsFalse :
  round697ClayPromotion ≡ false
round697ClayPromotionIsFalse = refl
