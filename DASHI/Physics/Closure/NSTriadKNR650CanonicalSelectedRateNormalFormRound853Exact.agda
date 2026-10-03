{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CanonicalSelectedRateNormalFormRound853Exact where

------------------------------------------------------------------------
-- R853 / GENERAL POINTWISE NORMAL FORM OF THE R815/R823 SELECTED RATE
--
-- R815 already proves, on every live packet and at every time,
--
--   signedOrbitRate(delta) = 6 * (Combined - PacketSurplus(delta)).
--
-- R741 gives the two SAME-OBJECT identities
--
--   Combined = 12 * GlobalCoherentCommutator,
--   PacketSurplus(delta) = Production - (2nu-delta) * Dissipation.
--
-- Therefore, without using the special R829 snapshot arithmetic,
--
--   signedOrbitRate(delta)
--     = 6 * (12*C - P + (2nu-delta)*D).
--
-- This is the general semantic identity needed by the real R830/R831 lane.
-- At the decision normalization nu = delta = 1 it becomes exactly
--
--   6 * (12*C - P + D),
--
-- i.e. the public Lean selectedRate definition.  R850 is merely the t=0
-- numerical specialization of this pointwise identity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

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
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700
import DASHI.Physics.Closure.NSTriadKNR650SignedOrbitPacketWeldRound815Exact as R815
import DASHI.Physics.Closure.NSTriadKNR650PointwiseW2PhysicalPacketCombinedRound741Exact as R741

F : C3.RealField _
F = Rational.rationalRealField

module CanonicalSelectedRateNormalForm
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

  module Signed = R815.SignedOrbitPacketWeld
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Physical = R741.PhysicalW2
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Signed.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module A = Signed.At cutoff time S

    coherent : ℚ
    coherent = Physical.K.P.globalCommutatorAt cutoff time

    production : ℚ
    production = Physical.K.productionAt cutoff time

    dissipation : ℚ
    dissipation = Physical.K.dissipationAt cutoff time

    twoNu : ℚ
    twoNu = Physical.K.twoNu

    selectedNormalForm : ℚ → ℚ
    selectedNormalForm margin =
      Signed.six *
        (R700.twelve * coherent
          - production
          + (twoNu - margin) * dissipation)

    combinedSameObject :
      A.Combined.combinedResidueAt cutoff time
      ≡ R700.twelve * coherent
    combinedSameObject =
      sym (Physical.twelveGlobalCommutatorIsCombined cutoff time)

    packetSameObject :
      Packet.physicalPacketStrictSurplusRate D cutoff margin time
      ≡ production - (twoNu - margin) * dissipation
      where
      margin : ℚ
      margin = A.coefficient A.dissipation
    packetSameObject = refl

    signedRateNormalForm :
      (margin : ℚ) →
      A.signedOrbitPaymentRate margin
      ≡ selectedNormalForm margin
    signedRateNormalForm margin =
      let
        packet = Packet.physicalPacketStrictSurplusRate D cutoff margin time
        combined = A.Combined.combinedResidueAt cutoff time
        prod = production
        diss = dissipation
        coeff = twoNu - margin
        comm = coherent

        packetToLiteral :
          packet ≡ prod - coeff * diss
        packetToLiteral =
          sym (Physical.literalStrictSurplusIsPhysicalPacket
            cutoff S margin time)
      in
      trans
        (A.signedOrbitRateIsSixPhysicalGap margin)
        (trans
          (cong
            (λ c → Signed.six * (c - packet))
            combinedSameObject)
          (trans
            (cong
              (λ p → Signed.six *
                (R700.twelve * comm - p))
              packetToLiteral)
            (solve
              ( Signed.six
              ∷ R700.twelve
              ∷ comm
              ∷ prod
              ∷ coeff
              ∷ diss
              ∷ []))))

  integratedSelectedNormalForm :
    (cutoff : Nat)
    (margin : ℚ)
    (terminal : Time)
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    integrateTo
      (λ time → Signed.At.signedOrbitPaymentRate cutoff time S margin)
      terminal
    ≡
    integrateTo
      (λ time → At.selectedNormalForm cutoff time S margin)
      terminal
  integratedSelectedNormalForm cutoff margin terminal S =
    Energy.integrationCongruent integrationLinearity
      (λ time → At.signedRateNormalForm cutoff time S margin)
      terminal

round853GeneralR815SelectedRateNormalFormClosed : Bool
round853GeneralR815SelectedRateNormalFormClosed = true

round853UsesSnapshotArithmetic : Bool
round853UsesSnapshotArithmetic = false

round853IntroducesEstimate : Bool
round853IntroducesEstimate = false

round853RealTrajectoryCarrierWeldClosed : Bool
round853RealTrajectoryCarrierWeldClosed = false

round853R823DecisionClosed : Bool
round853R823DecisionClosed = false

round853GeneralR815SelectedRateNormalFormClosedIsTrue :
  round853GeneralR815SelectedRateNormalFormClosed ≡ true
round853GeneralR815SelectedRateNormalFormClosedIsTrue = refl

round853UsesSnapshotArithmeticIsFalse :
  round853UsesSnapshotArithmetic ≡ false
round853UsesSnapshotArithmeticIsFalse = refl

round853IntroducesEstimateIsFalse :
  round853IntroducesEstimate ≡ false
round853IntroducesEstimateIsFalse = refl
