{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650IntegratedW2PhysicalPacketCombinedRound742Exact where

------------------------------------------------------------------------
-- ROUND742 / ORIGINAL INTEGRATED W2 = PHYSICAL PACKET SURPLUS <= COMBINED
--
-- R734 proves the integrated augmented-weighted W2 leaf is equivalent to the
-- direct R730 growth-to-combined leaf.
--
-- R659 proves exactly:
--
--   integrated strict critical surplus
--     = critical-energy growth with margin.
--
-- R648 proves exactly, under the standard physical packet structure:
--
--   integrated strict radial surplus
--     = integrated physical packet strict surplus.
--
-- Therefore the ORIGINAL integrated W2 leaf (not a pointwise strengthening)
-- is exactly equivalent to one literal signed spacetime inequality:
--
--   integral PacketStrictSurplus_{N,delta}
--     <= integral CombinedResidue_N.
--
-- R741 remains a stronger pointwise producer option.  This file freezes the
-- honest terminal analytic normal form.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

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
import DASHI.Physics.Closure.NSTriadKNLivePhysicalPacketStrictSurplusRound648Exact as R648
import DASHI.Physics.Closure.NSTriadKNR650C2CriticalEnergyGrowthNormalFormRound659Exact as R659
import DASHI.Physics.Closure.NSTriadKNR650AugmentedCriticalWeightedNormalFormRound734Exact as R734

F : C3.RealField _
F = Rational.rationalRealField

module IntegratedPhysicalW2
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

  module Aug = R734.AugmentedWeighted
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Direct = Aug.Direct
  module Combined = Aug.Combined

  module Packet = R648.LivePacketSurplus
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity

  module Growth = R659.EnergyGrowth
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity

  integratedPacketIsCriticalGrowth :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    (margin : ℚ) →
    (terminal : Time) →
    Packet.integratedPhysicalPacketStrictSurplus
      D cutoff margin terminal
    ≡
    Growth.criticalEnergyGrowthWithMargin
      D cutoff margin terminal
  integratedPacketIsCriticalGrowth cutoff S margin terminal =
    trans
      (sym
        (Packet.integratedRadialSurplusIsPhysicalPacketSurplus
          D C cutoff S margin terminal))
      (Growth.integratedRadialSurplusIsCriticalEnergyGrowthWithMargin
        D C cutoff margin terminal)

  record IntegratedPhysicalPacketCombinedPayment
      (cutoff : Nat)
      (terminal : Time) : Set₁ where
    field
      structure :
        Packet.LivePhysicalPacketStructure D C cutoff

      retainedMargin : ℚ
      retainedMarginPositive : 0ℚ < retainedMargin

      packetSurplusPaidByCombined :
        Packet.integratedPhysicalPacketStrictSurplus
          D cutoff retainedMargin terminal
        ≤ Combined.integratedCombinedSelfExternal cutoff terminal

  open IntegratedPhysicalPacketCombinedPayment public

  packetCombinedBuildsDirect :
    (cutoff : Nat) (terminal : Time) →
    IntegratedPhysicalPacketCombinedPayment cutoff terminal →
    Direct.DirectCombinedCriticalGrowthPayment cutoff terminal
  packetCombinedBuildsDirect cutoff terminal P = record
    { Direct.retainedMargin = retainedMargin P
    ; Direct.retainedMarginPositive = retainedMarginPositive P
    ; Direct.criticalGrowthPaidByCombined =
        subst
          (_≤ Combined.integratedCombinedSelfExternal cutoff terminal)
          (integratedPacketIsCriticalGrowth
            cutoff (structure P) (retainedMargin P) terminal)
          (packetSurplusPaidByCombined P)
    }

  directBuildsPacketCombined :
    (cutoff : Nat) (terminal : Time) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    Direct.DirectCombinedCriticalGrowthPayment cutoff terminal →
    IntegratedPhysicalPacketCombinedPayment cutoff terminal
  directBuildsPacketCombined cutoff terminal S P = record
    { structure = S
    ; retainedMargin = Direct.retainedMargin P
    ; retainedMarginPositive = Direct.retainedMarginPositive P
    ; packetSurplusPaidByCombined =
        subst
          (_≤ Combined.integratedCombinedSelfExternal cutoff terminal)
          (sym
            (integratedPacketIsCriticalGrowth
              cutoff S (Direct.retainedMargin P) terminal))
          (Direct.criticalGrowthPaidByCombined P)
    }

  packetCombinedBuildsAugmentedW2 :
    (cutoff : Nat) (terminal : Time) →
    IntegratedPhysicalPacketCombinedPayment cutoff terminal →
    Aug.AugmentedCriticalWeightedPayment cutoff terminal
  packetCombinedBuildsAugmentedW2 cutoff terminal P =
    Aug.directBuildsAugmented
      cutoff terminal
      (packetCombinedBuildsDirect cutoff terminal P)

  augmentedW2BuildsPacketCombined :
    (cutoff : Nat) (terminal : Time) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    Aug.AugmentedCriticalWeightedPayment cutoff terminal →
    IntegratedPhysicalPacketCombinedPayment cutoff terminal
  augmentedW2BuildsPacketCombined cutoff terminal S P =
    directBuildsPacketCombined
      cutoff terminal S
      (Aug.augmentedBuildsDirect cutoff terminal P)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round742OriginalIntegratedW2IsPacketSurplusBelowCombined : Bool
round742OriginalIntegratedW2IsPacketSurplusBelowCombined = true

round742NoPointwiseStrengtheningRequired : Bool
round742NoPointwiseStrengtheningRequired = true

round742R406TransportRequired : Bool
round742R406TransportRequired = false

round742IntegratedPacketCombinedPaymentClosed : Bool
round742IntegratedPacketCombinedPaymentClosed = false

round742IntroducesEstimate : Bool
round742IntroducesEstimate = false

round742ClayPromotion : Bool
round742ClayPromotion = false

round742OriginalIntegratedW2IsPacketSurplusBelowCombinedIsTrue :
  round742OriginalIntegratedW2IsPacketSurplusBelowCombined ≡ true
round742OriginalIntegratedW2IsPacketSurplusBelowCombinedIsTrue = refl

round742NoPointwiseStrengtheningRequiredIsTrue :
  round742NoPointwiseStrengtheningRequired ≡ true
round742NoPointwiseStrengtheningRequiredIsTrue = refl

round742R406TransportRequiredIsFalse :
  round742R406TransportRequired ≡ false
round742R406TransportRequiredIsFalse = refl

round742IntegratedPacketCombinedPaymentClosedIsFalse :
  round742IntegratedPacketCombinedPaymentClosed ≡ false
round742IntegratedPacketCombinedPaymentClosedIsFalse = refl

round742IntroducesEstimateIsFalse :
  round742IntroducesEstimate ≡ false
round742IntroducesEstimateIsFalse = refl

round742ClayPromotionIsFalse :
  round742ClayPromotion ≡ false
round742ClayPromotionIsFalse = refl
