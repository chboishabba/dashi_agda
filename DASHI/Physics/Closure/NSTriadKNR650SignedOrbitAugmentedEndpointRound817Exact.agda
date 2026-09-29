{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SignedOrbitAugmentedEndpointRound817Exact where

------------------------------------------------------------------------
-- ROUND817 / INTEGRATED SIGNED ORBIT = NEGATIVE AUGMENTED W2 DEFECT
--
-- Compose R815's literal signed orbit rate with R742's integrated packet
-- growth identification and R734's exact mixed-energy/weighted-work
-- endpoint balance.  No new estimate, sign, or scale-free equality is used.
--
--   integral [D_sep + D_cc + six*(2nu-delta)d] dt
--     = -six * (
--           [(X-12E)(T)-(X-12E)(0)] + delta*D(T) - 12*W(T)
--       ).
--
-- Therefore the signed orbit payment >=0 is exactly the original
-- augmented-W2 defect <=0. This is a temporal, not an amplitude-independent,
-- representation: the quartic mixed-energy endpoint carries the quintic
-- dynamics through its derivative, as in the repo's R734 work.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNPhysicalBonySwapEquivarianceRound129Exact as R129
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
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedResidualCarrierRound760Exact as R760
import DASHI.Physics.Closure.NSTriadKNR650EnergyOrbitBonyProfileRound775Exact as R775
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744
import DASHI.Physics.Closure.NSTriadKNR650SignedOrbitPacketWeldRound815Exact as R815
import DASHI.Physics.Closure.NSTriadKNR650IntegratedW2PhysicalPacketCombinedRound742Exact as R742
import DASHI.Physics.Closure.NSTriadKNR650IntegratedSignedOrbitPaymentRound816Exact as R816
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700

F : C3.RealField _
F = Rational.rationalRealField

module SignedOrbitAugmentedEndpoint
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




  module Signed = R816.IntegratedSignedOrbitCompiler
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module W2 = Signed.W2
  module Aug = W2.Aug
  module Packet = W2.Packet
  module Combined = W2.Combined

  module At
      (cutoff : Nat)
      (margin : ℚ)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module Source = Signed.At cutoff margin S

    criticalGrowth : Time → ℚ
    criticalGrowth terminal =
      W2.Growth.criticalEnergyGrowthWithMargin D cutoff margin terminal

    weighted : Time → ℚ
    weighted terminal =
      Aug.Balance.globalIntegratedWeighted cutoff terminal

    mixedTerminal : ℚ
    mixedTerminal = Aug.Upper.globalSelfEnergy cutoff initialTime

    mixedEnergyAt : Time → ℚ
    mixedEnergyAt time = Aug.Upper.globalSelfEnergy cutoff time

    twelve : ℚ
    twelve = R700.twelve

    augmentedW2Defect : Time → ℚ
    augmentedW2Defect terminal =
      Aug.augmentedCriticalGrowthWithMargin cutoff margin terminal
        - twelve * weighted terminal

    combinedMinusPacketAsNegativeAugmented :
      (terminal : Time) →
      Source.integratedCombined terminal -
        Source.integratedPacket terminal
      ≡ 0ℚ - augmentedW2Defect terminal
    combinedMinusPacketAsNegativeAugmented terminal =
      let
        combined = Source.integratedCombined terminal
        packet = Source.integratedPacket terminal
        growth = criticalGrowth terminal
        w = weighted terminal
        eT = mixedEnergyAt terminal
        e0 = mixedTerminal
        augmented = Aug.augmentedCriticalGrowthWithMargin cutoff margin terminal

        combinedMeaning :
          combined ≡ twelve * (w + eT - e0)
        combinedMeaning =
          Aug.combinedAsTwelveWeightedPlusEndpoint cutoff terminal

        packetMeaning : packet ≡ growth
        packetMeaning =
          W2.integratedPacketIsCriticalGrowth cutoff S margin terminal

        beforeEndpoint :
          combined - packet
          ≡ 0ℚ - ((growth - twelve * (eT - e0)) - twelve * w)
        beforeEndpoint =
          trans
            (cong₂ _-_ combinedMeaning packetMeaning)
            (solve (growth ∷ twelve ∷ w ∷ eT ∷ e0 ∷ []))

        endpointMeaning :
          growth - twelve * (eT - e0) ≡ augmented
        endpointMeaning =
          Aug.directGrowthMinusEndpointIsAugmentedGrowth
            cutoff margin terminal
      in
      trans
        beforeEndpoint
        (cong
          (λ g → 0ℚ - (g - twelve * w))
          endpointMeaning)

    integratedSignedOrbitIsNegativeSixAugmentedDefect :
      (terminal : Time) →
      Source.integratedOrbitPayment terminal
      ≡ 0ℚ - Signed.six * augmentedW2Defect terminal
    integratedSignedOrbitIsNegativeSixAugmentedDefect terminal =
      trans
        (Source.integratedOrbitIsSixPhysicalGap terminal)
        (trans
          (cong (Signed.six *_)
            (combinedMinusPacketAsNegativeAugmented terminal))
          (solve (Signed.six ∷ augmentedW2Defect terminal ∷ [])))

round817CompleteSignedOrbitIsNegativeSixAugmentedW2Defect : Bool
round817CompleteSignedOrbitIsNegativeSixAugmentedW2Defect = true

round817UsesExactR734MixedEnergyEndpoint : Bool
round817UsesExactR734MixedEnergyEndpoint = true

round817DoesNotRequirePointwiseCancellation : Bool
round817DoesNotRequirePointwiseCancellation = true

round817DoesNotGrantSignedInequality : Bool
round817DoesNotGrantSignedInequality = true

round817W1Closed : Bool
round817W1Closed = false

round817W2Closed : Bool
round817W2Closed = false

round817ClayPromotion : Bool
round817ClayPromotion = false

round817W2ClosedIsFalse :
  round817W2Closed ≡ false
round817W2ClosedIsFalse = refl

round817ClayPromotionIsFalse :
  round817ClayPromotion ≡ false
round817ClayPromotionIsFalse = refl
