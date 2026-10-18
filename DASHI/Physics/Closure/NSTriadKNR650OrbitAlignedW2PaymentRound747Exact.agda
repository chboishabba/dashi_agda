{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650OrbitAlignedW2PaymentRound747Exact where

------------------------------------------------------------------------
-- ROUND747 / W2 AS NONNEGATIVITY OF ONE SIGNED SPACETIME RESIDUAL
--
-- R746 proves, under the standard R648 packet structure,
--
--   G_N,delta(T)
--     = 3 * ( Combined_N(T) - PacketStrictSurplus_N,delta(T) ),
--
-- where G_N,delta is the integrated R745 orbit-aligned residual.
--
-- Since 3 > 0, the original R742 W2 payment
--
--   PacketStrictSurplus <= Combined
--
-- is EXACTLY equivalent to
--
--   0 <= G_N,delta(T).
--
-- This owner makes that one signed residual the preferred W2 payment surface.
-- No estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

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
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744
import DASHI.Physics.Closure.NSTriadKNR650IntegratedW2PhysicalPacketCombinedRound742Exact as R742
import DASHI.Physics.Closure.NSTriadKNR650IntegratedOrbitAlignedW2ResidualRound746Exact as R746

F : C3.RealField _
F = Rational.rationalRealField

threePositive747 : 0ℚ < R744.three
threePositive747 = ℚP.positive⁻¹ R744.three

threeNonnegative747 : 0ℚ ≤ R744.three
threeNonnegative747 = ℚP.<⇒≤ threePositive747

module ResidualPayment
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

  module G = R746.IntegratedOrbitAligned
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module W2 = R742.IntegratedPhysicalW2
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = G.Packet
  module Combined = G.Combined

  record OrbitAlignedResidualPayment
      (cutoff : Nat)
      (terminal : Time) : Set₁ where
    field
      structure :
        Packet.LivePhysicalPacketStructure D C cutoff

      retainedMargin : ℚ
      retainedMarginPositive : 0ℚ < retainedMargin

      integratedResidualNonnegative :
        0ℚ ≤
        G.integratedOrbitAlignedResidual
          cutoff retainedMargin terminal

  open OrbitAlignedResidualPayment public

  packetBelowCombinedGivesDifferenceNonnegative :
    (packet combined : ℚ) →
    packet ≤ combined →
    0ℚ ≤ combined - packet
  packetBelowCombinedGivesDifferenceNonnegative packet combined h =
    let
      translated :
        packet + (- packet) ≤ combined + (- packet)
      translated = ℚP.+-mono-≤ h ℚP.≤-refl
    in
    subst
      (0ℚ ≤_)
      (solve (combined ∷ packet ∷ []))
      (subst
        (_≤ combined + (- packet))
        (solve (packet ∷ []))
        translated)

  differenceNonnegativeGivesPacketBelowCombined :
    (packet combined : ℚ) →
    0ℚ ≤ combined - packet →
    packet ≤ combined
  differenceNonnegativeGivesPacketBelowCombined packet combined h =
    let
      translated :
        0ℚ + packet ≤ (combined - packet) + packet
      translated = ℚP.+-mono-≤ h ℚP.≤-refl
    in
    subst
      (packet ≤_)
      (solve (combined ∷ packet ∷ []))
      (subst
        (_≤ (combined - packet) + packet)
        (solve (packet ∷ []))
        translated)

  r742BuildsOrbitAlignedResidualPayment :
    (cutoff : Nat) (terminal : Time) →
    W2.IntegratedPhysicalPacketCombinedPayment cutoff terminal →
    OrbitAlignedResidualPayment cutoff terminal
  r742BuildsOrbitAlignedResidualPayment cutoff terminal P = record
    { structure = W2.structure P
    ; retainedMargin = W2.retainedMargin P
    ; retainedMarginPositive = W2.retainedMarginPositive P
    ; integratedResidualNonnegative = paid
    }
    where
    margin = W2.retainedMargin P
    packet =
      Packet.integratedPhysicalPacketStrictSurplus
        D cutoff margin terminal
    combined =
      Combined.integratedCombinedSelfExternal cutoff terminal
    residual =
      G.integratedOrbitAlignedResidual cutoff margin terminal

    differenceNonnegative :
      0ℚ ≤ combined - packet
    differenceNonnegative =
      packetBelowCombinedGivesDifferenceNonnegative
        packet combined
        (W2.packetSurplusPaidByCombined P)

    scaled :
      0ℚ ≤ R744.three * (combined - packet)
    scaled =
      let
        gap = combined - packet

        doubled :
          0ℚ + 0ℚ ≤ gap + gap
        doubled =
          ℚP.+-mono-≤ differenceNonnegative differenceNonnegative

        tripled :
          (0ℚ + 0ℚ) + 0ℚ ≤ (gap + gap) + gap
        tripled =
          ℚP.+-mono-≤ doubled differenceNonnegative
      in
      subst
        (0ℚ ≤_)
        (solve (gap ∷ R744.three ∷ []))
        (subst
          (_≤ (gap + gap) + gap)
          (solve [])
          tripled)

    paid :
      0ℚ ≤ residual
    paid =
      subst
        (0ℚ ≤_)
        (sym
          (G.integratedResidualIsThreeCombinedMinusPacket
            cutoff (W2.structure P) margin terminal))
        scaled

  orbitAlignedResidualPaymentBuildsR742 :
    (cutoff : Nat) (terminal : Time) →
    OrbitAlignedResidualPayment cutoff terminal →
    W2.IntegratedPhysicalPacketCombinedPayment cutoff terminal
  orbitAlignedResidualPaymentBuildsR742 cutoff terminal P = record
    { W2.structure = structure P
    ; W2.retainedMargin = retainedMargin P
    ; W2.retainedMarginPositive = retainedMarginPositive P
    ; W2.packetSurplusPaidByCombined = paid
    }
    where
    margin = retainedMargin P
    packet =
      Packet.integratedPhysicalPacketStrictSurplus
        D cutoff margin terminal
    combined =
      Combined.integratedCombinedSelfExternal cutoff terminal

    scaledNonnegative :
      0ℚ ≤ R744.three * (combined - packet)
    scaledNonnegative =
      subst
        (0ℚ ≤_)
        (G.integratedResidualIsThreeCombinedMinusPacket
          cutoff (structure P) margin terminal)
        (integratedResidualNonnegative P)

    differenceNonnegative :
      0ℚ ≤ combined - packet
    differenceNonnegative =
      let
        normalized :
          R744.three * 0ℚ
          ≤ R744.three * (combined - packet)
        normalized =
          subst
            (_≤ R744.three * (combined - packet))
            (solve [])
            scaledNonnegative
      in
      ℚP.*-cancelˡ-≤-pos
        R744.three normalized

    paid : packet ≤ combined
    paid =
      differenceNonnegativeGivesPacketBelowCombined
        packet combined differenceNonnegative

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round747W2ExactlyEquivalentToResidualNonnegativity : Bool
round747W2ExactlyEquivalentToResidualNonnegativity = true

round747PreferredW2SurfaceIsOneSignedSpacetimeResidual : Bool
round747PreferredW2SurfaceIsOneSignedSpacetimeResidual = true

round747IntroducesEstimate : Bool
round747IntroducesEstimate = false

round747IntegratedResidualNonnegativeClosed : Bool
round747IntegratedResidualNonnegativeClosed = false

round747ClayPromotion : Bool
round747ClayPromotion = false

round747W2ExactlyEquivalentToResidualNonnegativityIsTrue :
  round747W2ExactlyEquivalentToResidualNonnegativity ≡ true
round747W2ExactlyEquivalentToResidualNonnegativityIsTrue = refl

round747PreferredW2SurfaceIsOneSignedSpacetimeResidualIsTrue :
  round747PreferredW2SurfaceIsOneSignedSpacetimeResidual ≡ true
round747PreferredW2SurfaceIsOneSignedSpacetimeResidualIsTrue = refl

round747IntroducesEstimateIsFalse :
  round747IntroducesEstimate ≡ false
round747IntroducesEstimateIsFalse = refl

round747IntegratedResidualNonnegativeClosedIsFalse :
  round747IntegratedResidualNonnegativeClosed ≡ false
round747IntegratedResidualNonnegativeClosedIsFalse = refl

round747ClayPromotionIsFalse :
  round747ClayPromotion ≡ false
round747ClayPromotionIsFalse = refl
