{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CanonicalViscosityMarginPaymentRound816Exact where

------------------------------------------------------------------------
-- ROUND816 / CANONICAL RETAINED MARGIN delta = nu
--
-- R815 leaves the exact integrated signed payment at an arbitrary retained
-- margin delta:
--
--   integral Orbit_delta
--     = 6 * integral (Combined - Packet_delta).
--
-- The live support already carries Positive nu, and nu is one physical
-- trajectory constant, independent of cutoff and time.  Choose
--
--   delta := nu.
--
-- Then the retained coefficient simplifies exactly:
--
--   2*nu - delta = nu > 0.
--
-- Hence ONE signed analytic theorem at this canonical margin,
--
--   0 <= integral Orbit_nu,
--
-- directly constructs R742's IntegratedPhysicalPacketCombinedPayment with
-- retainedMargin = nu.  This removes a separate "uniform positive margin"
-- theorem from the downstream compiler: the common floor may be chosen as the
-- physical viscosity itself.
--
-- No signed estimate is proved here.  The input nonnegativity remains the
-- central analytic leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; Positive; _+_; _-_; _*_; -_; _≤_; _<_; _/_; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

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
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNR650SignedOrbitPacketWeldRound815Exact as R815
import DASHI.Physics.Closure.NSTriadKNR650IntegratedW2PhysicalPacketCombinedRound742Exact as R742

F : C3.RealField _
F = Rational.rationalRealField

module CanonicalViscosityMarginPayment
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
      R417.HermitianDerivativeCalculus Time VectorDerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
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

  module Live =
    R408.LiteralDynamics
      Time initialTime integrateTo VectorDerivativeOf

  module Support =
    R405.LiteralCutoffSupport
      Time initialTime integrateTo VectorDerivativeOf

  module Weld =
    R815.SignedOrbitPacketWeld
      Time initialTime integrateTo
      VectorDerivativeOf ScalarDerivativeOf
      projectedCross vectorAlgebra zeroCalculus
      hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
      FTC integrationLinearity integrationTransport D C R

  module W2 =
    R742.IntegratedPhysicalW2
      Time initialTime integrateTo
      VectorDerivativeOf ScalarDerivativeOf
      projectedCross vectorAlgebra zeroCalculus
      hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
      FTC integrationLinearity integrationTransport D C R

  nu : ℚ
  nu = Live.physicalViscosity (Live.support D)

  nuPositive : 0ℚ < nu
  nuPositive = ℚP.positive⁻¹ (Support.physicalViscosityPositive R)

  canonicalCoefficient :
    (cutoff : Nat) →
    (time : Time) →
    (S : Weld.Packet.LivePhysicalPacketStructure D C cutoff) →
    Weld.At.coefficient cutoff time S nu ≡ nu
  canonicalCoefficient cutoff time S =
    solve (nu ∷ Fold.two ∷ [])

  canonicalOrbitRate :
    (cutoff : Nat) →
    Weld.Packet.LivePhysicalPacketStructure D C cutoff →
    Time → ℚ
  canonicalOrbitRate cutoff S time =
    Weld.At.signedOrbitPaymentRate cutoff time S nu

  canonicalOrbitIntegral :
    (cutoff : Nat) →
    Weld.Packet.LivePhysicalPacketStructure D C cutoff →
    Time → ℚ
  canonicalOrbitIntegral cutoff S terminal =
    integrateTo (canonicalOrbitRate cutoff S) terminal

  integratedGapMeaning :
    (cutoff : Nat) →
    (S : Weld.Packet.LivePhysicalPacketStructure D C cutoff) →
    (terminal : Time) →
    integrateTo
      (λ time → Weld.At.combinedMinusPacket cutoff time S nu)
      terminal
    ≡
    Weld.Combined.integratedCombinedSelfExternal cutoff terminal
      - Weld.Packet.integratedPhysicalPacketStrictSurplus
          D cutoff nu terminal
  integratedGapMeaning cutoff S terminal =
    let
      combined =
        Weld.Combined.integratedCombinedSelfExternal cutoff terminal
      packet =
        Weld.Packet.integratedPhysicalPacketStrictSurplus
          D cutoff nu terminal

      additive =
        Energy.integrationAdditive integrationLinearity
          (Weld.Combined.combinedResidueAt cutoff)
          (λ time →
            - Weld.Packet.physicalPacketStrictSurplusRate
                D cutoff nu time)
          terminal

      negative =
        Energy.integrationConstantScale integrationLinearity
          (- (+ 1 / 1))
          (Weld.Packet.physicalPacketStrictSurplusRate D cutoff nu)
          terminal
    in
    trans
      (Energy.integrationCongruent integrationLinearity
        (λ time →
          solve
            ( Weld.Combined.combinedResidueAt cutoff time
            ∷ Weld.Packet.physicalPacketStrictSurplusRate D cutoff nu time
            ∷ []))
        terminal)
      (trans additive
        (trans
          (cong
            (combined +_)
            (trans
              (Energy.integrationCongruent integrationLinearity
                (λ time →
                  solve
                    ( Weld.Packet.physicalPacketStrictSurplusRate
                        D cutoff nu time
                    ∷ []))
                terminal)
              negative))
          (solve (combined ∷ packet ∷ []))))

  sixLiteral : ℚ
  sixLiteral = + 6 / 1

  sixMeaning : Weld.six ≡ sixLiteral
  sixMeaning = solve []

  sixPositive : 0ℚ < Weld.six
  sixPositive =
    subst (0ℚ <_) (sym sixMeaning) (ℚP.positive⁻¹ sixLiteral)

  signedPaymentBuildsPacketCombined :
    (cutoff : Nat) →
    (S : Weld.Packet.LivePhysicalPacketStructure D C cutoff) →
    (terminal : Time) →
    0ℚ ≤ canonicalOrbitIntegral cutoff S terminal →
    W2.IntegratedPhysicalPacketCombinedPayment cutoff terminal
  signedPaymentBuildsPacketCombined cutoff S terminal payment =
    let
      gapIntegral =
        integrateTo
          (λ time → Weld.At.combinedMinusPacket cutoff time S nu)
          terminal

      welded :
        canonicalOrbitIntegral cutoff S terminal
        ≡ Weld.six * gapIntegral
      welded =
        Weld.integratedWeld cutoff nu terminal (λ _ → S)

      scaledNonnegative :
        0ℚ ≤ Weld.six * gapIntegral
      scaledNonnegative =
        subst (0ℚ ≤_) welded payment

      factorized :
        Weld.six * 0ℚ ≤ Weld.six * gapIntegral
      factorized =
        subst (_≤ Weld.six * gapIntegral)
          (solve (Weld.six ∷ []))
          scaledNonnegative

      gapNonnegative : 0ℚ ≤ gapIntegral
      gapNonnegative =
        let
          instance
            sixPositiveInstance : Positive Weld.six
            sixPositiveInstance = positive sixPositive
        in
        ℚP.*-cancelˡ-≤-pos Weld.six factorized

      physicalGapNonnegative :
        0ℚ ≤
          Weld.Combined.integratedCombinedSelfExternal cutoff terminal
            - Weld.Packet.integratedPhysicalPacketStrictSurplus
                D cutoff nu terminal
      physicalGapNonnegative =
        subst (0ℚ ≤_)
          (integratedGapMeaning cutoff S terminal)
          gapNonnegative

      packetBelowCombined :
        Weld.Packet.integratedPhysicalPacketStrictSurplus
            D cutoff nu terminal
        ≤ Weld.Combined.integratedCombinedSelfExternal cutoff terminal
      packetBelowCombined =
        let
          packet =
            Weld.Packet.integratedPhysicalPacketStrictSurplus
              D cutoff nu terminal
          combined =
            Weld.Combined.integratedCombinedSelfExternal cutoff terminal
          shifted =
            ℚP.+-mono-≤ physicalGapNonnegative ℚP.≤-refl
        in
        subst
          (λ left → left ≤ combined)
          (solve (packet ∷ []))
          (subst
            (λ right → 0ℚ + packet ≤ right)
            (solve (combined ∷ packet ∷ []))
            shifted)
    in
    record
      { W2.structure = S
      ; W2.retainedMargin = nu
      ; W2.retainedMarginPositive = nuPositive
      ; W2.packetSurplusPaidByCombined = packetBelowCombined
      }

round816CanonicalMarginIsPhysicalViscosity : Bool
round816CanonicalMarginIsPhysicalViscosity = true

round816RetainedCoefficientIsPositiveViscosity : Bool
round816RetainedCoefficientIsPositiveViscosity = true

round816UniformMarginSeparateLeafRequired : Bool
round816UniformMarginSeparateLeafRequired = false

round816SignedPaymentAtCanonicalMarginBuildsR742 : Bool
round816SignedPaymentAtCanonicalMarginBuildsR742 = true

round816SignedPaymentClosed : Bool
round816SignedPaymentClosed = false

round816IntroducesEstimate : Bool
round816IntroducesEstimate = false

round816ClayPromotion : Bool
round816ClayPromotion = false
