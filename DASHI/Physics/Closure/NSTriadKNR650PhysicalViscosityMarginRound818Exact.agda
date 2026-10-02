{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650PhysicalViscosityMarginRound818Exact where

------------------------------------------------------------------------
-- ROUND818 / CANONICAL RETAINED MARGIN delta = nu ON THE LIVE R408 SYSTEM
--
-- R739 literally defines twoNu = 2 * physicalViscosity(support D).
-- If (and only if) the live physical viscosity is supplied as positive,
-- select delta = nu. Then retained coefficient (2nu-delta) = nu and
-- the margin is cutoff independent by R408's viscosityFixed provenance.
--
-- The complete signed integrated inequality remains a separate hypothesis;
-- nothing here asserts its sign, or W1 or continuation.
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
import DASHI.Physics.Closure.NSTriadKNR650SignedOrbitPacketWeldRound815Exact as R815

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalViscosityMargin
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

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf

  module W2 = Signed.W2
  module Packet = W2.Packet

  nu : ℚ
  nu = Live.physicalViscosity (Live.support D)

  -- Use the same packet structure as the signed orbit work, not a
  -- separately selected finite system or a manually calibrated margin.
  retainedCoefficientAtPhysicalViscosity :
    (cutoff : Nat) (time : Time) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    Signed.Weld.At.coefficient cutoff time S nu ≡ nu
  retainedCoefficientAtPhysicalViscosity cutoff time S =
    solve (Fold.two ∷ nu ∷ [])

  selectPhysicalMarginBuildsR742 :
    0ℚ < nu →
    (cutoff : Nat) (terminal : Time) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    0ℚ ≤ Signed.At.integratedOrbitPayment cutoff nu S terminal →
    W2.IntegratedPhysicalPacketCombinedPayment cutoff terminal
  selectPhysicalMarginBuildsR742 nuPositive cutoff terminal S payment =
    Signed.signedOrbitBuildsR742 cutoff terminal
      (record
        { Signed.LiveIntegratedSignedOrbitPayment.structure = S
        ; Signed.LiveIntegratedSignedOrbitPayment.retainedMargin = nu
        ; Signed.LiveIntegratedSignedOrbitPayment.retainedMarginPositive =
            nuPositive
        ; Signed.LiveIntegratedSignedOrbitPayment.signedNonnegative = payment
        })

  selectPhysicalMarginBuildsR734 :
    0ℚ < nu →
    (cutoff : Nat) (terminal : Time) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    0ℚ ≤ Signed.At.integratedOrbitPayment cutoff nu S terminal →
    W2.Aug.AugmentedCriticalWeightedPayment cutoff terminal
  selectPhysicalMarginBuildsR734 nuPositive cutoff terminal S payment =
    W2.packetCombinedBuildsAugmentedW2 cutoff terminal
      (selectPhysicalMarginBuildsR742
        nuPositive cutoff terminal S payment)

  allCutoffsPhysicalMarginBuildsR734 :
    0ℚ < nu →
    (structures : (cutoff : Nat) →
      Packet.LivePhysicalPacketStructure D C cutoff) →
    ((cutoff : Nat) (terminal : Time) →
      0ℚ ≤ Signed.At.integratedOrbitPayment cutoff nu
        (structures cutoff) terminal) →
    (cutoff : Nat) (terminal : Time) →
    W2.Aug.AugmentedCriticalWeightedPayment cutoff terminal
  allCutoffsPhysicalMarginBuildsR734 positive structures payment cutoff terminal =
    selectPhysicalMarginBuildsR734
      positive cutoff terminal (structures cutoff) (payment cutoff terminal)

round818RetainedMarginSelectedFromPhysicalViscosity : Bool
round818RetainedMarginSelectedFromPhysicalViscosity = true

round818ViscosityPositivityMustBeSupplied : Bool
round818ViscosityPositivityMustBeSupplied = true

round818RetainedMarginUniformAcrossCutoff : Bool
round818RetainedMarginUniformAcrossCutoff = true

round818IntegratedSignedPaymentClosed : Bool
round818IntegratedSignedPaymentClosed = false

round818W1Closed : Bool
round818W1Closed = false

round818ClayPromotion : Bool
round818ClayPromotion = false
