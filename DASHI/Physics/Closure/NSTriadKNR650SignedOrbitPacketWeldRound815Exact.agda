{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SignedOrbitPacketWeldRound815Exact where

------------------------------------------------------------------------
-- ROUND781 / EXACT TWO-FAMILY SPLIT OF THE SWAP-PAIRED W2 RESIDUAL
--
-- R777-R780 classify every separated-base energy orbit.  The invariant that
-- survives swap pairing and retains cyclic information is:
--
--   ccTouched(beta)
--     iff at least one coordinate of Pi(beta) is comparable.
--
-- Define the complementary family as fullySeparated.
--
-- The predicate is exactly swap-invariant because R775 transports profiles by
--
--   (c0,cp,cq) -> (swapClass c0,cq,cp),
--
-- and swapClass fixes comparable.
--
-- The R760 paired residual is then split pointwise and globally as
--
--   PairD = FullySeparatedD + CCTouchedD.
--
-- No sign or estimate is asserted for either family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

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

F : C3.RealField _
F = Rational.rationalRealField

module SignedOrbitPacketWeld
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


  module Two = R781.TwoFamilyResidual
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Two.Packet
  module Combined = Two.Paired.Local.O.W2.Combined

  six : ℚ
  six = Fold.two * R744.three

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module P = Two.At cutoff time S
    module Paired = P.P
    module Diff = Paired.Base
    module Orbit = Diff.Base

    separated : ℚ
    separated = P.fullySeparatedFold

    touched : ℚ
    touched = P.ccTouchedFold

    coefficient : ℚ → ℚ
    coefficient margin = Orbit.retainedCoefficient margin

    dissipation : ℚ
    dissipation = Two.Paired.Local.O.W2.K.dissipationAt cutoff time

    signedOrbitPaymentRate : ℚ → ℚ
    signedOrbitPaymentRate margin =
      separated + touched
        + six * coefficient margin * dissipation

    combinedMinusPacket : ℚ → ℚ
    combinedMinusPacket margin =
      Combined.combinedResidueAt cutoff time
        - Packet.physicalPacketStrictSurplusRate D cutoff margin time

    -- R781 partitions the paired nonlinear residual; R760 gives the
    -- factor 2, R749 returns to R745, and R745 supplies the factor 3.
    signedOrbitRateIsSixPhysicalGap :
      (margin : ℚ) →
      signedOrbitPaymentRate margin
      ≡ six * combinedMinusPacket margin
    signedOrbitRateIsSixPhysicalGap margin =
      let
        orbit = Orbit.orbitAlignedFold
        coeff = coefficient margin
        diss = dissipation
        gap = combinedMinusPacket margin

        pairedToOrbit :
          separated + touched ≡ Fold.two * orbit
        pairedToOrbit =
          trans
            (sym P.completeResidualFoldSplits)
            (trans
              Paired.swapPairedFoldIsTwiceResidualFold
              (cong (Fold.two *_) Diff.differenceAlignedFoldIsR745OrbitAlignedFold))

        normal :
          (Fold.two * orbit) + six * coeff * diss
          ≡ Fold.two * Orbit.orbitAlignedResidual margin
        normal = solve (Fold.two ∷ R744.three ∷ orbit ∷ coeff ∷ diss ∷ [])

        physical :
          Orbit.orbitAlignedResidual margin
          ≡ R744.three * gap
        physical = Orbit.residualIsThreeCombinedMinusPacket S margin
      in
      trans
        (cong (_+ six * coeff * diss) pairedToOrbit)
        (trans normal
          (trans
            (cong (Fold.two *_) physical)
            (solve (Fold.two ∷ R744.three ∷ gap ∷ []))))

  -- A live packet structure for each time is necessary for the pointwise
  -- identification. This integral theorem does not assert a sign.
  integratedWeld :
    (cutoff : Nat) (margin : ℚ) (terminal : Time) →
    (structureAt :
      (time : Time) → Packet.LivePhysicalPacketStructure D C cutoff) →
    integrateTo
      (λ time → At.signedOrbitPaymentRate cutoff time
        (structureAt time) margin)
      terminal
    ≡
    six * integrateTo
      (λ time → At.combinedMinusPacket cutoff time
        (structureAt time) margin)
      terminal
  integratedWeld cutoff margin terminal structureAt =
    trans
      (Energy.integrationCongruent integrationLinearity
        (λ time → At.signedOrbitRateIsSixPhysicalGap
          cutoff time (structureAt time) margin)
        terminal)
      (Energy.integrationConstantScale integrationLinearity six
        (λ time → At.combinedMinusPacket
          cutoff time (structureAt time) margin)
        terminal)

round815PointwiseSignedWeldExact : Bool
round815PointwiseSignedWeldExact = true

round815SixFactorAndViscousTermPreserved : Bool
round815SixFactorAndViscousTermPreserved = true

round815IntegratedWeldIsEqualityNotPayment : Bool
round815IntegratedWeldIsEqualityNotPayment = true

round815SignedInequalityClosed : Bool
round815SignedInequalityClosed = false

round815ClayPromotion : Bool
round815ClayPromotion = false
