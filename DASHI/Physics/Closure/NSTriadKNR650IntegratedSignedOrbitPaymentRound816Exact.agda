{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650IntegratedSignedOrbitPaymentRound816Exact where

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

F : C3.RealField _
F = Rational.rationalRealField

module IntegratedSignedOrbitCompiler
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



  module Weld = R815.SignedOrbitPacketWeld
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

  module Packet = W2.Packet
  module Combined = W2.Combined

  six : ℚ
  six = Weld.six

  onePositive : 0ℚ < 1ℚ
  onePositive = ℚP.positive⁻¹ 1ℚ

  twoPositive : 0ℚ < 1ℚ + 1ℚ
  twoPositive = ℚP.+-mono-<-< onePositive onePositive

  threePositive : 0ℚ < (1ℚ + 1ℚ) + 1ℚ
  threePositive = ℚP.+-mono-<-< twoPositive onePositive

  sixPositive : 0ℚ < six
  sixPositive =
    subst (0ℚ <_)
      (sym (solve []))
      (ℚP.+-mono-<-< threePositive threePositive)

  module At
      (cutoff : Nat)
      (margin : ℚ)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    orbitRate : Time → ℚ
    orbitRate time =
      Weld.At.signedOrbitPaymentRate cutoff time S margin

    integratedOrbitPayment : Time → ℚ
    integratedOrbitPayment terminal =
      integrateTo orbitRate terminal

    combinedRate : Time → ℚ
    combinedRate time = Combined.combinedResidueAt cutoff time

    packetRate : Time → ℚ
    packetRate time =
      Packet.physicalPacketStrictSurplusRate D cutoff margin time

    gapRate : Time → ℚ
    gapRate time = combinedRate time - packetRate time

    integratedCombined : Time → ℚ
    integratedCombined terminal =
      Combined.integratedCombinedSelfExternal cutoff terminal

    integratedPacket : Time → ℚ
    integratedPacket terminal =
      Packet.integratedPhysicalPacketStrictSurplus D cutoff margin terminal

    negOne : ℚ
    negOne = 0ℚ - 1ℚ

    gapIsSum :
      (time : Time) →
      gapRate time ≡ combinedRate time + negOne * packetRate time
    gapIsSum time = solve (combinedRate time ∷ packetRate time ∷ [])

    integratedGapIsDifference :
      (terminal : Time) →
      integrateTo gapRate terminal
      ≡ integratedCombined terminal - integratedPacket terminal
    integratedGapIsDifference terminal =
      trans
        (Energy.integrationCongruent integrationLinearity
          gapIsSum terminal)
        (trans
          (Energy.integrationAdditive integrationLinearity
            combinedRate
            (λ time → negOne * packetRate time)
            terminal)
          (trans
            (cong
              (integratedCombined terminal +_)
              (Energy.integrationConstantScale integrationLinearity
                negOne packetRate terminal))
            (solve
              ( integratedCombined terminal
              ∷ integratedPacket terminal
              ∷ []))))

    integratedOrbitIsSixPhysicalGap :
      (terminal : Time) →
      integratedOrbitPayment terminal
      ≡ six * (integratedCombined terminal - integratedPacket terminal)
    integratedOrbitIsSixPhysicalGap terminal =
      trans
        (Weld.integratedWeld cutoff margin terminal (λ _ → S))
        (cong (six *_) (integratedGapIsDifference terminal))

    -- A lower bound is an analytic hypothesis. It cannot be manufactured
    -- from R815's equality, and linearity alone does not imply monotonicity.
    record SignedSpacetimePayment (terminal : Time) : Set where
      field
        integratedSignedNonnegative :
          0ℚ ≤ integratedOrbitPayment terminal

    integratedPaymentBuildsR742 :
      (terminal : Time) →
      SignedSpacetimePayment terminal →
      Packet.integratedPhysicalPacketStrictSurplus D cutoff margin terminal
      ≤ Combined.integratedCombinedSelfExternal cutoff terminal
    integratedPaymentBuildsR742 terminal payment =
      let
        combined = integratedCombined terminal
        packet = integratedPacket terminal
        scaled :
          six * 0ℚ ≤ six * (combined - packet)
        scaled =
          subst
            (λ lhs → lhs ≤ six * (combined - packet))
            (solve [])
            (subst
              (0ℚ ≤_)
              (integratedOrbitIsSixPhysicalGap terminal)
              (SignedSpacetimePayment.integratedSignedNonnegative payment))

        gapNonnegative : 0ℚ ≤ combined - packet
        gapNonnegative =
          ℚP.*-cancelˡ-≤-pos six scaled

        packetUpper : packet ≤ combined
        packetUpper =
          ℚP.+-cancelˡ-≤ (0ℚ - packet)
            (subst
              (λ left → left ≤ combined - packet)
              (solve (packet ∷ []))
              gapNonnegative)
      in packetUpper

  record LiveIntegratedSignedOrbitPayment
      (cutoff : Nat)
      (terminal : Time) : Set₁ where
    field
      structure : Packet.LivePhysicalPacketStructure D C cutoff
      retainedMargin : ℚ
      retainedMarginPositive : 0ℚ < retainedMargin
      signedNonnegative :
        0ℚ ≤ At.integratedOrbitPayment cutoff retainedMargin
          structure terminal

  signedOrbitBuildsR742 :
    (cutoff : Nat) (terminal : Time) →
    LiveIntegratedSignedOrbitPayment cutoff terminal →
    W2.IntegratedPhysicalPacketCombinedPayment cutoff terminal
  signedOrbitBuildsR742 cutoff terminal P =
    record
      { W2.structure = LiveIntegratedSignedOrbitPayment.structure P
      ; W2.retainedMargin = LiveIntegratedSignedOrbitPayment.retainedMargin P
      ; W2.retainedMarginPositive =
          LiveIntegratedSignedOrbitPayment.retainedMarginPositive P
      ; W2.packetSurplusPaidByCombined =
          At.integratedPaymentBuildsR742
            cutoff
            (LiveIntegratedSignedOrbitPayment.retainedMargin P)
            (LiveIntegratedSignedOrbitPayment.structure P)
            terminal
            (record
              { At.SignedSpacetimePayment.integratedSignedNonnegative =
                  LiveIntegratedSignedOrbitPayment.signedNonnegative P
              })
      }

  signedOrbitBuildsR734AugmentedW2 :
    (cutoff : Nat) (terminal : Time) →
    LiveIntegratedSignedOrbitPayment cutoff terminal →
    W2.Aug.AugmentedCriticalWeightedPayment cutoff terminal
  signedOrbitBuildsR734AugmentedW2 cutoff terminal P =
    W2.packetCombinedBuildsAugmentedW2 cutoff terminal
      (signedOrbitBuildsR742 cutoff terminal P)

round816R815IntegralConvertedToActualR742Consumer : Bool
round816R815IntegralConvertedToActualR742Consumer = true

round816RetainsIntegratedNotPointwisePayment : Bool
round816RetainsIntegratedNotPointwisePayment = true

round816RetainsPositiveMargin : Bool
round816RetainsPositiveMargin = true

round816ImpliesMarginBelowTwiceViscosity : Bool
round816ImpliesMarginBelowTwiceViscosity = false

round816SignedPaymentClosed : Bool
round816SignedPaymentClosed = false

round816W1Closed : Bool
round816W1Closed = false

round816ClayPromotion : Bool
round816ClayPromotion = false

round816SignedPaymentClosedIsFalse :
  round816SignedPaymentClosed ≡ false
round816SignedPaymentClosedIsFalse = refl

round816ImpliesMarginBelowTwiceViscosityIsFalse :
  round816ImpliesMarginBelowTwiceViscosity ≡ false
round816ImpliesMarginBelowTwiceViscosityIsFalse = refl
