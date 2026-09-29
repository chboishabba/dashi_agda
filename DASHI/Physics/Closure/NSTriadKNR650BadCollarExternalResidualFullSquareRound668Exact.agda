{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarExternalResidualFullSquareRound668Exact where

------------------------------------------------------------------------
-- ROUND668 / R667 EXTERNAL NETWORK -> LITERAL R112 RESIDUAL FULL SQUARE
--
-- R609 rewrites ONE R606 external forcing pair, given the already-defined
-- ThreeLegResidualMembership witnesses for alpha and swap(alpha), as four
-- selected pairings against literal self-orbit-removed R112 residual vectors.
--
-- The R607/R667 external-network scalar is the COMPLETE fixed-output full
-- square of exactly those R606 pairs, multiplied by rateTotal.  Therefore a
-- fibre-wide residual-membership authority lifts the R609 pointwise identity
-- without estimate:
--
--   ExternalForcingFull
--     = fullSquare ResidualExternalPair
--
-- and
--
--   ExternalNetworkContribution
--     = rateTotal * fullSquare ResidualExternalPair.
--
-- This closes only the representation seam.  No Waleffe-cell identification,
-- sign, cancellation, norm estimate, or cutoff-uniform payment is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; Positive; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedFullSquareRateCancellationExact as Cauchy
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeResidualCarrierRound112Exact as R112
import DASHI.Physics.Closure.NSTriadKNR567ExternalResidualPairExpansionRound609Exact as R609
import DASHI.Physics.Closure.NSTriadKNA3CauchyMismatchNetworkSplitRound607Exact as R607

F : C3.RealField _
F = Rational.rationalRealField

module ResidualFullSquare
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode)
    (membership :
      (tau : Physical.PhysicalTriadIncidence) →
      R112.ThreeLegResidualMembership
        (Field30.finiteSystem physicalSystem) tau) where

  module E = R609.FixedOutput physicalSystem S output

  fibre : List Physical.PhysicalTriadIncidence
  fibre = E.Split.fibre

  residualExternalPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  residualExternalPair alpha beta =
    E.Split.C.T.Swap.pairResolvent alpha beta
      * E.residualWitnessPairingSum
          alpha beta
          (membership alpha)
          (membership (Symmetry.swapTriad alpha))

  externalPairIsResidualPair :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    E.Split.externalForcingPair alpha beta
    ≡ residualExternalPair alpha beta
  externalPairIsResidualPair alpha beta =
    E.externalForcingPairOnLiteralResidualCarriers
      alpha beta
      (membership alpha)
      (membership (Symmetry.swapTriad alpha))

  externalForcingFullOnResidualCarrier :
    E.Split.externalForcingFull
    ≡ R543.fullSquareSum residualExternalPair fibre
  externalForcingFullOnResidualCarrier =
    Cauchy.fullSquareCongruent
      E.Split.externalForcingPair
      residualExternalPair
      externalPairIsResidualPair
      fibre

module ExternalNetworkCarrier
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (Audit.velocityAt (Field30.finiteSystem physicalSystem)))
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output)
    (membership :
      (tau : Physical.PhysicalTriadIncidence) →
      R112.ThreeLegResidualMembership
        (Field30.finiteSystem physicalSystem) tau) where

  module Split = R607.FixedOutput
    physicalSystem S L H P viscosityPositive output outputNonzero

  module Residual =
    ResidualFullSquare physicalSystem S output membership

  residualExternalFull : ℚ
  residualExternalFull =
    R543.fullSquareSum
      Residual.residualExternalPair
      Residual.fibre

  externalNetworkContributionOnResidualCarrier :
    Split.externalNetworkContribution
    ≡ Split.rateTotal * residualExternalFull
  externalNetworkContributionOnResidualCarrier =
    cong
      (Split.rateTotal *_)
      Residual.externalForcingFullOnResidualCarrier

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round668ExternalForcingFullOnLiteralR112ResidualCarrier : Bool
round668ExternalForcingFullOnLiteralR112ResidualCarrier = true

round668ExternalNetworkContributionOnLiteralResidualFullSquare : Bool
round668ExternalNetworkContributionOnLiteralResidualFullSquare = true

round668RequiresFibreWideThreeLegResidualMembership : Bool
round668RequiresFibreWideThreeLegResidualMembership = true

round668IdentifiesResidualPairingsWithR115WaleffeCells : Bool
round668IdentifiesResidualPairingsWithR115WaleffeCells = false

round668ExternalNetworkQuantitativePaymentClosed : Bool
round668ExternalNetworkQuantitativePaymentClosed = false

round668IntroducesEstimate : Bool
round668IntroducesEstimate = false

round668IntroducesNewClayLeaf : Bool
round668IntroducesNewClayLeaf = false

round668C2Closed : Bool
round668C2Closed = false

round668ClayPromotion : Bool
round668ClayPromotion = false

round668ExternalForcingFullOnLiteralR112ResidualCarrierIsTrue :
  round668ExternalForcingFullOnLiteralR112ResidualCarrier ≡ true
round668ExternalForcingFullOnLiteralR112ResidualCarrierIsTrue = refl

round668ExternalNetworkContributionOnLiteralResidualFullSquareIsTrue :
  round668ExternalNetworkContributionOnLiteralResidualFullSquare ≡ true
round668ExternalNetworkContributionOnLiteralResidualFullSquareIsTrue = refl

round668RequiresFibreWideThreeLegResidualMembershipIsTrue :
  round668RequiresFibreWideThreeLegResidualMembership ≡ true
round668RequiresFibreWideThreeLegResidualMembershipIsTrue = refl

round668IdentifiesResidualPairingsWithR115WaleffeCellsIsFalse :
  round668IdentifiesResidualPairingsWithR115WaleffeCells ≡ false
round668IdentifiesResidualPairingsWithR115WaleffeCellsIsFalse = refl

round668ExternalNetworkQuantitativePaymentClosedIsFalse :
  round668ExternalNetworkQuantitativePaymentClosed ≡ false
round668ExternalNetworkQuantitativePaymentClosedIsFalse = refl

round668IntroducesEstimateIsFalse :
  round668IntroducesEstimate ≡ false
round668IntroducesEstimateIsFalse = refl

round668IntroducesNewClayLeafIsFalse :
  round668IntroducesNewClayLeaf ≡ false
round668IntroducesNewClayLeafIsFalse = refl

round668C2ClosedIsFalse :
  round668C2Closed ≡ false
round668C2ClosedIsFalse = refl

round668ClayPromotionIsFalse :
  round668ClayPromotion ≡ false
round668ClayPromotionIsFalse = refl
