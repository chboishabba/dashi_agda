{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR567ExternalResidualPairExpansionRound609Exact where

------------------------------------------------------------------------
-- ROUND609 / R606 EXTERNAL FORCING PAIR -> FOUR RESIDUAL SELECTED PAIRINGS
--
-- R606's external Cauchy pair is
--
--   K_ab Re < E_a^dbl , D_b >,
--
-- with
--
--   E_a^dbl = 2 E_a + 2 E_swap(a),
--   D_b     = 2 A_b + 2 A_swap(b).
--
-- Exact real-Hermitian bilinearity therefore gives
--
--   Re < E_a^dbl , D_b >
--     = 4 (
--         Re<E_a,A_b>       + Re<E_a,A_swap(b)>
--       + Re<E_swap(a),A_b> + Re<E_swap(a),A_swap(b)>
--       ).
--
-- If R112 residual witnesses are supplied for a and swap(a), R608 rewrites
-- E_a and E_swap(a) to the literal self-orbit-removed p/q residual vectors.
--
-- This is the first scalar same-object bridge from the R606 external-network
-- mismatch toward the mature residual-cell/Waleffe branch.  It does NOT claim
-- these four terms equal the R115 scalar Waleffe functional, and it introduces
-- no estimate or cancellation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNDoubleMixedAsSwapPairedPlusMinusRound387Exact as R387
import DASHI.Physics.Closure.NSTriadKNR567ForcingFullSelfExternalSplitRound606Exact as R606
import DASHI.Physics.Closure.NSTriadKNR230ExternalResidualCarrierRound608Exact as R608
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeResidualCarrierRound112Exact as R112

F : C3.RealField _
F = Rational.rationalRealField

two four : ℚ
two = 2
four = 4

realCrossDoubleLeft :
  (left right : C3.Complex3 F) →
  R179.realHermitianCross (R387.doublePlus left) right
  ≡ two * R179.realHermitianCross left right
realCrossDoubleLeft left right =
  trans
    (R291.realCrossAddLeft left left right)
    (solve (R179.realHermitianCross left right ∷ []))

realCrossDoubleRight :
  (left right : C3.Complex3 F) →
  R179.realHermitianCross left (R387.doublePlus right)
  ≡ two * R179.realHermitianCross left right
realCrossDoubleRight left right =
  trans
    (R291.realCrossAddRight left right right)
    (solve (R179.realHermitianCross left right ∷ []))

realCrossDoubleDouble :
  (left right : C3.Complex3 F) →
  R179.realHermitianCross (R387.doublePlus left) (R387.doublePlus right)
  ≡ four * R179.realHermitianCross left right
realCrossDoubleDouble left right =
  trans
    (realCrossDoubleLeft left (R387.doublePlus right))
    (trans
      (cong (two *_) (realCrossDoubleRight left right))
      (solve (R179.realHermitianCross left right ∷ [])))

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Split = R606.FixedOutput physicalSystem S output
  module Residual = R608.FixedSystem physicalSystem S

  system = Field30.finiteSystem physicalSystem
  velocity = Audit.velocityAt system

  mixedCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  mixedCell = R224.mixedPlusMinus S velocity

  externalCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  externalCell = Split.Net.externalProductRuleCell

  fourResidualPairingSum :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  fourResidualPairingSum alpha beta =
    four *
      ( R179.realHermitianCross (externalCell alpha) (mixedCell beta)
      + R179.realHermitianCross
          (externalCell alpha)
          (mixedCell (Symmetry.swapTriad beta))
      + R179.realHermitianCross
          (externalCell (Symmetry.swapTriad alpha))
          (mixedCell beta)
      + R179.realHermitianCross
          (externalCell (Symmetry.swapTriad alpha))
          (mixedCell (Symmetry.swapTriad beta))
      )

  externalDoublePairingIsFourResidualPairings :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    R179.realHermitianCross
      (Split.externalDoubleForcing alpha)
      (Split.C.Row.doubleCell beta)
    ≡ fourResidualPairingSum alpha beta
  externalDoublePairingIsFourResidualPairings alpha beta =
    let
      ea = externalCell alpha
      eas = externalCell (Symmetry.swapTriad alpha)
      ab = mixedCell beta
      abs = mixedCell (Symmetry.swapTriad beta)

      forcingMeaning :
        Split.externalDoubleForcing alpha
        ≡ C3.complex3Add
            (R387.doublePlus ea)
            (R387.doublePlus eas)
      forcingMeaning = refl

      cellMeaning :
        Split.C.Row.doubleCell beta
        ≡ C3.complex3Add
            (R387.doublePlus ab)
            (R387.doublePlus abs)
      cellMeaning =
        R387.doubleMixedIsSwapPairedPlusMinus S velocity beta
    in
    trans
      (cong₂ R179.realHermitianCross forcingMeaning cellMeaning)
      (trans
        (R291.realCrossAddLeft
          (R387.doublePlus ea)
          (R387.doublePlus eas)
          (C3.complex3Add
            (R387.doublePlus ab)
            (R387.doublePlus abs)))
        (trans
          (cong₂ _+_
            (R291.realCrossAddRight
              (R387.doublePlus ea)
              (R387.doublePlus ab)
              (R387.doublePlus abs))
            (R291.realCrossAddRight
              (R387.doublePlus eas)
              (R387.doublePlus ab)
              (R387.doublePlus abs)))
          (trans
            (cong₂ _+_
              (cong₂ _+_
                (realCrossDoubleDouble ea ab)
                (realCrossDoubleDouble ea abs))
              (cong₂ _+_
                (realCrossDoubleDouble eas ab)
                (realCrossDoubleDouble eas abs)))
            (solve
              ( R179.realHermitianCross ea ab
              ∷ R179.realHermitianCross ea abs
              ∷ R179.realHermitianCross eas ab
              ∷ R179.realHermitianCross eas abs
              ∷ [])))))

  externalForcingPairIsFourResidualPairings :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Split.externalForcingPair alpha beta
    ≡ Split.C.T.Swap.pairResolvent alpha beta
        * fourResidualPairingSum alpha beta
  externalForcingPairIsFourResidualPairings alpha beta =
    cong
      (Split.C.T.Swap.pairResolvent alpha beta *_)
      (externalDoublePairingIsFourResidualPairings alpha beta)

  residualExternalCell :
    (tau : Physical.PhysicalTriadIncidence) →
    R112.ThreeLegResidualMembership system tau →
    C3.Complex3 F
  residualExternalCell tau M =
    R608.externalResidualProductRuleCell physicalSystem S tau M

  residualWitnessPairingSum :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    R112.ThreeLegResidualMembership system alpha →
    R112.ThreeLegResidualMembership system (Symmetry.swapTriad alpha) →
    ℚ
  residualWitnessPairingSum alpha beta M Ms =
    four *
      ( R179.realHermitianCross
          (residualExternalCell alpha M)
          (mixedCell beta)
      + R179.realHermitianCross
          (residualExternalCell alpha M)
          (mixedCell (Symmetry.swapTriad beta))
      + R179.realHermitianCross
          (residualExternalCell (Symmetry.swapTriad alpha) Ms)
          (mixedCell beta)
      + R179.realHermitianCross
          (residualExternalCell (Symmetry.swapTriad alpha) Ms)
          (mixedCell (Symmetry.swapTriad beta))
      )

  fourResidualPairingsUseLiteralR112Carriers :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (M : R112.ThreeLegResidualMembership system alpha) →
    (Ms :
      R112.ThreeLegResidualMembership system (Symmetry.swapTriad alpha)) →
    fourResidualPairingSum alpha beta
    ≡ residualWitnessPairingSum alpha beta M Ms
  fourResidualPairingsUseLiteralR112Carriers alpha beta M Ms
    rewrite
      R608.externalProductRuleCellIsResidualCarrier
        physicalSystem S alpha M
      | R608.externalProductRuleCellIsResidualCarrier
          physicalSystem S (Symmetry.swapTriad alpha) Ms =
    refl

  externalForcingPairOnLiteralResidualCarriers :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (M : R112.ThreeLegResidualMembership system alpha) →
    (Ms :
      R112.ThreeLegResidualMembership system (Symmetry.swapTriad alpha)) →
    Split.externalForcingPair alpha beta
    ≡ Split.C.T.Swap.pairResolvent alpha beta
        * residualWitnessPairingSum alpha beta M Ms
  externalForcingPairOnLiteralResidualCarriers alpha beta M Ms =
    trans
      (externalForcingPairIsFourResidualPairings alpha beta)
      (cong
        (Split.C.T.Swap.pairResolvent alpha beta *_)
        (fourResidualPairingsUseLiteralR112Carriers alpha beta M Ms))

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round609ExternalPairExpandedToFourSelectedResidualPairings : Bool
round609ExternalPairExpandedToFourSelectedResidualPairings = true

round609R606ExternalPairOnLiteralR112ResidualCarriers : Bool
round609R606ExternalPairOnLiteralR112ResidualCarriers = true

round609RequiresExistingResidualWitnessForAlphaAndSwap : Bool
round609RequiresExistingResidualWitnessForAlphaAndSwap = true

round609IdentifiesThesePairingsWithR115WaleffeCells : Bool
round609IdentifiesThesePairingsWithR115WaleffeCells = false

round609ExternalNetworkPaymentClosed : Bool
round609ExternalNetworkPaymentClosed = false

round609IntroducesEstimate : Bool
round609IntroducesEstimate = false

round609ExternalPairExpandedToFourSelectedResidualPairingsIsTrue :
  round609ExternalPairExpandedToFourSelectedResidualPairings ≡ true
round609ExternalPairExpandedToFourSelectedResidualPairingsIsTrue = refl

round609R606ExternalPairOnLiteralR112ResidualCarriersIsTrue :
  round609R606ExternalPairOnLiteralR112ResidualCarriers ≡ true
round609R606ExternalPairOnLiteralR112ResidualCarriersIsTrue = refl

round609RequiresExistingResidualWitnessForAlphaAndSwapIsTrue :
  round609RequiresExistingResidualWitnessForAlphaAndSwap ≡ true
round609RequiresExistingResidualWitnessForAlphaAndSwapIsTrue = refl

round609IdentifiesThesePairingsWithR115WaleffeCellsIsFalse :
  round609IdentifiesThesePairingsWithR115WaleffeCells ≡ false
round609IdentifiesThesePairingsWithR115WaleffeCellsIsFalse = refl

round609ExternalNetworkPaymentClosedIsFalse :
  round609ExternalNetworkPaymentClosed ≡ false
round609ExternalNetworkPaymentClosedIsFalse = refl

round609IntroducesEstimateIsFalse :
  round609IntroducesEstimate ≡ false
round609IntroducesEstimateIsFalse = refl
