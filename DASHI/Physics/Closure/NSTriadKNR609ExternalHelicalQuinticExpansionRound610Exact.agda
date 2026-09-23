{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR609ExternalHelicalQuinticExpansionRound610Exact where

------------------------------------------------------------------------
-- ROUND610 / R609 RESIDUAL PAIRINGS -> EIGHT LITERAL HELICAL QUINTIC CELLS
--
-- R609 reduces one external R567 Cauchy pair to four real-Hermitian pairings
--
--   Re < E_alpha , A_beta >
--   Re < E_alpha , A_swap(beta) >
--   Re < E_swap(alpha) , A_beta >
--   Re < E_swap(alpha) , A_swap(beta) >.
--
-- R608 defines each residual product-rule vector E_tau as exactly two helical
-- slot insertions:
--
--   P^+(Residual_p) x P^-(u_q)
--     +
--   P^+(u_p) x P^-(Residual_q).
--
-- Real-Hermitian additivity therefore expands every R609 pairing into two
-- literal quintic cells, hence the four-pair sum into eight cells.  This is
-- exact representation only: no absolute value, Waleffe identification, or
-- analytic estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeResidualCarrierRound112Exact as R112
import DASHI.Physics.Closure.NSTriadKNR230ExternalResidualCarrierRound608Exact as R608
import DASHI.Physics.Closure.NSTriadKNR567ExternalResidualPairExpansionRound609Exact as R609

F : C3.RealField _
F = Rational.rationalRealField

four : ℚ
four = 4

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Prev = R609.FixedOutput physicalSystem S output

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem
  velocity = Audit.velocityAt system

  pResidualInsertion :
    (tau : Physical.PhysicalTriadIncidence) →
    R112.ThreeLegResidualMembership system tau →
    C3.Complex3 F
  pResidualInsertion tau M =
    Cross.complex3Cross
      (Helical.helicalProjectorPlus E I S
        (Physical.p tau)
        (R112.externalResidualP system tau M))
      (Helical.helicalProjectorMinus E I S
        (Physical.q tau)
        (velocity (Physical.q tau)))

  qResidualInsertion :
    (tau : Physical.PhysicalTriadIncidence) →
    R112.ThreeLegResidualMembership system tau →
    C3.Complex3 F
  qResidualInsertion tau M =
    Cross.complex3Cross
      (Helical.helicalProjectorPlus E I S
        (Physical.p tau)
        (velocity (Physical.p tau)))
      (Helical.helicalProjectorMinus E I S
        (Physical.q tau)
        (R112.externalResidualQ system tau M))

  selectedMixedCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  selectedMixedCell = R224.mixedPlusMinus S velocity

  pQuinticCell :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    R112.ThreeLegResidualMembership system alpha →
    ℚ
  pQuinticCell alpha beta M =
    R179.realHermitianCross
      (pResidualInsertion alpha M)
      (selectedMixedCell beta)

  qQuinticCell :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    R112.ThreeLegResidualMembership system alpha →
    ℚ
  qQuinticCell alpha beta M =
    R179.realHermitianCross
      (qResidualInsertion alpha M)
      (selectedMixedCell beta)

  residualExternalCellIsTwoHelicalInsertions :
    (tau : Physical.PhysicalTriadIncidence) →
    (M : R112.ThreeLegResidualMembership system tau) →
    Prev.residualExternalCell tau M
    ≡ C3.complex3Add
        (pResidualInsertion tau M)
        (qResidualInsertion tau M)
  residualExternalCellIsTwoHelicalInsertions tau M = refl

  residualPairingIsTwoQuinticCells :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (M : R112.ThreeLegResidualMembership system alpha) →
    R179.realHermitianCross
      (Prev.residualExternalCell alpha M)
      (selectedMixedCell beta)
    ≡ pQuinticCell alpha beta M + qQuinticCell alpha beta M
  residualPairingIsTwoQuinticCells alpha beta M =
    trans
      (cong₂ R179.realHermitianCross
        (residualExternalCellIsTwoHelicalInsertions alpha M)
        refl)
      (R291.realCrossAddLeft
        (pResidualInsertion alpha M)
        (qResidualInsertion alpha M)
        (selectedMixedCell beta))

  eightQuinticCellSum :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    R112.ThreeLegResidualMembership system alpha →
    R112.ThreeLegResidualMembership system (Symmetry.swapTriad alpha) →
    ℚ
  eightQuinticCellSum alpha beta M Ms =
    four *
      ( pQuinticCell alpha beta M
      + qQuinticCell alpha beta M
      + pQuinticCell alpha (Symmetry.swapTriad beta) M
      + qQuinticCell alpha (Symmetry.swapTriad beta) M
      + pQuinticCell (Symmetry.swapTriad alpha) beta Ms
      + qQuinticCell (Symmetry.swapTriad alpha) beta Ms
      + pQuinticCell
          (Symmetry.swapTriad alpha) (Symmetry.swapTriad beta) Ms
      + qQuinticCell
          (Symmetry.swapTriad alpha) (Symmetry.swapTriad beta) Ms
      )

  residualWitnessPairingSumIsEightQuinticCells :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (M : R112.ThreeLegResidualMembership system alpha) →
    (Ms : R112.ThreeLegResidualMembership system (Symmetry.swapTriad alpha)) →
    Prev.residualWitnessPairingSum alpha beta M Ms
    ≡ eightQuinticCellSum alpha beta M Ms
  residualWitnessPairingSumIsEightQuinticCells alpha beta M Ms
    rewrite residualPairingIsTwoQuinticCells alpha beta M
          | residualPairingIsTwoQuinticCells
              alpha (Symmetry.swapTriad beta) M
          | residualPairingIsTwoQuinticCells
              (Symmetry.swapTriad alpha) beta Ms
          | residualPairingIsTwoQuinticCells
              (Symmetry.swapTriad alpha) (Symmetry.swapTriad beta) Ms =
    solve
      ( pQuinticCell alpha beta M
      ∷ qQuinticCell alpha beta M
      ∷ pQuinticCell alpha (Symmetry.swapTriad beta) M
      ∷ qQuinticCell alpha (Symmetry.swapTriad beta) M
      ∷ pQuinticCell (Symmetry.swapTriad alpha) beta Ms
      ∷ qQuinticCell (Symmetry.swapTriad alpha) beta Ms
      ∷ pQuinticCell
          (Symmetry.swapTriad alpha) (Symmetry.swapTriad beta) Ms
      ∷ qQuinticCell
          (Symmetry.swapTriad alpha) (Symmetry.swapTriad beta) Ms
      ∷ [])

  externalForcingPairIsEightHelicalQuinticCells :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (M : R112.ThreeLegResidualMembership system alpha) →
    (Ms : R112.ThreeLegResidualMembership system (Symmetry.swapTriad alpha)) →
    Prev.Split.externalForcingPair alpha beta
    ≡ Prev.Split.C.T.Swap.pairResolvent alpha beta
        * eightQuinticCellSum alpha beta M Ms
  externalForcingPairIsEightHelicalQuinticCells alpha beta M Ms =
    trans
      (Prev.externalForcingPairOnLiteralResidualCarriers alpha beta M Ms)
      (cong₂ _*_
        refl
        (residualWitnessPairingSumIsEightQuinticCells alpha beta M Ms))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round610ResidualPairingExpandedToTwoHelicalQuinticCells : Bool
round610ResidualPairingExpandedToTwoHelicalQuinticCells = true

round610ExternalPairExpandedToEightHelicalQuinticCells : Bool
round610ExternalPairExpandedToEightHelicalQuinticCells = true

round610IdentifiesHelicalQuinticCellsWithR115QuarticWaleffeCells : Bool
round610IdentifiesHelicalQuinticCellsWithR115WaleffeCells = false

round610ExternalNetworkPaymentClosed : Bool
round610ExternalNetworkPaymentClosed = false

round610IntroducesEstimate : Bool
round610IntroducesEstimate = false

round610ExternalPairExpandedToEightHelicalQuinticCellsIsTrue :
  round610ExternalPairExpandedToEightHelicalQuinticCells ≡ true
round610ExternalPairExpandedToEightHelicalQuinticCellsIsTrue = refl

round610IdentifiesHelicalQuinticCellsWithR115QuarticWaleffeCellsIsFalse :
  round610IdentifiesHelicalQuinticCellsWithR115WaleffeCells ≡ false
round610IdentifiesHelicalQuinticCellsWithR115QuarticWaleffeCellsIsFalse = refl

round610ExternalNetworkPaymentClosedIsFalse :
  round610ExternalNetworkPaymentClosed ≡ false
round610ExternalNetworkPaymentClosedIsFalse = refl

round610IntroducesEstimateIsFalse :
  round610IntroducesEstimate ≡ false
round610IntroducesEstimateIsFalse = refl
