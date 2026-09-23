{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR609ExternalHelicalQuarticExpansionRound610Exact where

------------------------------------------------------------------------
-- ROUND610 / R609 RESIDUAL PAIRINGS -> EIGHT LITERAL HELICAL QUARTIC CELLS
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
-- literal quartic cells, hence the four-pair sum into eight cells.  This is
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

  pQuarticCell :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    R112.ThreeLegResidualMembership system alpha →
    ℚ
  pQuarticCell alpha beta M =
    R179.realHermitianCross
      (pResidualInsertion alpha M)
      (selectedMixedCell beta)

  qQuarticCell :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    R112.ThreeLegResidualMembership system alpha →
    ℚ
  qQuarticCell alpha beta M =
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

  residualPairingIsTwoQuarticCells :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (M : R112.ThreeLegResidualMembership system alpha) →
    R179.realHermitianCross
      (Prev.residualExternalCell alpha M)
      (selectedMixedCell beta)
    ≡ pQuarticCell alpha beta M + qQuarticCell alpha beta M
  residualPairingIsTwoQuarticCells alpha beta M =
    trans
      (cong₂ R179.realHermitianCross
        (residualExternalCellIsTwoHelicalInsertions alpha M)
        refl)
      (R291.realCrossAddLeft
        (pResidualInsertion alpha M)
        (qResidualInsertion alpha M)
        (selectedMixedCell beta))

  eightQuarticCellSum :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    R112.ThreeLegResidualMembership system alpha →
    R112.ThreeLegResidualMembership system (Symmetry.swapTriad alpha) →
    ℚ
  eightQuarticCellSum alpha beta M Ms =
    four *
      ( pQuarticCell alpha beta M
      + qQuarticCell alpha beta M
      + pQuarticCell alpha (Symmetry.swapTriad beta) M
      + qQuarticCell alpha (Symmetry.swapTriad beta) M
      + pQuarticCell (Symmetry.swapTriad alpha) beta Ms
      + qQuarticCell (Symmetry.swapTriad alpha) beta Ms
      + pQuarticCell
          (Symmetry.swapTriad alpha) (Symmetry.swapTriad beta) Ms
      + qQuarticCell
          (Symmetry.swapTriad alpha) (Symmetry.swapTriad beta) Ms
      )

  residualWitnessPairingSumIsEightQuarticCells :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (M : R112.ThreeLegResidualMembership system alpha) →
    (Ms : R112.ThreeLegResidualMembership system (Symmetry.swapTriad alpha)) →
    Prev.residualWitnessPairingSum alpha beta M Ms
    ≡ eightQuarticCellSum alpha beta M Ms
  residualWitnessPairingSumIsEightQuarticCells alpha beta M Ms
    rewrite residualPairingIsTwoQuarticCells alpha beta M
          | residualPairingIsTwoQuarticCells
              alpha (Symmetry.swapTriad beta) M
          | residualPairingIsTwoQuarticCells
              (Symmetry.swapTriad alpha) beta Ms
          | residualPairingIsTwoQuarticCells
              (Symmetry.swapTriad alpha) (Symmetry.swapTriad beta) Ms =
    solve
      ( pQuarticCell alpha beta M
      ∷ qQuarticCell alpha beta M
      ∷ pQuarticCell alpha (Symmetry.swapTriad beta) M
      ∷ qQuarticCell alpha (Symmetry.swapTriad beta) M
      ∷ pQuarticCell (Symmetry.swapTriad alpha) beta Ms
      ∷ qQuarticCell (Symmetry.swapTriad alpha) beta Ms
      ∷ pQuarticCell
          (Symmetry.swapTriad alpha) (Symmetry.swapTriad beta) Ms
      ∷ qQuarticCell
          (Symmetry.swapTriad alpha) (Symmetry.swapTriad beta) Ms
      ∷ [])

  externalForcingPairIsEightHelicalQuarticCells :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (M : R112.ThreeLegResidualMembership system alpha) →
    (Ms : R112.ThreeLegResidualMembership system (Symmetry.swapTriad alpha)) →
    Prev.Split.externalForcingPair alpha beta
    ≡ Prev.Split.C.T.Swap.pairResolvent alpha beta
        * eightQuarticCellSum alpha beta M Ms
  externalForcingPairIsEightHelicalQuarticCells alpha beta M Ms =
    trans
      (Prev.externalForcingPairOnLiteralResidualCarriers alpha beta M Ms)
      (cong₂ _*_
        refl
        (residualWitnessPairingSumIsEightQuarticCells alpha beta M Ms))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round610ResidualPairingExpandedToTwoHelicalQuarticCells : Bool
round610ResidualPairingExpandedToTwoHelicalQuarticCells = true

round610ExternalPairExpandedToEightHelicalQuarticCells : Bool
round610ExternalPairExpandedToEightHelicalQuarticCells = true

round610IdentifiesHelicalQuarticCellsWithR115WaleffeCells : Bool
round610IdentifiesHelicalQuarticCellsWithR115WaleffeCells = false

round610ExternalNetworkPaymentClosed : Bool
round610ExternalNetworkPaymentClosed = false

round610IntroducesEstimate : Bool
round610IntroducesEstimate = false

round610ExternalPairExpandedToEightHelicalQuarticCellsIsTrue :
  round610ExternalPairExpandedToEightHelicalQuarticCells ≡ true
round610ExternalPairExpandedToEightHelicalQuarticCellsIsTrue = refl

round610IdentifiesHelicalQuarticCellsWithR115WaleffeCellsIsFalse :
  round610IdentifiesHelicalQuarticCellsWithR115WaleffeCells ≡ false
round610IdentifiesHelicalQuarticCellsWithR115WaleffeCellsIsFalse = refl

round610ExternalNetworkPaymentClosedIsFalse :
  round610ExternalNetworkPaymentClosed ≡ false
round610ExternalNetworkPaymentClosedIsFalse = refl

round610IntroducesEstimateIsFalse :
  round610IntroducesEstimate ≡ false
round610IntroducesEstimateIsFalse = refl
