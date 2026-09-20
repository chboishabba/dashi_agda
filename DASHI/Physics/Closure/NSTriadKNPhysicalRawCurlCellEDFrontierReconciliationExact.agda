module DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlCellEDFrontierReconciliationExact where

------------------------------------------------------------------------
-- R217 -> R218/R219 -> GLOBAL FOUR-HELICITY RECONCILIATION
--
-- R217's historical frontier still lists two routine physical adapters as
-- open.  Later owners have paid both on the literal physical carrier:
--
--   R218 : p+q=k -> |k|^2 <= 2(|p|^2+|q|^2)
--   R219 : literal raw-curl cell -> R217 RawCellRadialData
--          literal modal energy/dissipation -> R109 selected-pair ED
--
-- The global four-helicity owner then composes those exact adapters and proves
-- the complete selected physical commutator CELL MASS estimate
--
--   M_N <= 36 E_N D_N
--
-- with no Fourier-cardinality factor.
--
-- This reconciliation exports the actual theorem-bearing physical statement,
-- rather than merely updating a status Boolean.  It leaves the coherent signed
-- Gram/interference term untouched: that is the genuinely nonlinear residual.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalResonantEuclideanSquareTriangleRound218Exact as R218
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlCellEDAdapterRound219Exact as R219
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalCommutatorFourHelicityEDPaymentExact as Global

F : C3.RealField _
F = Rational.rationalRealField

module ReconciledPhysicalCellMass
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws
      F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S)
    (O : Leray.RationalInverseNormOrder
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)) where

  module G = Global.GlobalCommutatorPayment physicalSystem S L O

  literalGlobalRawCurlCellMassBelowThirtySixED :
    G.globalCommutatorComponentMass
    Rational.≤
    Global.thirtySix
      Rational.*
      (R219.R109.sumEnergy G.modalED G.modes
        Rational.*
       R219.R109.sumDissipation G.modalED G.modes)
  literalGlobalRawCurlCellMassBelowThirtySixED =
    G.globalCommutatorComponentMassBelowThirtySixED

------------------------------------------------------------------------
-- Reconciled boundary.
------------------------------------------------------------------------

physicalResonanceSquareTriangleAdapterClosed : Bool
physicalResonanceSquareTriangleAdapterClosed =
  R218.round218PhysicalResonantEuclideanSquareTriangleClosed

physicalSelectedCellToEDAdapterClosed : Bool
physicalSelectedCellToEDAdapterClosed =
  R219.round219PhysicalSelectorEDAdapterClosed

physicalGlobalCellMassEDPaymentClosed : Bool
physicalGlobalCellMassEDPaymentClosed = true

physicalGlobalCellMassIntroducesCardinalityTax : Bool
physicalGlobalCellMassIntroducesCardinalityTax = false

coherentSignedGramResidualBudgetClosedHere : Bool
coherentSignedGramResidualBudgetClosedHere = false

clayPromotion : Bool
clayPromotion = false

physicalResonanceSquareTriangleAdapterClosedIsTrue :
  physicalResonanceSquareTriangleAdapterClosed ≡ true
physicalResonanceSquareTriangleAdapterClosedIsTrue =
  R218.round218PhysicalResonantEuclideanSquareTriangleClosedIsTrue

physicalSelectedCellToEDAdapterClosedIsTrue :
  physicalSelectedCellToEDAdapterClosed ≡ true
physicalSelectedCellToEDAdapterClosedIsTrue =
  R219.round219PhysicalSelectorEDAdapterClosedIsTrue

physicalGlobalCellMassEDPaymentClosedIsTrue :
  physicalGlobalCellMassEDPaymentClosed ≡ true
physicalGlobalCellMassEDPaymentClosedIsTrue = refl

physicalGlobalCellMassIntroducesCardinalityTaxIsFalse :
  physicalGlobalCellMassIntroducesCardinalityTax ≡ false
physicalGlobalCellMassIntroducesCardinalityTaxIsFalse = refl

coherentSignedGramResidualBudgetClosedHereIsFalse :
  coherentSignedGramResidualBudgetClosedHere ≡ false
coherentSignedGramResidualBudgetClosedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
