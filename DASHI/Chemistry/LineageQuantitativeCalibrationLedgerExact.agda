module DASHI.Chemistry.LineageQuantitativeCalibrationLedgerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.LineageCalibrationAttributionEnvelopeExact as Attribution

------------------------------------------------------------------------
-- QUANTITATIVE CALIBRATION LEDGER
--
-- A numeric coordinate is not paid by citation, source identity, a nearby
-- table, or a qualitative mechanism statement. Exact locator, units, method,
-- biological/chemical context and uncertainty/provenance are independent.
------------------------------------------------------------------------

data NumericPaymentState : Set where
  unpaidNumeric : NumericPaymentState
  boundedNumeric : NumericPaymentState
  sourcePaidNumeric : NumericPaymentState

data ContextMatchState : Set where
  contextUnresolved : ContextMatchState
  partialContextMatch : ContextMatchState
  sameDeclaredContext : ContextMatchState

data LocatorPaymentState : Set where
  noExactLocator : LocatorPaymentState
  articleOrSectionOnly : LocatorPaymentState
  exactTableFigureDatasetLocator : LocatorPaymentState

record QuantitativeCalibrationCell : Set₁ where
  constructor quantitativeCalibrationCell
  field
    coordinateKey : String
    sourceEnvelopeReference : String
    quantityRole : String
    valueReference : String
    unitsReference : String
    uncertaintyReference : String
    methodReference : String
    sampleSpeciesIsoformReference : String
    environmentCompartmentReference : String
    locatorReference : String
    locatorState : LocatorPaymentState
    contextState : ContextMatchState
    paymentState : NumericPaymentState
    unpaidResidual : String
    missingValueIsZero : Bool
    missingValueIsZeroIsFalse : missingValueIsZero ≡ false

open QuantitativeCalibrationCell public

bh4BranchFluxCell : QuantitativeCalibrationCell
bh4BranchFluxCell =
  quantitativeCalibrationCell
    "BH4 J_PAH/J_TH/J_TPH/J_NOS/J_AGMO"
    "KitzerowBH4 reaction/source atlas + future same-system flux dataset"
    "branch-specific fluxes under declared perturbation"
    "unpaid"
    "concentration/time or isotope-flux units to be source-defined"
    "unpaid"
    "requires calibrated same-system metabolite/isotope/enzymatic assay"
    "cell type / genotype / isoform unresolved"
    "compartment, oxygen, substrate and redox state unresolved"
    "no same-object quantitative locator acquired"
    noExactLocator
    contextUnresolved
    unpaidNumeric
    "all branch flux values and uncertainties"
    false refl

pahKineticCell : QuantitativeCalibrationCell
pahKineticCell =
  quantitativeCalibrationCell
    "PAH Km/Vmax/kcat calibration"
    "pahEnvelope / primary kinetic source required"
    "kinetic parameter set"
    "unpaid"
    "source-defined"
    "unpaid"
    "primary kinetic assay required"
    "species/isoform unresolved"
    "pH, temperature, substrate/BH4/O2 context unresolved"
    "mechanism review is not an exact numeric locator"
    articleOrSectionOnly
    contextUnresolved
    unpaidNumeric
    "exact parameter values, units, uncertainty and assay context"
    false refl

chlorElectrodeCell : QuantitativeCalibrationCell
chlorElectrodeCell =
  quantitativeCalibrationCell
    "chlor-alkali electrode potential/current-density calibration"
    "chlorEnvelope / primary electrochemical or audited technical dataset"
    "potential, current density and kinetic/material coordinates"
    "unpaid"
    "V, A area^-1 and source-specific rate units"
    "unpaid"
    "polarization/kinetic measurement"
    "electrode material unresolved"
    "electrolyte composition and temperature unresolved"
    "process-level source identified; exact calibration row unresolved"
    articleOrSectionOnly
    partialContextMatch
    unpaidNumeric
    "same-cell potential/current-density/material/temperature values"
    false refl

pbCaAffinityCell : QuantitativeCalibrationCell
pbCaAffinityCell =
  quantitativeCalibrationCell
    "Pb/Ca same-target affinity/occupancy/function"
    "pbCaEnvelope + target-specific primary experiment"
    "same-object target-relative calibration"
    "unpaid as universal replay coordinate"
    "source-specific affinity/concentration/function units"
    "unpaid"
    "same-target structural/biophysical/functional assay"
    "target/site specific"
    "ion competition, pH, hydration and expression must match"
    "structural survey article does not pay one universal same-target numeric tuple"
    articleOrSectionOnly
    partialContextMatch
    unpaidNumeric
    "same-target affinity, occupancy, geometry and functional uncertainty"
    false refl

carbonSiliconYieldCell : QuantitativeCalibrationCell
carbonSiliconYieldCell =
  quantitativeCalibrationCell
    "matched carbon-vs-silicon reaction-network yields/kinetics"
    "carbonEnvelope + future matched comparative dataset"
    "reachable-chemistry comparison under frozen consumer/environment"
    "unpaid"
    "reaction-specific yield/energy/rate units"
    "unpaid"
    "matched experimental or validated computational protocol"
    "backbone families must be explicitly paired"
    "solvent/T/P/redox/water activity/catalysts must match"
    "Astrobiology Primer is overview context, not matched quantitative calibration"
    articleOrSectionOnly
    contextUnresolved
    unpaidNumeric
    "matched reaction families, negative-result coverage, yields, energetics and kinetics"
    false refl

canonicalQuantitativeCells : List QuantitativeCalibrationCell
canonicalQuantitativeCells =
  bh4BranchFluxCell
  ∷ pahKineticCell
  ∷ chlorElectrodeCell
  ∷ pbCaAffinityCell
  ∷ carbonSiliconYieldCell
  ∷ []

record QuantitativeCalibrationBoundary : Set where
  constructor quantitativeCalibrationBoundary
  field
    numberWithoutExactLocatorPromoted : Bool
    numberWithoutExactLocatorPromotedIsFalse : numberWithoutExactLocatorPromoted ≡ false
    numberWithoutContextPromoted : Bool
    numberWithoutContextPromotedIsFalse : numberWithoutContextPromoted ≡ false
    unpaidCoordinateInterpretedAsZero : Bool
    unpaidCoordinateInterpretedAsZeroIsFalse : unpaidCoordinateInterpretedAsZero ≡ false
    reviewMechanismPaysKinetics : Bool
    reviewMechanismPaysKineticsIsFalse : reviewMechanismPaysKinetics ≡ false
    databaseIdentityPaysInVivoFlux : Bool
    databaseIdentityPaysInVivoFluxIsFalse : databaseIdentityPaysInVivoFlux ≡ false
    exactUnitsAndUncertaintyRemainRequired : Bool
    exactUnitsAndUncertaintyRemainRequiredIsTrue : exactUnitsAndUncertaintyRemainRequired ≡ true
    unpaidCellRetainsSourceProvenance : Bool
    unpaidCellRetainsSourceProvenanceIsTrue : unpaidCellRetainsSourceProvenance ≡ true

open QuantitativeCalibrationBoundary public

canonicalQuantitativeCalibrationBoundary : QuantitativeCalibrationBoundary
canonicalQuantitativeCalibrationBoundary =
  quantitativeCalibrationBoundary false refl false refl false refl false refl false refl true refl true refl
