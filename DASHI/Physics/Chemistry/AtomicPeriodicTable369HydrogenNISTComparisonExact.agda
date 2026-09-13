module DASHI.Physics.Chemistry.AtomicPeriodicTable369HydrogenNISTComparisonExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369RadialIdentityRepairExecutionExact as R

------------------------------------------------------------------------
-- First authoritative reference-data comparison downstream of the repaired
-- radial-state identity producer.
--
-- The same committed hydrogenic 1s numerical state is converted to eV using
-- the 2022 CODATA Hartree conversion and compared with NIST ASD H I.  We also
-- retain the analytic infinite-nuclear-mass Coulomb value, because the finite
-- grid happens to move the numerical answer toward NIST: that accidental
-- cancellation must not be promoted as improved physical accuracy.
------------------------------------------------------------------------

record HydrogenReferenceComparisonReceipt : Set where
  constructor hydrogenReferenceComparisonReceipt
  field
    producerPath : String
    receiptPath : String
    producerSHA256 : String
    inputRadialProducerSHA256 : String
    model : String
    hartreeToEV2022CODATA : String
    nistASDDOI : String
    nistSpectrum : String
    nistGroundShell : String
    nistIonizationEnergyEV : String
    nistUncertaintyEV : String
    numericIonizationEnergyEV : String
    numericMinusNISTEV : String
    numericRelativeResidual : String
    analyticInfiniteMassIonizationEnergyEV : String
    analyticInfiniteMassMinusNISTEV : String
    comparisonExecuted : Bool

canonicalHydrogenReferenceComparisonReceipt : HydrogenReferenceComparisonReceipt
canonicalHydrogenReferenceComparisonReceipt =
  hydrogenReferenceComparisonReceipt
    "scripts/atomic_hydrogen_nist_comparison.py"
    "Artifacts/atomic-periodic-table-369/hydrogen-nist-comparison-receipt.json"
    "43d6ca4c6a3ac5a66db75819d9e5d2b6d47423ce6987eeba0fd717f1b8de4961"
    "d4df9c2ef1e2292cdf216d7bf5da4aab78189b47cff02dc83bb28d308d240b9e"
    "nonrelativistic infinite-nuclear-mass Coulomb hydrogenic Z=1"
    "27.211386245981 eV/E_h"
    "10.18434/T4W30F"
    "H I"
    "1s"
    "13.598434599702"
    "0.000000000012"
    "13.604333505485517"
    "+0.005898905783517705"
    "0.000433793003177511"
    "13.6056931229905"
    "+0.00725852328850074"
    true

------------------------------------------------------------------------
-- Attribution / snowball surface.
------------------------------------------------------------------------

record HydrogenReferenceAttribution : Set where
  constructor hydrogenReferenceAttribution
  field
    objectName : String
    doi : String
    qid : String
    primaryStatus : String
    dewey : String
    goldBook : String
    oeis : String
    directLink : String
    relationship : String

nistASDAttribution : HydrogenReferenceAttribution
nistASDAttribution =
  hydrogenReferenceAttribution
    "NIST Atomic Spectra Database, Standard Reference Database 78"
    "10.18434/T4W30F"
    "ionization energy Q483769; atom Q9121"
    "authoritative reference-data source"
    "539.7 atomic-physics topic coordinate"
    "ionization energy I03199"
    "not an OEIS object"
    "https://www.nist.gov/pml/atomic-spectra-database"
    "authoritative external consumer for measured/evaluated H I ionization data; does not prove the DASHI producer"

codataAttribution : HydrogenReferenceAttribution
codataAttribution =
  hydrogenReferenceAttribution
    "2022 CODATA Hartree energy in electron volts"
    "NIST/CODATA constant-table source; individual constant DOI not assigned here"
    "quantum mechanics Q944"
    "authoritative constants reference"
    "530.12 quantum-mechanics topic coordinate"
    "unassigned"
    "not an OEIS object"
    "https://physics.nist.gov/cgi-bin/cuu/Value?hrev"
    "conversion coordinate used to map the committed Hartree-valued producer result into eV"

structuralSequenceBoundaryAttribution : HydrogenReferenceAttribution
structuralSequenceBoundaryAttribution =
  hydrogenReferenceAttribution
    "upstream structural periodic-table sequence atlas"
    "Restrepo/Pachon DOI 10.1007/s10698-006-9026-6"
    "periodic table Q10693; Aufbau principle Q585745"
    "mathematical-chemistry context"
    "546.8 periodic-table coordinate"
    "Aufbau principle AT06996"
    "A167268 / A093907 / A018227"
    "https://oeis.org/A167268"
    "the OEIS/Madelung structural lane is upstream of this numerical comparison; sequence identity does not predict this ionization residual"

------------------------------------------------------------------------
-- The key epistemic correction.
------------------------------------------------------------------------

record HydrogenComparisonBoundary : Set where
  constructor hydrogenComparisonBoundary
  field
    oneElectronReferenceDiagnosticPaid : Bool
    numericResidualCloserThanAnalyticImpliesBetterPhysics : Bool
    numericalDiscretizationErrorSeparatedFromModelError : Bool
    finiteProtonMassPaid : Bool
    relativisticQEDPaid : Bool
    manyElectronSCFPaid : Bool
    periodicTableEmpiricalRecoveryPaid : Bool

canonicalHydrogenComparisonBoundary : HydrogenComparisonBoundary
canonicalHydrogenComparisonBoundary =
  hydrogenComparisonBoundary true false false false false false false

record HydrogenComparisonFrontier : Set where
  constructor hydrogenComparisonFrontier
  field
    paid : String
    diagnostic : String
    firstOneElectronPhysicalCorrection : String
    firstManyElectronProducer : String
    downstreamAuthority : String
    paymentRule : String

canonicalHydrogenComparisonFrontier : HydrogenComparisonFrontier
canonicalHydrogenComparisonFrontier =
  hydrogenComparisonFrontier
    "the repaired same-object H 1s numerical energy has been converted with the pinned CODATA factor and compared to the pinned NIST ASD H I ionization datum"
    "the finite-grid numerical IE is about 0.005899 eV above NIST while the analytic infinite-mass Coulomb IE is about 0.007259 eV above NIST; the smaller numerical residual is partly accidental cancellation and is not a physical promotion"
    "pay finite proton mass / reduced-mass hydrogen first; only then add relativistic and QED corrections if precision hydrogen is the target"
    "for the periodic-table lane, build a state-tracking self-consistent many-electron Hartree/HF producer, then compare neutral/cation total-energy differences against NIST ASD"
    "NIST ASD SRD 78 DOI 10.18434/T4W30F; ionization energy Q483769 / Gold Book I03199"
    "DOI/QID/Dewey/GoldBook/OEIS identify source objects and routes; only same-object model corrections plus executed external comparison pay quantitative physics"

-- Keep the radial repair as explicit upstream dependency.
radialRepairOwner : Set
radialRepairOwner = R.RadialIdentityRepairBoundary
