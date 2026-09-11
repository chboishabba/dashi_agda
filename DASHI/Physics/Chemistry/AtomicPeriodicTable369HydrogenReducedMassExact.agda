module DASHI.Physics.Chemistry.AtomicPeriodicTable369HydrogenReducedMassExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369HydrogenNISTComparisonExact as H

------------------------------------------------------------------------
-- Leading finite-nuclear-mass correction on the one-electron hydrogen branch.
--
-- For a proton/electron two-body Coulomb system, the electron-mass-scaled
-- reduced mass is
--
--   mu / m_e = 1 / (1 + m_e/m_p).
--
-- Using the 2022 CODATA electron-proton mass ratio and the same Hartree-to-eV
-- conversion as the first NIST comparison moves the infinite-mass hydrogen
-- ionization energy from 13.6056931229905 eV to 13.598287264283275 eV.
-- This is much closer to NIST ASD H I 13.598434599702 eV, but the remaining
-- residual is still far larger than the NIST uncertainty and must not be
-- attributed to one omitted effect without a typed correction budget.
------------------------------------------------------------------------

record ReducedMassExecutionReceipt : Set where
  constructor reducedMassExecutionReceipt
  field
    producerPath : String
    receiptPath : String
    producerSHA256 : String
    inputComparisonProducerSHA256 : String
    electronProtonMassRatio2022CODATA : String
    reducedMassOverElectronMass : String
    reducedMassIonizationEnergyEV : String
    nistIonizationEnergyEV : String
    reducedMassMinusNISTEV : String
    relativeResidual : String
    infiniteMassMinusNISTEV : String
    residualMagnitudeImprovesOverInfiniteMass : Bool
    executionPaid : Bool

canonicalReducedMassExecutionReceipt : ReducedMassExecutionReceipt
canonicalReducedMassExecutionReceipt =
  reducedMassExecutionReceipt
    "scripts/atomic_hydrogen_reduced_mass_nist.py"
    "Artifacts/atomic-periodic-table-369/hydrogen-reduced-mass-nist-receipt.json"
    "25b2ac8fd8925b64903535a90b238e4bb4f53a95144695972c9edac99df8121f"
    "43d6ca4c6a3ac5a66db75819d9e5d2b6d47423ce6987eeba0fd717f1b8de4961"
    "5.446170214889e-4"
    "0.9994556794247615"
    "13.598287264283275"
    "13.598434599702"
    "-0.0001473354187240261"
    "-1.0834733780846721e-05"
    "+0.00725852328850074"
    true
    true

------------------------------------------------------------------------
-- Identifier-rich source receipt.
------------------------------------------------------------------------

record ReducedMassAttribution : Set where
  constructor reducedMassAttribution
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

codataMassRatioAttribution : ReducedMassAttribution
codataMassRatioAttribution =
  reducedMassAttribution
    "2022 CODATA electron-proton mass ratio m_e/m_p"
    "CODATA 2022 recommended constants; table object"
    "quantum mechanics Q944"
    "authoritative constants source"
    "530.12 quantum-mechanics topic coordinate"
    "unassigned"
    "not an OEIS object"
    "https://physics.nist.gov/cuu/Constants/"
    "supplies the finite-proton-mass parameter; it does not identify the remaining hydrogen residual"

nistHydrogenAttribution : ReducedMassAttribution
nistHydrogenAttribution =
  reducedMassAttribution
    "NIST ASD H I ground state and ionization energy"
    "10.18434/T4W30F"
    "ionization energy Q483769; atom Q9121"
    "authoritative reference-data source"
    "539.7 atomic-physics topic coordinate"
    "I03199"
    "not an OEIS object"
    "https://physics.nist.gov/asd"
    "downstream external comparison target retained from the first reference-data tranche"

------------------------------------------------------------------------
-- Correction budget.  We pay reduced mass and leave the rest explicit.
------------------------------------------------------------------------

record HydrogenCorrectionBudget : Set where
  constructor hydrogenCorrectionBudget
  field
    infiniteNuclearMassBaselinePaid : Bool
    finiteProtonReducedMassPaid : Bool
    relativisticCorrectionPaid : Bool
    radiativeQEDPaid : Bool
    higherOrderRecoilPaid : Bool
    protonFiniteSizePaid : Bool
    hyperfinePaid : Bool
    nistAgreementWithinQuotedUncertaintyPaid : Bool
    manyElectronGeneralityPaid : Bool

canonicalHydrogenCorrectionBudget : HydrogenCorrectionBudget
canonicalHydrogenCorrectionBudget =
  hydrogenCorrectionBudget true true false false false false false false false

record ReducedMassBoundary : Set where
  constructor reducedMassBoundary
  field
    residualReductionImpliesFullHydrogenTheory : Bool
    remainingResidualMayBeAssignedToQEDWithoutCalculation : Bool
    nistPrecisionAgreementPaid : Bool
    reducedMassPromotesPeriodicTableEmpiricalRecovery : Bool
    nextCorrectionBudgetRequired : Bool

canonicalReducedMassBoundary : ReducedMassBoundary
canonicalReducedMassBoundary =
  reducedMassBoundary false false false false true

record ReducedMassFrontier : Set where
  constructor reducedMassFrontier
  field
    paid : String
    strongestNumericalFinding : String
    nextOneElectronLeaf : String
    nextPeriodicTableLeaf : String
    provenanceRule : String

canonicalReducedMassFrontier : ReducedMassFrontier
canonicalReducedMassFrontier =
  reducedMassFrontier
    "finite proton mass is paid at leading nonrelativistic reduced-mass order using the 2022 CODATA electron-proton mass ratio"
    "the analytic infinite-mass residual of about +0.007259 eV falls to about -0.0001473 eV after reduced mass; this is a useful correction-budget result, not precision agreement"
    "separate relativistic/Dirac, radiative QED, recoil and proton-size contributions before assigning the remaining residual"
    "move in parallel to the many-electron state-tracking SCF/HF producer for He and beyond; hydrogen precision is not the bottleneck for periodic-table recovery"
    "CODATA/NIST/DOI/QID/Dewey/GoldBook/OEIS coordinates remain source identities; quantitative promotion requires same-object correction calculations and external residuals"

upstreamHydrogenComparisonOwner : Set
upstreamHydrogenComparisonOwner = H.HydrogenComparisonBoundary
