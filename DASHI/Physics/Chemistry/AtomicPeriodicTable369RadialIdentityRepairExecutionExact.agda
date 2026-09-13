module DASHI.Physics.Chemistry.AtomicPeriodicTable369RadialIdentityRepairExecutionExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369ArchiveHartreeRadialIdentityDefectExact as D

------------------------------------------------------------------------
-- Execution receipt for the first typed repair of the archive Hartree defect.
--
-- The historical archive solver erased n and always selected the lowest
-- eigenpair for l.  The repaired producer
--
--   scripts/atomic_radial_identity_repair.py
--
-- uses radialStateIndex(n,l)=n-l-1 in the hydrogenic V_H=0 limit, solves all
-- required eigenpairs in one l-sector diagonalization, and checks:
--
--   * 1s / 2s / 3s are distinct radial eigenstates,
--   * radial node count is n-l-1,
--   * hydrogenic energies agree with -1/(2 n^2) within 5e-4 Hartree,
--   * the selected eigenvectors are mutually orthogonal within each l sector.
--
-- This is a same-object executable receipt for radial identity only.  It does
-- not pay SCF convergence or quantitative many-electron atomic chemistry.
------------------------------------------------------------------------

record RadialIdentityExecutionReceipt : Set where
  constructor radialIdentityExecutionReceipt
  field
    producerPath : String
    receiptPath : String
    producerSHA256 : String
    executionDate : String
    executionEnvironment : String
    rmaxBohr : String
    gridPoints : Nat
    energyToleranceHartree : String
    sameLPrincipalIdentityDistinguished : Bool
    hydrogenicEnergyChecksPassed : Bool
    radialNodeChecksPassed : Bool
    orthogonalityChecksPassed : Bool
    overallPassed : Bool

canonicalRadialIdentityExecutionReceipt : RadialIdentityExecutionReceipt
canonicalRadialIdentityExecutionReceipt =
  radialIdentityExecutionReceipt
    "scripts/atomic_radial_identity_repair.py"
    "Artifacts/atomic-periodic-table-369/radial-identity-repair-receipt.json"
    "d4df9c2ef1e2292cdf216d7bf5da4aab78189b47cff02dc83bb28d308d240b9e"
    "2026-09-11"
    "Python 3.13.5; NumPy 2.3.5; SciPy 1.17.0"
    "80.0"
    4000
    "5e-4"
    true true true true true

------------------------------------------------------------------------
-- Retained numerical values.  Floating-point numbers are provenance strings,
-- not reified exact reals in Agda.  Their authority comes from the committed
-- producer+receipt pair, not from source-code presence alone.
------------------------------------------------------------------------

record RadialStateNumericReceipt : Set where
  constructor radialStateNumericReceipt
  field
    stateLabel : String
    radialIndex : Nat
    observedNodes : Nat
    computedEnergyHartree : String
    analyticEnergyHartree : String
    absoluteErrorHartree : String
    passed : Bool

oneSReceipt : RadialStateNumericReceipt
oneSReceipt = radialStateNumericReceipt
  "1s" 0 0 "-0.4999500349782737" "-0.5" "4.9965021726272596e-05" true

twoSReceipt : RadialStateNumericReceipt
twoSReceipt = radialStateNumericReceipt
  "2s" 1 1 "-0.12499687671803333" "-0.125" "3.1232819666660028e-06" true

threeSReceipt : RadialStateNumericReceipt
threeSReceipt = radialStateNumericReceipt
  "3s" 2 2 "-0.05555493859367163" "-0.05555555555555555" "6.169618839216295e-07" true

twoPReceipt : RadialStateNumericReceipt
twoPReceipt = radialStateNumericReceipt
  "2p" 0 0 "-0.12500104120998212" "-0.125" "1.0412099821222043e-06" true

threePReceipt : RadialStateNumericReceipt
threePReceipt = radialStateNumericReceipt
  "3p" 1 1 "-0.055556035451670566" "-0.05555555555555555" "4.798961150132008e-07" true

threeDReceipt : RadialStateNumericReceipt
threeDReceipt = radialStateNumericReceipt
  "3d" 0 0 "-0.055555596687603834" "-0.05555555555555555" "4.113204828126715e-08" true

------------------------------------------------------------------------
-- Same-object defect/repair relationship.
------------------------------------------------------------------------

record DefectRepairWeld : Set where
  constructor defectRepairWeld
  field
    archiveDefectLocated : Bool
    repairedProducerLocated : Bool
    sameDefectAddressed : Bool
    radialIdentityExecutionPaid : Bool
    scfStateTrackingPaid : Bool
    manyElectronSpectrumPaid : Bool
    calibratedIonizationPaid : Bool

canonicalDefectRepairWeld : DefectRepairWeld
canonicalDefectRepairWeld =
  defectRepairWeld true true true true false false false

------------------------------------------------------------------------
-- Identifier-rich attribution / snowball register.
------------------------------------------------------------------------

record RadialIdentityAttribution : Set where
  constructor radialIdentityAttribution
  field
    sourceObject : String
    doi : String
    qid : String
    primaryStatus : String
    dewey : String
    oeis : String
    directLink : String
    relationship : String

schrodinger1926Receipt : RadialIdentityAttribution
schrodinger1926Receipt =
  radialIdentityAttribution
    "Erwin Schrodinger, Quantisierung als Eigenwertproblem (1926)"
    "10.1002/andp.19263840404"
    "atom Q9121; quantum mechanics Q944"
    "external primary quantum-mechanics source"
    "539.7 atom / 530.12 quantum-mechanics topic coordinates"
    "not an OEIS object"
    "https://doi.org/10.1002/andp.19263840404"
    "primary historical eigenvalue-problem provenance for the hydrogenic spectral regression; not a receipt for the DASHI numerical implementation"

nistASDReceipt : RadialIdentityAttribution
nistASDReceipt =
  radialIdentityAttribution
    "NIST Atomic Spectra Database, Standard Reference Database 78, version 5.12"
    "10.18434/T4W30F"
    "ionization energy Q483769; atom Q9121"
    "authoritative reference-data source; current database"
    "539.7 atomic-physics topic coordinate"
    "not an OEIS object; A167268/A093907 remain structural selector coordinates only"
    "https://www.nist.gov/pml/atomic-spectra-database"
    "authoritative downstream comparison target for levels, ground states, and ionization energies; not yet consumed by this hydrogenic radial-identity receipt"

structuralOEISReceipt : RadialIdentityAttribution
structuralOEISReceipt =
  radialIdentityAttribution
    "DASHI exact Madelung selector / period partition"
    "Restrepo/Pachon DOI 10.1007/s10698-006-9026-6"
    "periodic table Q10693; Aufbau principle Q585745"
    "structural mathematical-chemistry context"
    "546.8 periodic-table coordinate"
    "A167268 -> A093907 -> A018227"
    "https://oeis.org/A167268 ; https://oeis.org/A093907 ; https://oeis.org/A018227"
    "upstream structural order/capacity provenance only; these sequence identities do not validate the radial eigenproblem or quantitative atomic energies"

------------------------------------------------------------------------
-- Non-promotion boundary and new highest-alpha frontier.
------------------------------------------------------------------------

record RadialIdentityRepairBoundary : Set where
  constructor radialIdentityRepairBoundary
  field
    hydrogenicRegressionImpliesSCFConvergence : Bool
    orthogonalityImpliesCorrectManyElectronHartree : Bool
    radialIdentityImpliesMeasuredSpectrum : Bool
    nistDatabasePresenceImpliesAgreement : Bool
    exactProducerHashImportsEmpiricalAuthority : Bool
    sameObjectSCFProducerStillNeeded : Bool

canonicalRadialIdentityRepairBoundary : RadialIdentityRepairBoundary
canonicalRadialIdentityRepairBoundary =
  radialIdentityRepairBoundary false false false false false true

record RadialIdentityRepairFrontier : Set where
  constructor radialIdentityRepairFrontier
  field
    newlyPaid : String
    nextSameObjectImplementation : String
    nextExecution : String
    nextExternalComparison : String
    attributionRule : String

canonicalRadialIdentityRepairFrontier : RadialIdentityRepairFrontier
canonicalRadialIdentityRepairFrontier =
  radialIdentityRepairFrontier
    "the n-erasure defect is repaired in an executable hydrogenic producer: n-l-1 selects distinct radial eigenstates; energies, nodes, and within-l orthogonality pass in the committed receipt"
    "lift the repaired l-sector eigenstate family into the self-consistent many-electron producer while preserving (n,l) state identity across SCF iterations and excluding self-interaction / specifying exchange treatment"
    "commit a same-object SCF receipt with convergence history, producer SHA-256, input occupations, total energies E(Z), and explicit neutral/cation pairing for IE1(Z)"
    "compare the resulting ground states / levels / ionization energies to NIST ASD SRD 78 DOI 10.18434/T4W30F with uncertainty-aware residuals"
    "archive, executable receipt, DOI, QID, Dewey, OEIS and reference-data coordinates remain separate; only same-object execution plus external comparison pays quantitative physics"

-- Keep the historical defect owner as an explicit predecessor rather than
-- rewriting its evidence state.
archiveDefectOwner : Set
archiveDefectOwner = D.ArchiveHartreeDefectBoundary
