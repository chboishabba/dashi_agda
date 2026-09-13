module DASHI.Physics.Chemistry.AtomicPeriodicTable369HeliumHartreeConvergenceExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Executed convergence diagnostic for the first corrected many-electron
-- producer.  The numerical receipt is kept separate from the external
-- reference sources and from the later empirical-recovery gate.
------------------------------------------------------------------------

record HeliumHartreeConvergenceReceipt : Set where
  constructor heliumHartreeConvergenceReceipt
  field
    executionDate : String
    executionEnvironment : String
    producerPath : String
    producerGitBlob : String
    upstreamProducerPath : String
    upstreamGitBlob : String
    grids : String
    iterationsPerGrid : String
    totalEnergySequenceHartree : String
    monotoneTowardPublishedHFLimit : Bool
    richardsonEnergyHartree : String
    publishedHFLimitHartree : String
    richardsonMinusHFLimitHartree : String
    richardsonIonizationEV : String
    nistIonizationEV : String
    richardsonMinusNISTEV : String
    hfMinusPekerisHartree : String
    hfMinusPekerisEV : String
    overallPassed : Bool

canonicalHeliumHartreeConvergenceReceipt : HeliumHartreeConvergenceReceipt
canonicalHeliumHartreeConvergenceReceipt =
  heliumHartreeConvergenceReceipt
    "2026-09-11"
    "Python 3.13.5; NumPy 2.3.5; SciPy 1.17.0"
    "scripts/atomic_helium_hartree_convergence.py"
    "b67a2913c6c985cc89d3d3ab07f43f7a1caea2c2"
    "scripts/atomic_helium_hartree_scf.py"
    "289eae455beb8f42674f808f5f5209afcc9ec65b"
    "4000,8000,16000,32000,64000"
    "64,64,64,64,64"
    "-2.851230574616222,-2.8565263848367546,-2.8591210611461726,-2.8604050079530117,-2.861043623041157"
    true
    "-2.861682238129302"
    "-2.861679995612"
    "-2.2425173020756972e-06"
    "23.447568203037818"
    "24.587389011"
    "-1.139820807962181"
    "0.042044379387999875"
    "1.1440858469994268"
    true

------------------------------------------------------------------------
-- Snowball attribution: DOI/QID/Dewey/OEIS/direct-link coordinates are
-- retained by role.  Literature benchmarks calibrate the approximation class;
-- they do not import DASHI correctness.
------------------------------------------------------------------------

record HeliumHartreeAttribution : Set where
  constructor heliumHartreeAttribution
  field
    heliumQid : String
    heliumDewey : String
    periodicTableQid : String
    atomQid : String
    hartreeFockQid : String
    ionizationEnergyQid : String
    nistDoi : String
    hartreePrimaryDoi : String
    hfLimitDoi : String
    pekerisDoi : String
    oeisIonizationSequence : String
    directLinks : String
    sourceRoles : String

canonicalHeliumHartreeAttribution : HeliumHartreeAttribution
canonicalHeliumHartreeAttribution =
  heliumHartreeAttribution
    "Q560"
    "553.971 (current Wikidata catalogue coordinate; not a physics theorem)"
    "Q10693"
    "Q9121"
    "Q7879841"
    "Q483769"
    "10.18434/T4W30F"
    "10.1017/S0305004100011920"
    "10.1016/0009-2614(92)85634-M"
    "10.1103/PhysRev.115.1216"
    "A320506 first-ionization-energy sequence; A320507 atomic numbers sorted by first ionization energy"
    "https://physics.nist.gov/asd ; https://doi.org/10.1017/S0305004100011920 ; https://doi.org/10.1016/0009-2614(92)85634-M ; https://doi.org/10.1103/PhysRev.115.1216 ; https://oeis.org/A320506"
    "NIST = authoritative reference data; Hartree 1928 = primary SCF method source; Mohallem 1992 = published HF-limit benchmark; Pekeris 1959 = accurate nonrelativistic correlated benchmark; OEIS = integer-sequence/navigation coordinate"

------------------------------------------------------------------------
-- What this diagnostic actually pays.
------------------------------------------------------------------------

record HeliumHartreeConvergenceBoundary : Set where
  constructor heliumHartreeConvergenceBoundary
  field
    executedGridConvergencePaid : Bool
    convergenceTowardPublishedHFLimitPaid : Bool
    numericalVsModelResidualSeparated : Bool
    electronCorrelationPaid : Bool
    genericMultiOrbitalStateTrackingPaid : Bool
    calibratedPeriodicTableIonizationPaid : Bool
    nuclearStabilityPaid : Bool
    oeisIdentityImpliesMechanism : Bool
    qidOrDeweyImpliesScientificTruth : Bool

canonicalHeliumHartreeConvergenceBoundary : HeliumHartreeConvergenceBoundary
canonicalHeliumHartreeConvergenceBoundary =
  heliumHartreeConvergenceBoundary
    true true true false false false false false false

record HeliumHartreeConvergenceFrontier : Set where
  constructor heliumHartreeConvergenceFrontier
  field
    strongestPaid : String
    survivingPhysicalDefect : String
    nextProducer : String
    nextComparison : String
    paymentRule : String

canonicalHeliumHartreeConvergenceFrontier : HeliumHartreeConvergenceFrontier
canonicalHeliumHartreeConvergenceFrontier =
  heliumHartreeConvergenceFrontier
    "same-object closed-shell He Hartree numerics converge toward the published HF/SCF limit; first-order Richardson extrapolation is within about 2.24e-6 Hartree"
    "the approximately 0.042044 Hartree / 1.144 eV HF-to-Pekeris gap is unpaid electron correlation/model physics rather than the prior radial-identity defect"
    "promote the corrected state-identity machinery from one occupied 1s spatial orbital to multiple occupied (n,l) sectors with orthogonality/state tracking through SCF or HF iterations"
    "for each promoted atom, compute matched neutral/cation total energies and compare IE1 against NIST ASD SRD 78 with source and uncertainty retained"
    "Snowball acquisition may proceed through DOI/QID/Dewey/OEIS/link neighbours, but only same-object executed/typed dependencies pay promotion"
