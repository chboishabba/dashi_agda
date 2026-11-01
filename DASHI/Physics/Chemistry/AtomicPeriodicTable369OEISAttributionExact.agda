module DASHI.Physics.Chemistry.AtomicPeriodicTable369OEISAttributionExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as G

------------------------------------------------------------------------
-- OEIS attribution / correspondence surface for the atomic formalism.
--
-- This follows the repository's existing OEIS discipline: an OEIS identifier
-- is a sequence-identity / reference coordinate.  It does not import a proof,
-- does not identify the physical mechanism that generated the sequence, and
-- does not promote a finite prefix match into empirical recovery.
------------------------------------------------------------------------

data OEISRelationship : Set where
  exactFormulaSequence : OEISRelationship
  partialSumSequence : OEISRelationship
  aufbauPeriodSequence : OEISRelationship
  closureSequence : OEISRelationship
  crossReferenceSequence : OEISRelationship

record OEISReceipt : Set where
  constructor oeisReceipt
  field
    oeisId : String
    title : String
    canonicalURL : String
    listedAuthor : String
    relation : OEISRelationship
    dashiObject : String
    exactReading : String
    primaryPhysicsAuthority : Bool
    promotesDashiMechanism : Bool
    promotesEmpiricalRecovery : Bool

open OEISReceipt public

------------------------------------------------------------------------
-- Exact sequence correspondences.
------------------------------------------------------------------------

subshellCapacityOEIS : OEISReceipt
subshellCapacityOEIS =
  oeisReceipt
    "A016825"
    "a(n) = 4*n + 2"
    "https://oeis.org/A016825"
    "N. J. A. Sloane"
    exactFormulaSequence
    "subshellCapacity l = 2*(2*l+1) = 4*l+2"
    "exact formula identity after indexing l from 0; DASHI s/p/d capacities 2,6,10 are the first three terms"
    false false false

shellCapacityOEIS : OEISReceipt
shellCapacityOEIS =
  oeisReceipt
    "A001105"
    "a(n) = 2*n^2"
    "https://oeis.org/A001105"
    "Bernd Walter"
    exactFormulaSequence
    "shellCapacity n = 2*n^2"
    "exact formula identity; OEIS also records this as the maximum number of electrons in atomic shell n"
    false false false

cumulativeShellCapacityOEIS : OEISReceipt
cumulativeShellCapacityOEIS =
  oeisReceipt
    "A006331"
    "a(n) = n*(n+1)*(2*n+1)/3"
    "https://oeis.org/A006331"
    "N. J. A. Sloane"
    partialSumSequence
    "sum_{k=1..n} 2*k^2"
    "partial sums of A001105; useful as the cumulative shell-capacity coordinate, not as the actual Aufbau period boundary by itself"
    false false false

aufbauPeriodLengthOEIS : OEISReceipt
aufbauPeriodLengthOEIS =
  oeisReceipt
    "A093907"
    "Number of elements in the n-th period of the periodic table as predicted by the Aufbau principle"
    "https://oeis.org/A093907"
    "Guillermo Restrepo"
    aufbauPeriodSequence
    "period-length target 2,8,8,18,18,32,32,..."
    "external sequence coordinate for Aufbau-predicted period lengths; it is deliberately distinct from shellCapacity n = 2*n^2"
    false false false

nobleClosureOEIS : OEISReceipt
nobleClosureOEIS =
  oeisReceipt
    "A018227"
    "Magic numbers: atoms with full shells"
    "https://oeis.org/A018227"
    "John Raithel"
    closureSequence
    "noble-element / closed-shell atomic-number coordinate 2,10,18,36,54,86,118,..."
    "OEIS records A018227 as the partial sums of A093907; the historical DASHI 2,10,18 closure regression is a three-term prefix match only"
    false false false

periodLengthCrossReferenceOEIS : OEISReceipt
periodLengthCrossReferenceOEIS =
  oeisReceipt
    "A116471"
    "Values 2*(n +/- 1)^2 sorted"
    "https://oeis.org/A116471"
    "Lekraj Beedassy"
    crossReferenceSequence
    "alternative duplicated-shell-capacity sequence whose early terms encode period lengths"
    "OEIS notes that terms a(2) through a(8) give the numbers of elements in periods 1 through 7; retained as a cross-reference, not a separate DASHI theorem"
    false false false

------------------------------------------------------------------------
-- Exact repo-native regressions against the sequence identities.
------------------------------------------------------------------------

subshellPrefixRegression :
  G.subshellCapacity 0 ≡ 2
  × G.subshellCapacity 1 ≡ 6
  × G.subshellCapacity 2 ≡ 10
subshellPrefixRegression =
  G.sCapacity , (G.pCapacity , G.dCapacity)

shellPrefixRegression :
  G.shellCapacity 1 ≡ 2
  × G.shellCapacity 2 ≡ 8
  × G.shellCapacity 3 ≡ 18
shellPrefixRegression =
  G.firstShellCapacity , (G.secondShellCapacity , G.thirdShellCapacity)

closurePrefixRegression :
  G.historicalClosureZ G.heliumLikeClosure ≡ 2
  × G.historicalClosureZ G.neonLikeClosure ≡ 10
  × G.historicalClosureZ G.argonLikeClosure ≡ 18
closurePrefixRegression =
  G.heliumLikeZ , (G.neonLikeZ , G.argonLikeZ)

------------------------------------------------------------------------
-- Source snowball from OEIS into primary literature.
--
-- A093907 links Restrepo/Pachon, "Mathematical Aspects of the Periodic Law",
-- Foundations of Chemistry 9 (2007), 189-214,
-- DOI 10.1007/s10698-006-9026-6, arXiv:math/0611410.
-- This is retained as primary/peer-reviewed mathematical-chemistry context for
-- period-length mathematics; it does not prove the DASHI 369 mechanism.
------------------------------------------------------------------------

record OEISPrimarySourceSnowball : Set where
  constructor oeisPrimarySourceSnowball
  field
    sourceSequence : String
    authors : String
    title : String
    doi : String
    arxiv : String
    directLink : String
    relationship : String
    sameObjectDashiTheory : Bool

aufbauPrimarySourceSnowball : OEISPrimarySourceSnowball
aufbauPrimarySourceSnowball =
  oeisPrimarySourceSnowball
    "A093907"
    "Guillermo Restrepo and Leonardo A. Pachon"
    "Mathematical Aspects of the Periodic Law"
    "10.1007/s10698-006-9026-6"
    "math/0611410"
    "https://doi.org/10.1007/s10698-006-9026-6"
    "primary mathematical-chemistry literature snowballed from the OEIS period-length entry; source context for mathematical periodic-law structure"
    false

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

record OEISAtomicBoundary : Set where
  constructor oeisAtomicBoundary
  field
    sequenceMatchImpliesMechanismIdentity : Bool
    oeisEntryImportsProof : Bool
    threeTermClosurePrefixProvesFullPeriodicTable : Bool
    shellCapacityEqualsAufbauPeriodLengthGlobally : Bool
    aufbauSequenceProvesNuclearStability : Bool
    oeisReferenceIsPrimaryPhysicsSource : Bool

canonicalOEISAtomicBoundary : OEISAtomicBoundary
canonicalOEISAtomicBoundary =
  oeisAtomicBoundary false false false false false false

------------------------------------------------------------------------
-- Highest-alpha use of the OEIS layer.
------------------------------------------------------------------------

record OEISAtomicFrontier : Set where
  constructor oeisAtomicFrontier
  field
    exactPaidCorrespondence : String
    strongestClosureCoordinate : String
    primaryLiteraturePaid : String
    firstUnpaidMathematicalWeld : String
    firstUnpaidPhysicalWeld : String
    paymentRule : String

canonicalOEISAtomicFrontier : OEISAtomicFrontier
canonicalOEISAtomicFrontier =
  oeisAtomicFrontier
    "A016825 <-> subshellCapacity(l)=4*l+2; A001105 <-> shellCapacity(n)=2*n^2"
    "A018227 gives the noble/full-shell closure sequence and contains the historical DASHI regression 2,10,18 as its first three terms"
    "A093907 snowballs to Restrepo/Pachon DOI 10.1007/s10698-006-9026-6 and arXiv math/0611410"
    "connect the DASHI valence-recurrence / MDL selector to the full A093907 Aufbau period-length sequence rather than only capacity identities or the 2,10,18 prefix"
    "pay the same-object operator-to-spectrum / calibrated ionization-energy bridge; OEIS sequence identity cannot discharge it"
    "OEIS may identify exact integer sequences and route source discovery; only typed same-object mathematics and physical receipts promote the DASHI claim"
