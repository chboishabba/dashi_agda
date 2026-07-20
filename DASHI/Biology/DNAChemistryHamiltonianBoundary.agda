module DASHI.Biology.DNAChemistryHamiltonianBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DNAChemistryCarrier as DNA
import DASHI.Geometry.DNAFourAdicSheetLift as Lift

------------------------------------------------------------------------
-- Chemistry Hamiltonian boundary on four-adic sheets.
--
-- Microscopic chemistry is governed by quantum dynamics, but the practical
-- storage codec does not carry the complete electronic, solvent, ionic,
-- temperature, polymerase, synthesis, and measurement microstate.  This module
-- therefore records operational Hamiltonian terms and their scope rather than
-- promoting a nearest-neighbour or mismatch kernel into exact quantum authority.

------------------------------------------------------------------------
-- Chemistry observables and interaction ranks.

data ChemistryObservable : Set where
  gcDebtObservable : ChemistryObservable
  purinePyrimidineObservable : ChemistryObservable
  homopolymerRunObservable : ChemistryObservable
  forbiddenMotifObservable : ChemistryObservable
  nearestNeighbourDeltaGObservable : ChemistryObservable
  hairpinSelfComplementarityObservable : ChemistryObservable
  dimerisationObservable : ChemistryObservable
  pcrBiasObservable : ChemistryObservable
  synthesisSequencingRiskObservable : ChemistryObservable

data HamiltonianArity : Set where
  pointHamiltonian : HamiltonianArity
  lineHamiltonian : HamiltonianArity
  sheetHamiltonian : HamiltonianArity
  voxelHamiltonian : HamiltonianArity
  supervoxelHamiltonian : HamiltonianArity
  crossRankHamiltonian : HamiltonianArity

record HamiltonianTerm : Set where
  constructor mkHamiltonianTerm
  field
    observable : ChemistryObservable
    arity : HamiltonianArity
    hardConstraint : Bool
    kernelApproximation : Bool
    exactMicroscopicHamiltonian : Bool
    chemistryReading : String

open HamiltonianTerm public

canonicalHamiltonianTerms : List HamiltonianTerm
canonicalHamiltonianTerms =
  mkHamiltonianTerm gcDebtObservable crossRankHamiltonian true false false
    "GC debt is an exact codec-state constraint on the UV carrier and a coarse-sheet balance observable, not the complete molecular Hamiltonian"
  ∷ mkHamiltonianTerm purinePyrimidineObservable crossRankHamiltonian false false false
    "R/Y balance is an exact base-coordinate observable and an optional chemistry-facing regulariser"
  ∷ mkHamiltonianTerm homopolymerRunObservable lineHamiltonian true false false
    "run length is a hard finite-state writing constraint; rmax four permits AA CC GG TT while rejecting a fifth identical base"
  ∷ mkHamiltonianTerm forbiddenMotifObservable voxelHamiltonian true false false
    "provider primer restriction enzyme and protocol motifs are hard language constraints when configured"
  ∷ mkHamiltonianTerm nearestNeighbourDeltaGObservable lineHamiltonian false true false
    "nearest-neighbour Delta G is a local empirical thermodynamic approximation over adjacent pairs and end corrections"
  ∷ mkHamiltonianTerm hairpinSelfComplementarityObservable crossRankHamiltonian true true false
    "hairpin risk couples complementarity stem mismatch loop separation distance and thermodynamic context across ranks"
  ∷ mkHamiltonianTerm dimerisationObservable supervoxelHamiltonian true true false
    "inter-strand reverse-complement alignment is a supervoxel or pool-level interaction"
  ∷ mkHamiltonianTerm pcrBiasObservable supervoxelHamiltonian false true false
    "PCR response depends on composition structure primers enzymes and environment and is not reducible to one scalar"
  ∷ mkHamiltonianTerm synthesisSequencingRiskObservable supervoxelHamiltonian false true false
    "writing and reading risk is an operational pipeline observable rather than an exact sequence-only law"
  ∷ []

------------------------------------------------------------------------
-- Configured hard-bound surface.

record ChemistryConstraintConfig : Set where
  constructor mkChemistryConstraintConfig
  field
    maximumHomopolymerRun : Nat
    hairpinStemMinimum : Nat
    hairpinSearchRadius : Nat
    mismatchClassesIncluded : Nat
    hardBanExactReverseComplement : Bool
    hardBanNearReverseComplement : Bool
    multiscaleGCEnabled : Bool
    multiscaleRYEnabled : Bool
    nearestNeighbourDeltaGEnabled : Bool

open ChemistryConstraintConfig public

canonicalChemistryConstraintConfig : ChemistryConstraintConfig
canonicalChemistryConstraintConfig =
  mkChemistryConstraintConfig
    4
    8
    64
    2
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- Sheet Hamiltonian coordinates.
--
-- The coefficients remain abstract here.  A concrete numerical adapter may use
-- mean-square sheet energy, reverse-complement cross-correlation, mismatch-
-- weighted kernels, or nearest-neighbour Delta G tables.  Cross-rank coupling is
-- explicit and band independence is not assumed.

data SheetChannel : Set where
  UChannel : SheetChannel
  VChannel : SheetChannel
  UVInteractionChannel : SheetChannel
  reverseComplementChannel : SheetChannel
  thermoKernelChannel : SheetChannel

record SheetHamiltonianCoordinate : Set where
  constructor mkSheetHamiltonianCoordinate
  field
    sourceRank : Lift.FourLiftRank
    targetRank : Lift.FourLiftRank
    channel : SheetChannel
    crossRankCoupled : Bool
    hardGate : Bool
    operationalOnly : Bool

open SheetHamiltonianCoordinate public

canonicalSheetHamiltonianCoordinates : List SheetHamiltonianCoordinate
canonicalSheetHamiltonianCoordinates =
  mkSheetHamiltonianCoordinate Lift.pointRank Lift.lineRank UChannel false true true
  ∷ mkSheetHamiltonianCoordinate Lift.pointRank Lift.lineRank VChannel false false true
  ∷ mkSheetHamiltonianCoordinate Lift.lineRank Lift.sheetRank thermoKernelChannel true false true
  ∷ mkSheetHamiltonianCoordinate Lift.sheetRank Lift.voxelRank reverseComplementChannel true true true
  ∷ mkSheetHamiltonianCoordinate Lift.voxelRank Lift.supervoxelRank UVInteractionChannel true true true
  ∷ []

------------------------------------------------------------------------
-- Operational chemistry quotient.

data ChemistryBasin : Set where
  admissibleChemistryBasin : ChemistryBasin
  constrainedRiskBasin : ChemistryBasin
  invalidWritingBasin : ChemistryBasin
  unresolvedMicroscopicBasin : ChemistryBasin

record ChemistryObservationProfile : Set where
  constructor mkChemistryObservationProfile
  field
    basin : ChemistryBasin
    gcConstraintSatisfied : Bool
    runConstraintSatisfied : Bool
    motifConstraintSatisfied : Bool
    hairpinConstraintSatisfied : Bool
    dimerConstraintSatisfied : Bool
    synthesisRiskAccepted : Bool
    sequencingRiskAccepted : Bool

open ChemistryObservationProfile public

sameOperationalChemistryBasin :
  ChemistryObservationProfile →
  ChemistryObservationProfile →
  Bool
sameOperationalChemistryBasin
  (mkChemistryObservationProfile admissibleChemistryBasin _ _ _ _ _ _ _)
  (mkChemistryObservationProfile admissibleChemistryBasin _ _ _ _ _ _ _) = true
sameOperationalChemistryBasin
  (mkChemistryObservationProfile constrainedRiskBasin _ _ _ _ _ _ _)
  (mkChemistryObservationProfile constrainedRiskBasin _ _ _ _ _ _ _) = true
sameOperationalChemistryBasin
  (mkChemistryObservationProfile invalidWritingBasin _ _ _ _ _ _ _)
  (mkChemistryObservationProfile invalidWritingBasin _ _ _ _ _ _ _) = true
sameOperationalChemistryBasin
  (mkChemistryObservationProfile unresolvedMicroscopicBasin _ _ _ _ _ _ _)
  (mkChemistryObservationProfile unresolvedMicroscopicBasin _ _ _ _ _ _ _) = true
sameOperationalChemistryBasin _ _ = false

------------------------------------------------------------------------
-- Scope receipt.

record DNAChemistryHamiltonianReceipt : Set where
  constructor mkDNAChemistryHamiltonianReceipt
  field
    configuredConstraints : ChemistryConstraintConfig
    terms : List HamiltonianTerm
    coordinates : List SheetHamiltonianCoordinate
    gcActsAcrossLifts : Bool
    runsPermitLengthFour : Bool
    hairpinsCoupleRanks : Bool
    nearestNeighbourIsKernelApproximation : Bool
    chemistryIsMicroscopicallyExactInPrinciple : Bool
    codecCarriesCompleteMicroscopicState : Bool
    operationalQuotientIsExplicit : Bool
    hamiltonianBoundaryHolds : Bool
    hamiltonianBoundaryHoldsIsTrue : hamiltonianBoundaryHolds ≡ true

open DNAChemistryHamiltonianReceipt public

canonicalDNAChemistryHamiltonianReceipt : DNAChemistryHamiltonianReceipt
canonicalDNAChemistryHamiltonianReceipt =
  mkDNAChemistryHamiltonianReceipt
    canonicalChemistryConstraintConfig
    canonicalHamiltonianTerms
    canonicalSheetHamiltonianCoordinates
    true
    true
    true
    true
    true
    false
    true
    true
    refl
