module DASHI.Chemistry.PAHMechanismStatePromotionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.MolecularMechanisticPromotionLadderExact as Ladder
import DASHI.Chemistry.LineageAcquiredPrimaryEvidenceExact as Evidence
import DASHI.Chemistry.LineageAcquiredQuantitativePaymentsExact as Payment
import DASHI.Biology.KitzerowBH4ReactionChemistryExact as BH4

------------------------------------------------------------------------
-- PAH SAME-OBJECT STRUCTURE / STATE / MECHANISM PROMOTION
--
-- The PAH gold replay is promoted beyond a reaction label using source-backed
-- structural artifacts, isotope lineage, single-turnover kinetics and a QM/MM
-- reaction-path model. None of this substitutes for the missing same-system
-- BH4 branch-allocation experiment.
------------------------------------------------------------------------

record ReleasedStructuralArtifact : Set where
  constructor releasedStructuralArtifact
  field
    artifactKey : String
    sourceReference : String
    objectReference : String
    resolutionReference : String
    coordinateCarrierReference : String
    artifactCreatesIndependentAuthority : Bool
    artifactCreatesIndependentAuthorityIsFalse : artifactCreatesIndependentAuthority ≡ false
    artifactCreatesElectronicWavefunction : Bool
    artifactCreatesElectronicWavefunctionIsFalse : artifactCreatesElectronicWavefunction ≡ false

open ReleasedStructuralArtifact public

pah1J8UArtifact : ReleasedStructuralArtifact
pah1J8UArtifact =
  releasedStructuralArtifact
    "PDB 1J8U"
    "LineageAcquiredPrimaryEvidenceExact.pahCatalyticDomainBH4PDB1J8U"
    "human PAH catalytic domain Fe(II) in complex with BH4"
    "1.50 A X-ray diffraction structure"
    "wwPDB/RCSB versioned coordinate and structure-factor carrier"
    false refl false refl

pah6HYCArtifact : ReleasedStructuralArtifact
pah6HYCArtifact =
  releasedStructuralArtifact
    "PDB 6HYC"
    "LineageAcquiredPrimaryEvidenceExact.pahFullLengthBH4PDB6HYC"
    "full-length human PAH in complex with BH4"
    "3.18 A crystal structure in primary publication; versioned wwPDB coordinates/diffraction carrier"
    "wwPDB/RCSB versioned coordinate and diffraction-data carrier"
    false refl false refl

record PAHMechanisticState : Set where
  constructor pahMechanisticState
  field
    reactionReference : String
    isotopeLineageReference : String
    catalyticStructureReference : String
    fullLengthStructureReference : String
    releasedCatalyticArtifact : ReleasedStructuralArtifact
    releasedFullLengthArtifact : ReleasedStructuralArtifact
    kineticMechanismReference : String
    qmmpesReference : String
    activeSiteReference : String
    stateInterpretation : String
    microscopicResidual : String

open PAHMechanisticState public

canonicalPAHMechanisticState : PAHMechanisticState
canonicalPAHMechanisticState =
  pahMechanisticState
    "KitzerowBH4ReactionChemistryExact.pahReaction: Phe + O2 + BH4 -> Tyr + qBH2 + H2O"
    "LineageAcquiredQuantitativePaymentsExact.pah4aOxygenLineagePayment"
    "Andersen/Flatmark/Hough 2001 Fe(II)/BH4 catalytic-domain structures; PDB 1J8T/1J8U"
    "Flydal et al. 2019 full-length human PAH unbound/BH4-bound structures; PDB 6HPO/6HYC"
    pah1J8UArtifact
    pah6HYCArtifact
    "Fitzpatrick et al. 2013 single-turnover PheHDelta117 mechanism: ordered BH4/Phe assembly, O2 binding, intermediates, hydroxylation and rate-determining product release"
    "Ishida et al. 2004 QM/MM + QM reaction-path/energetics model on a 5176-atom catalytic-domain model"
    "Fe(II), BH4 second coordination sphere / precatalytic-to-active positioning, substrate/cofactor/allosteric geometry remain source-conditioned"
    "same reaction now has typed reaction identity + isotope lineage + real structural coordinate artifacts + source-backed kinetic mechanism + source-backed QM/MM energetic path"
    "complete atom map, exact electronic Hamiltonian, real-space orbitals, CI/eigenvector coefficients, independent replay of the QM/MM calculation, and in-vivo branch flux remain unpaid"

canonicalPAHMechanisticPromotion : Ladder.MolecularMechanisticPromotion
canonicalPAHMechanisticPromotion =
  Ladder.molecularMechanisticPromotion
    "PAH/BH4 hydroxylation mechanistic promotion"
    "gold-R2 literal reaction replay; mechanistic depth consumer only — BH4 H1/H2/H3/H4 allocation consumer remains separate"
    Ladder.authorReleasedNumericalArtifact
    "1J8U catalytic-domain Fe(II):BH4 + 6HYC full-length hPAH:BH4 structural artifacts"
    "source-backed precatalytic/catalytic structural-state carrier; not an electronic eigenstate"
    "Ishida et al. 2004 QM/MM reaction-path and energetics model"
    "Fitzpatrick et al. 2013 single-turnover kinetic mechanism; not quantum wavepacket dynamics"
    "wwPDB 1J8U and 6HYC coordinate/diffraction artifacts"
    "no independent DASHI structural/QM/MM numerical replay acquired"
    "no real-space electronic wavefunction/eigenvector coefficient carrier acquired"
    Ladder.authorReleasedArtifact
    "same PAH reaction family with source/context distinctions retained explicitly"
    "full numerical Hamiltonian/wavefunction, exact complete atom map, independent numerical replay and in-vivo allocation/flux"
    false refl false refl

record PAHMechanisticPromotionBoundary : Set where
  constructor pahMechanisticPromotionBoundary
  field
    reactionIdentityPaid : Bool
    reactionIdentityPaidIsTrue : reactionIdentityPaid ≡ true
    partialOxygenLineagePaid : Bool
    partialOxygenLineagePaidIsTrue : partialOxygenLineagePaid ≡ true
    sourceBackedStructurePaid : Bool
    sourceBackedStructurePaidIsTrue : sourceBackedStructurePaid ≡ true
    literalReleasedStructuralCoordinatesPaid : Bool
    literalReleasedStructuralCoordinatesPaidIsTrue : literalReleasedStructuralCoordinatesPaid ≡ true
    sourceBackedKineticMechanismPaid : Bool
    sourceBackedKineticMechanismPaidIsTrue : sourceBackedKineticMechanismPaid ≡ true
    sourceBackedQMMPESPaid : Bool
    sourceBackedQMMPESPaidIsTrue : sourceBackedQMMPESPaid ≡ true
    completeAtomMapPaid : Bool
    completeAtomMapPaidIsFalse : completeAtomMapPaid ≡ false
    releasedHamiltonianMatrixPaid : Bool
    releasedHamiltonianMatrixPaidIsFalse : releasedHamiltonianMatrixPaid ≡ false
    numericRealSpaceWavefunctionPaid : Bool
    numericRealSpaceWavefunctionPaidIsFalse : numericRealSpaceWavefunctionPaid ≡ false
    qmmpesIndependentlyReplayed : Bool
    qmmpesIndependentlyReplayedIsFalse : qmmpesIndependentlyReplayed ≡ false
    mechanisticPromotionPaysBH4AllocationFlux : Bool
    mechanisticPromotionPaysBH4AllocationFluxIsFalse : mechanisticPromotionPaysBH4AllocationFlux ≡ false

open PAHMechanisticPromotionBoundary public

canonicalPAHMechanisticPromotionBoundary : PAHMechanisticPromotionBoundary
canonicalPAHMechanisticPromotionBoundary =
  pahMechanisticPromotionBoundary
    true refl true refl true refl true refl true refl true refl
    false refl false refl false refl false refl false refl
