module DASHI.Interop.UnifiedMathLanguageAssertedProofs where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Sigma using (snd)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.UnifiedMathLanguageSpine as Unified
import DASHI.Interop.PNFHyperfabric369 as Hyperfabric
import Ontology.DNA.Supervoxel4Adic as DNA
import Ontology.DNA.ChemistryConcrete as Chemistry
import Ontology.DNA.ChemistryQuotient as Quotient
import Ontology.DNA.ChemistrySheetHamiltonian as Hamiltonian
import Ontology.DNA.CrossoverAttachmentSurface as Crossover
import Ontology.DNA.SupervoxelAdmissibility as Supervoxel
import Ontology.DNA.SupervoxelChemistryCouplingLaws as Coupling
import Ontology.DNA.StreamingEncoderSurface as Streaming

------------------------------------------------------------------------
-- Asserted proof layer for the unified math language.
--
-- The carrier spine records vocabulary and projection boundaries.  This
-- module is the next layer up: it records where the repository has an
-- internally asserted proof surface, especially definitional equalities that
-- check by computation/refl or by existing local witnesses.
--
-- "Asserted" here means internal to the DASHI formal corpus.  It does not
-- promote Clay, legal, Wikidata, biological truth, or external physics theorem
-- authority.

data ProofPosture : Set where
  carrierOnly : ProofPosture
  internalDefinitionalProof : ProofPosture
  internalConditionalProof : ProofPosture
  approachingClosedProof : ProofPosture
  externalPromotionBlocked : ProofPosture

data AssertedProofLane : Set where
  chemistryDefinitionLane : AssertedProofLane
  supervoxelChemistryLane : AssertedProofLane
  pnfHyperfabric369Lane : AssertedProofLane
  brainFMRIObservationLane : AssertedProofLane
  biologyChemistryParentLane : AssertedProofLane
  navierStokesApproachLane : AssertedProofLane
  yangMillsApproachLane : AssertedProofLane
  unifiedCarrierParentLane : AssertedProofLane
  externalBoundaryLane : AssertedProofLane

canonicalAssertedProofLanes : List AssertedProofLane
canonicalAssertedProofLanes =
  chemistryDefinitionLane
  ∷ supervoxelChemistryLane
  ∷ pnfHyperfabric369Lane
  ∷ brainFMRIObservationLane
  ∷ biologyChemistryParentLane
  ∷ navierStokesApproachLane
  ∷ yangMillsApproachLane
  ∷ unifiedCarrierParentLane
  ∷ externalBoundaryLane
  ∷ []

lanePosture : AssertedProofLane → ProofPosture
lanePosture chemistryDefinitionLane =
  internalDefinitionalProof
lanePosture supervoxelChemistryLane =
  internalDefinitionalProof
lanePosture pnfHyperfabric369Lane =
  internalDefinitionalProof
lanePosture brainFMRIObservationLane =
  carrierOnly
lanePosture biologyChemistryParentLane =
  internalConditionalProof
lanePosture navierStokesApproachLane =
  approachingClosedProof
lanePosture yangMillsApproachLane =
  approachingClosedProof
lanePosture unifiedCarrierParentLane =
  carrierOnly
lanePosture externalBoundaryLane =
  externalPromotionBlocked

chemistryLaneIsDefinitional :
  lanePosture chemistryDefinitionLane ≡ internalDefinitionalProof
chemistryLaneIsDefinitional =
  refl

supervoxelChemistryLaneIsDefinitional :
  lanePosture supervoxelChemistryLane ≡ internalDefinitionalProof
supervoxelChemistryLaneIsDefinitional =
  refl

pnfHyperfabric369LaneIsDefinitional :
  lanePosture pnfHyperfabric369Lane ≡ internalDefinitionalProof
pnfHyperfabric369LaneIsDefinitional =
  refl

brainFMRIObservationLaneIsCarrierOnly :
  lanePosture brainFMRIObservationLane ≡ carrierOnly
brainFMRIObservationLaneIsCarrierOnly =
  refl

navierStokesLaneIsApproachingClosed :
  lanePosture navierStokesApproachLane ≡ approachingClosedProof
navierStokesLaneIsApproachingClosed =
  refl

yangMillsLaneIsApproachingClosed :
  lanePosture yangMillsApproachLane ≡ approachingClosedProof
yangMillsLaneIsApproachingClosed =
  refl

externalBoundaryBlocksPromotion :
  lanePosture externalBoundaryLane ≡ externalPromotionBlocked
externalBoundaryBlocksPromotion =
  refl

record ChemistryDefinitionalProofSurface : Set₁ where
  field
    quotientInterface :
      Quotient.ChemistryQuotientInterface

    quotientInterfaceIsConcrete :
      quotientInterface ≡ Chemistry.chemistryQuotientInterfaceConcrete

    sectionProof :
      (u : Quotient.FeatureU) →
      (v : Quotient.FeatureV) →
      Chemistry.featureMapConcrete (Chemistry.representativeUV u v)
        ≡
        Quotient.chemistryFeature u v

    sectionProofIsConcrete :
      sectionProof ≡ Chemistry.sectionUV

    mergeStrengthDefinitional :
      (u : Quotient.Strength) →
      (v : Quotient.PurineClass) →
      Quotient.strength (Chemistry.mergeBase u v) ≡ u

    mergePurineDefinitional :
      (u : Quotient.Strength) →
      (v : Quotient.PurineClass) →
      Quotient.purineClass (Chemistry.mergeBase u v) ≡ v

    sheetHamiltonian :
      DNA.FlatDNA256 → Nat

    sheetHamiltonianIsConcrete :
      sheetHamiltonian ≡ Hamiltonian.chemistryHamiltonian

    internalProofPromoted :
      Bool

    internalProofPromotedIsTrue :
      internalProofPromoted ≡ true

    externalAuthorityPromoted :
      Bool

    externalAuthorityPromotedIsFalse :
      externalAuthorityPromoted ≡ false

canonicalChemistryDefinitionalProofSurface :
  ChemistryDefinitionalProofSurface
canonicalChemistryDefinitionalProofSurface =
  record
    { quotientInterface =
        Chemistry.chemistryQuotientInterfaceConcrete
    ; quotientInterfaceIsConcrete =
        refl
    ; sectionProof =
        Chemistry.sectionUV
    ; sectionProofIsConcrete =
        refl
    ; mergeStrengthDefinitional =
        Chemistry.merge-strength
    ; mergePurineDefinitional =
        Chemistry.merge-purine
    ; sheetHamiltonian =
        Hamiltonian.chemistryHamiltonian
    ; sheetHamiltonianIsConcrete =
        refl
    ; internalProofPromoted =
        true
    ; internalProofPromotedIsTrue =
        refl
    ; externalAuthorityPromoted =
        false
    ; externalAuthorityPromotedIsFalse =
        refl
    }

record SupervoxelChemistryDefinitionalProofSurface : Set₁ where
  field
    admissibilitySurface :
      Supervoxel.SupervoxelAdmissibilitySurface

    admissibilitySurfaceIsCanonical :
      admissibilitySurface ≡ Supervoxel.supervoxelAdmissibilitySurface

    couplingSurface :
      Coupling.SupervoxelChemistryCouplingLawSurface

    couplingSurfaceIsCanonical :
      couplingSurface ≡ Coupling.supervoxelChemistryCouplingLawSurface

    reverseComplementInvolution :
      (sv : Supervoxel.Supervoxel256) →
      Supervoxel.swapRC (Supervoxel.swapRC sv) ≡ sv

    reverseComplementInvolutionIsCanonical :
      reverseComplementInvolution ≡ Supervoxel.swapRC-involutive

    leftStreamingHamiltonianOwner :
      (sv : Supervoxel.Supervoxel256) →
      snd
        (Streaming.StreamingEncoderSurface.checksumSurface
          (Crossover.CrossoverAttachmentSurface.streaming
            Crossover.crossoverAttachmentSurface)
          (Streaming.stateOf (Supervoxel.Supervoxel256.leftVoxel sv)))
      ≡
      Hamiltonian.chemistryHamiltonianOf
        (Supervoxel.Supervoxel256.leftVoxel sv)

    rightStreamingHamiltonianOwner :
      (sv : Supervoxel.Supervoxel256) →
      snd
        (Streaming.StreamingEncoderSurface.checksumSurface
          (Crossover.CrossoverAttachmentSurface.streaming
            Crossover.crossoverAttachmentSurface)
          (Streaming.stateOf (Supervoxel.Supervoxel256.rightVoxel sv)))
      ≡
      Hamiltonian.chemistryHamiltonianOf
        (Supervoxel.Supervoxel256.rightVoxel sv)

    coupledStreamingHamiltonian :
      (sv : Supervoxel.Supervoxel256) →
      Supervoxel.SupervoxelChecksum.leftHamiltonian
        (Supervoxel.supervoxelChecksum sv)
        +
      Supervoxel.SupervoxelChecksum.rightHamiltonian
        (Supervoxel.supervoxelChecksum sv)
      ≡
      snd
        (Streaming.StreamingEncoderSurface.checksumSurface
          (Crossover.CrossoverAttachmentSurface.streaming
            Crossover.crossoverAttachmentSurface)
          (Streaming.stateOf (Supervoxel.Supervoxel256.leftVoxel sv)))
        +
      snd
        (Streaming.StreamingEncoderSurface.checksumSurface
          (Crossover.CrossoverAttachmentSurface.streaming
            Crossover.crossoverAttachmentSurface)
          (Streaming.stateOf (Supervoxel.Supervoxel256.rightVoxel sv)))

    internalProofPromoted :
      Bool

    internalProofPromotedIsTrue :
      internalProofPromoted ≡ true

    externalPhysicsPromoted :
      Bool

    externalPhysicsPromotedIsFalse :
      externalPhysicsPromoted ≡ false

canonicalSupervoxelChemistryDefinitionalProofSurface :
  SupervoxelChemistryDefinitionalProofSurface
canonicalSupervoxelChemistryDefinitionalProofSurface =
  record
    { admissibilitySurface =
        Supervoxel.supervoxelAdmissibilitySurface
    ; admissibilitySurfaceIsCanonical =
        refl
    ; couplingSurface =
        Coupling.supervoxelChemistryCouplingLawSurface
    ; couplingSurfaceIsCanonical =
        refl
    ; reverseComplementInvolution =
        Supervoxel.swapRC-involutive
    ; reverseComplementInvolutionIsCanonical =
        refl
    ; leftStreamingHamiltonianOwner =
        Coupling.leftStreamingHamiltonianOwnerCanonicalWitness
    ; rightStreamingHamiltonianOwner =
        Coupling.rightStreamingHamiltonianOwnerCanonicalWitness
    ; coupledStreamingHamiltonian =
        Coupling.coupledStreamingHamiltonianCanonicalWitness
    ; internalProofPromoted =
        true
    ; internalProofPromotedIsTrue =
        refl
    ; externalPhysicsPromoted =
        false
    ; externalPhysicsPromotedIsFalse =
        refl
    }

internalProofPromotionAllowed : AssertedProofLane → Bool
internalProofPromotionAllowed chemistryDefinitionLane =
  true
internalProofPromotionAllowed supervoxelChemistryLane =
  true
internalProofPromotionAllowed pnfHyperfabric369Lane =
  true
internalProofPromotionAllowed brainFMRIObservationLane =
  false
internalProofPromotionAllowed biologyChemistryParentLane =
  false
internalProofPromotionAllowed navierStokesApproachLane =
  false
internalProofPromotionAllowed yangMillsApproachLane =
  false
internalProofPromotionAllowed unifiedCarrierParentLane =
  false
internalProofPromotionAllowed externalBoundaryLane =
  false

externalTheoremPromotionAllowed : AssertedProofLane → Bool
externalTheoremPromotionAllowed _ =
  false

chemistryInternalProofPromotionAllowed :
  internalProofPromotionAllowed chemistryDefinitionLane ≡ true
chemistryInternalProofPromotionAllowed =
  refl

supervoxelChemistryInternalProofPromotionAllowed :
  internalProofPromotionAllowed supervoxelChemistryLane ≡ true
supervoxelChemistryInternalProofPromotionAllowed =
  refl

pnfHyperfabric369InternalProofPromotionAllowed :
  internalProofPromotionAllowed pnfHyperfabric369Lane ≡ true
pnfHyperfabric369InternalProofPromotionAllowed =
  refl

brainFMRIInternalProofPromotionBlocked :
  internalProofPromotionAllowed brainFMRIObservationLane ≡ false
brainFMRIInternalProofPromotionBlocked =
  refl

brainFMRIExternalPromotionBlocked :
  externalTheoremPromotionAllowed brainFMRIObservationLane ≡ false
brainFMRIExternalPromotionBlocked =
  refl

navierStokesExternalPromotionBlocked :
  externalTheoremPromotionAllowed navierStokesApproachLane ≡ false
navierStokesExternalPromotionBlocked =
  refl

yangMillsExternalPromotionBlocked :
  externalTheoremPromotionAllowed yangMillsApproachLane ≡ false
yangMillsExternalPromotionBlocked =
  refl

record UnifiedMathLanguageAssertedProofSurface : Set₁ where
  field
    unifiedCarrierSurface :
      Unified.UnifiedMathLanguageSurface

    unifiedCarrierSurfaceIsCanonical :
      unifiedCarrierSurface ≡ Unified.canonicalUnifiedMathLanguageSurface

    lanes :
      List AssertedProofLane

    lanesAreCanonical :
      lanes ≡ canonicalAssertedProofLanes

    posture :
      AssertedProofLane → ProofPosture

    postureIsCanonical :
      posture ≡ lanePosture

    chemistryProof :
      ChemistryDefinitionalProofSurface

    chemistryProofIsCanonical :
      chemistryProof ≡ canonicalChemistryDefinitionalProofSurface

    supervoxelChemistryProof :
      SupervoxelChemistryDefinitionalProofSurface

    supervoxelChemistryProofIsCanonical :
      supervoxelChemistryProof
        ≡
        canonicalSupervoxelChemistryDefinitionalProofSurface

    pnfHyperfabric369Proof :
      Hyperfabric.PNFHyperfabric369Surface

    pnfHyperfabric369ProofIsCanonical :
      pnfHyperfabric369Proof
        ≡
        Hyperfabric.canonicalPNFHyperfabric369Surface

    internalPromotion :
      AssertedProofLane → Bool

    internalPromotionIsCanonical :
      internalPromotion ≡ internalProofPromotionAllowed

    externalPromotion :
      AssertedProofLane → Bool

    externalPromotionIsCanonical :
      externalPromotion ≡ externalTheoremPromotionAllowed

    plainReading :
      String

canonicalUnifiedMathLanguageAssertedProofSurface :
  UnifiedMathLanguageAssertedProofSurface
canonicalUnifiedMathLanguageAssertedProofSurface =
  record
    { unifiedCarrierSurface =
        Unified.canonicalUnifiedMathLanguageSurface
    ; unifiedCarrierSurfaceIsCanonical =
        refl
    ; lanes =
        canonicalAssertedProofLanes
    ; lanesAreCanonical =
        refl
    ; posture =
        lanePosture
    ; postureIsCanonical =
        refl
    ; chemistryProof =
        canonicalChemistryDefinitionalProofSurface
    ; chemistryProofIsCanonical =
        refl
    ; supervoxelChemistryProof =
        canonicalSupervoxelChemistryDefinitionalProofSurface
    ; supervoxelChemistryProofIsCanonical =
        refl
    ; pnfHyperfabric369Proof =
        Hyperfabric.canonicalPNFHyperfabric369Surface
    ; pnfHyperfabric369ProofIsCanonical =
        refl
    ; internalPromotion =
        internalProofPromotionAllowed
    ; internalPromotionIsCanonical =
        refl
    ; externalPromotion =
        externalTheoremPromotionAllowed
    ; externalPromotionIsCanonical =
        refl
    ; plainReading =
        "The unified language now has an asserted internal proof layer. Chemistry, supervoxel-chemistry, and the 369 PNF hyperfabric are promoted internally as definitional/local checked proof surfaces. The brain/fMRI observation lane is carrier-only: it records quotient surfaces without empirical validation, latent-state recovery, cognition closure, or qualia closure. The 369 lane asserts the checked arithmetic shape 3*3=9, 9^2=81, and 3*3*3=27, with document-time as the hypervoxel axis and SSP/Monster as prime carriers. Biology-chemistry is conditional on its parents. Navier-Stokes and Yang-Mills are recorded as approaching closed proof lanes, but external theorem promotion remains blocked until their proof obligations are explicitly inhabited."
    }
