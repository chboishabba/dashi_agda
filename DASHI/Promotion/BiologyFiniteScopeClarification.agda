module DASHI.Promotion.BiologyFiniteScopeClarification where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Constants.Registry as Registry
open import Ontology.DNA.Supervoxel4Adic using
  (Base; A; C; G; T; DNA4; DNA16; DNA64; DNA256; FlatDNA256)
import Ontology.DNA.SemanticChecksumAlgebra as Checksum
import Ontology.DNA.StreamingEncoderSurface as Streaming

------------------------------------------------------------------------
-- Finite biological scope clarification.
--
-- This module deliberately separates a legitimate finite DNA/protein
-- combinatorial bridge from biological, causal, clinical, or brain-state
-- promotion.  The positive surface is finite and structured: DNA bases,
-- codons, standard genetic-code targets, supervoxel carriers, streaming
-- encoder checksums, and whole-chain checksum laws.  The negative surface
-- imports the registry's false guards and lists the external authority
-- receipts required before any empirical promotion can be considered.

data AminoAcid : Set where
  Ala Arg Asn Asp Cys Gln Glu Gly His Ile Leu Lys Met Phe Pro Ser Thr Trp Tyr
    Val : AminoAcid

data StopSignal : Set where
  ochre amber opal : StopSignal

data ProteinSymbol : Set where
  aminoAcid : AminoAcid → ProteinSymbol
  stopSignal : StopSignal → ProteinSymbol

record Codon : Set where
  constructor codon
  field
    first second third : Base

open Codon public

translateCodon : Codon → ProteinSymbol
translateCodon (codon T T T) = aminoAcid Phe
translateCodon (codon T T C) = aminoAcid Phe
translateCodon (codon T T A) = aminoAcid Leu
translateCodon (codon T T G) = aminoAcid Leu
translateCodon (codon T C T) = aminoAcid Ser
translateCodon (codon T C C) = aminoAcid Ser
translateCodon (codon T C A) = aminoAcid Ser
translateCodon (codon T C G) = aminoAcid Ser
translateCodon (codon T A T) = aminoAcid Tyr
translateCodon (codon T A C) = aminoAcid Tyr
translateCodon (codon T A A) = stopSignal ochre
translateCodon (codon T A G) = stopSignal amber
translateCodon (codon T G T) = aminoAcid Cys
translateCodon (codon T G C) = aminoAcid Cys
translateCodon (codon T G A) = stopSignal opal
translateCodon (codon T G G) = aminoAcid Trp
translateCodon (codon C T T) = aminoAcid Leu
translateCodon (codon C T C) = aminoAcid Leu
translateCodon (codon C T A) = aminoAcid Leu
translateCodon (codon C T G) = aminoAcid Leu
translateCodon (codon C C T) = aminoAcid Pro
translateCodon (codon C C C) = aminoAcid Pro
translateCodon (codon C C A) = aminoAcid Pro
translateCodon (codon C C G) = aminoAcid Pro
translateCodon (codon C A T) = aminoAcid His
translateCodon (codon C A C) = aminoAcid His
translateCodon (codon C A A) = aminoAcid Gln
translateCodon (codon C A G) = aminoAcid Gln
translateCodon (codon C G T) = aminoAcid Arg
translateCodon (codon C G C) = aminoAcid Arg
translateCodon (codon C G A) = aminoAcid Arg
translateCodon (codon C G G) = aminoAcid Arg
translateCodon (codon A T T) = aminoAcid Ile
translateCodon (codon A T C) = aminoAcid Ile
translateCodon (codon A T A) = aminoAcid Ile
translateCodon (codon A T G) = aminoAcid Met
translateCodon (codon A C T) = aminoAcid Thr
translateCodon (codon A C C) = aminoAcid Thr
translateCodon (codon A C A) = aminoAcid Thr
translateCodon (codon A C G) = aminoAcid Thr
translateCodon (codon A A T) = aminoAcid Asn
translateCodon (codon A A C) = aminoAcid Asn
translateCodon (codon A A A) = aminoAcid Lys
translateCodon (codon A A G) = aminoAcid Lys
translateCodon (codon A G T) = aminoAcid Ser
translateCodon (codon A G C) = aminoAcid Ser
translateCodon (codon A G A) = aminoAcid Arg
translateCodon (codon A G G) = aminoAcid Arg
translateCodon (codon G T T) = aminoAcid Val
translateCodon (codon G T C) = aminoAcid Val
translateCodon (codon G T A) = aminoAcid Val
translateCodon (codon G T G) = aminoAcid Val
translateCodon (codon G C T) = aminoAcid Ala
translateCodon (codon G C C) = aminoAcid Ala
translateCodon (codon G C A) = aminoAcid Ala
translateCodon (codon G C G) = aminoAcid Ala
translateCodon (codon G A T) = aminoAcid Asp
translateCodon (codon G A C) = aminoAcid Asp
translateCodon (codon G A A) = aminoAcid Glu
translateCodon (codon G A G) = aminoAcid Glu
translateCodon (codon G G T) = aminoAcid Gly
translateCodon (codon G G C) = aminoAcid Gly
translateCodon (codon G G A) = aminoAcid Gly
translateCodon (codon G G G) = aminoAcid Gly

baseAlphabetCount : Nat
baseAlphabetCount = 4

codonCombinatorialCount : Nat
codonCombinatorialCount = baseAlphabetCount * baseAlphabetCount * baseAlphabetCount

aminoAcidSymbolCount : Nat
aminoAcidSymbolCount = 20

stopSignalCount : Nat
stopSignalCount = 3

proteinTargetSymbolCount : Nat
proteinTargetSymbolCount = aminoAcidSymbolCount + stopSignalCount
  where
    _+_ : Nat → Nat → Nat
    zero + n = n
    suc m + n = suc (m + n)

baseAlphabetCountIs4 : baseAlphabetCount ≡ 4
baseAlphabetCountIs4 = refl

codonCombinatorialCountIs64 : codonCombinatorialCount ≡ 64
codonCombinatorialCountIs64 = refl

aminoAcidSymbolCountIs20 : aminoAcidSymbolCount ≡ 20
aminoAcidSymbolCountIs20 = refl

stopSignalCountIs3 : stopSignalCount ≡ 3
stopSignalCountIs3 = refl

proteinTargetSymbolCountIs23 : proteinTargetSymbolCount ≡ 23
proteinTargetSymbolCountIs23 = refl

standardStartCodonTargetsMethionine :
  translateCodon (codon A T G) ≡ aminoAcid Met
standardStartCodonTargetsMethionine = refl

canonicalStopCodonsRemainStops :
  List ProteinSymbol
canonicalStopCodonsRemainStops =
  translateCodon (codon T A A)
    ∷ translateCodon (codon T A G)
    ∷ translateCodon (codon T G A)
    ∷ []

record FiniteGeneticCodeBridge : Set₁ where
  field
    dnaBase : Set
    codonCarrier : Set
    proteinSymbolCarrier : Set
    translate : Codon → ProteinSymbol
    baseCount : Nat
    baseCountIs4 : baseCount ≡ 4
    codonCount : Nat
    codonCountIs64 : codonCount ≡ 64
    aminoAcidCount : Nat
    aminoAcidCountIs20 : aminoAcidCount ≡ 20
    stopCount : Nat
    stopCountIs3 : stopCount ≡ 3
    targetSymbolCount : Nat
    targetSymbolCountIs23 : targetSymbolCount ≡ 23
    bridgeStructured : Bool
    bridgeStructuredIsTrue : bridgeStructured ≡ true
    semanticsPromoted : Bool
    semanticsPromotedIsFalse : semanticsPromoted ≡ false

open FiniteGeneticCodeBridge public

canonicalFiniteGeneticCodeBridge : FiniteGeneticCodeBridge
canonicalFiniteGeneticCodeBridge = record
  { dnaBase = Base
  ; codonCarrier = Codon
  ; proteinSymbolCarrier = ProteinSymbol
  ; translate = translateCodon
  ; baseCount = baseAlphabetCount
  ; baseCountIs4 = baseAlphabetCountIs4
  ; codonCount = codonCombinatorialCount
  ; codonCountIs64 = codonCombinatorialCountIs64
  ; aminoAcidCount = aminoAcidSymbolCount
  ; aminoAcidCountIs20 = aminoAcidSymbolCountIs20
  ; stopCount = stopSignalCount
  ; stopCountIs3 = stopSignalCountIs3
  ; targetSymbolCount = proteinTargetSymbolCount
  ; targetSymbolCountIs23 = proteinTargetSymbolCountIs23
  ; bridgeStructured = true
  ; bridgeStructuredIsTrue = refl
  ; semanticsPromoted = false
  ; semanticsPromotedIsFalse = refl
  }

record SupervoxelChecksumScope : Set₁ where
  field
    block4Carrier : Set
    block16Carrier : Set
    block64Carrier : Set
    block256Carrier : Set
    flat256Carrier : Set
    streamingSurface : Streaming.StreamingEncoderSurface
    checksumLaw : Checksum.WholeChainChecksumLaw
    supervoxelStructured : Bool
    supervoxelStructuredIsTrue : supervoxelStructured ≡ true
    checksumStructured : Bool
    checksumStructuredIsTrue : checksumStructured ≡ true
    empiricalSequenceAuthorityAccepted : Bool
    empiricalSequenceAuthorityAcceptedIsFalse :
      empiricalSequenceAuthorityAccepted ≡ false

open SupervoxelChecksumScope public

canonicalSupervoxelChecksumScope : SupervoxelChecksumScope
canonicalSupervoxelChecksumScope = record
  { block4Carrier = DNA4
  ; block16Carrier = DNA16
  ; block64Carrier = DNA64
  ; block256Carrier = DNA256
  ; flat256Carrier = FlatDNA256
  ; streamingSurface = Streaming.streamingEncoderSurface
  ; checksumLaw = Checksum.singletonCWholeChainChecksumLaw
  ; supervoxelStructured = true
  ; supervoxelStructuredIsTrue = refl
  ; checksumStructured = true
  ; checksumStructuredIsTrue = refl
  ; empiricalSequenceAuthorityAccepted = false
  ; empiricalSequenceAuthorityAcceptedIsFalse = refl
  }

externalBiologyAuthorityRequirements : List String
externalBiologyAuthorityRequirements =
  "organism, tissue, cell-line, assay, and session provenance"
  ∷ "sequence or sample checksum plus protocol/source authority"
  ∷ "causal-identification and intervention/counterfactual receipt"
  ∷ "clinical validity, utility, regulatory, and ethics authority"
  ∷ "neuroimaging/connectome checksum with BIDS/FAIR metadata"
  ∷ "developmental, morphogenetic, and genome-to-connectome calibration"
  ∷ []

requirementCount : List String → Nat
requirementCount [] = zero
requirementCount (_ ∷ xs) = suc (requirementCount xs)

canonicalExternalAuthorityRequirementCount : Nat
canonicalExternalAuthorityRequirementCount =
  requirementCount externalBiologyAuthorityRequirements

canonicalExternalAuthorityRequirementCountIs6 :
  canonicalExternalAuthorityRequirementCount ≡ 6
canonicalExternalAuthorityRequirementCountIs6 = refl

record BiologyFalsePromotionGuards : Set₁ where
  field
    biologyReceipt : Registry.BiologyKnownInputsReferenceReceipt
    externalAuthorityRequirements : List String
    externalAuthorityRequirementCount : Nat
    externalAuthorityRequirementCountIs6 :
      externalAuthorityRequirementCount ≡ 6
    structuredBiologyBridgePopulated : Bool
    structuredBiologyBridgePopulatedIsTrue :
      structuredBiologyBridgePopulated ≡ true
    biologyCausationPromoted : Bool
    biologyCausationPromotedIsFalse :
      biologyCausationPromoted ≡ false
    interventionPromoted : Bool
    interventionPromotedIsFalse :
      interventionPromoted ≡ false
    clinicalValidityAccepted : Bool
    clinicalValidityAcceptedIsFalse :
      clinicalValidityAccepted ≡ false
    genomeToConnectomeClosurePromoted : Bool
    genomeToConnectomeClosurePromotedIsFalse :
      genomeToConnectomeClosurePromoted ≡ false
    brainStateRecoveryPromoted : Bool
    brainStateRecoveryPromotedIsFalse :
      brainStateRecoveryPromoted ≡ false
    externalInputOnly : Bool
    externalInputOnlyIsTrue :
      externalInputOnly ≡ true

open BiologyFalsePromotionGuards public

canonicalBiologyFalsePromotionGuards : BiologyFalsePromotionGuards
canonicalBiologyFalsePromotionGuards = record
  { biologyReceipt = Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; externalAuthorityRequirements =
      externalBiologyAuthorityRequirements
  ; externalAuthorityRequirementCount =
      canonicalExternalAuthorityRequirementCount
  ; externalAuthorityRequirementCountIs6 =
      canonicalExternalAuthorityRequirementCountIs6
  ; structuredBiologyBridgePopulated =
      Registry.BiologyKnownInputsReferenceReceipt.structuredBiologyBridgePopulated
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; structuredBiologyBridgePopulatedIsTrue =
      Registry.BiologyKnownInputsReferenceReceipt.structuredBiologyBridgePopulatedIsTrue
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; biologyCausationPromoted =
      Registry.BiologyKnownInputsReferenceReceipt.biologyCausationPromoted
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; biologyCausationPromotedIsFalse =
      Registry.BiologyKnownInputsReferenceReceipt.biologyCausationPromotedIsFalse
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; interventionPromoted =
      Registry.BiologyKnownInputsReferenceReceipt.interventionPromoted
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; interventionPromotedIsFalse =
      Registry.BiologyKnownInputsReferenceReceipt.interventionPromotedIsFalse
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; clinicalValidityAccepted =
      Registry.BiologyKnownInputsReferenceReceipt.clinicalValidityAccepted
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; clinicalValidityAcceptedIsFalse =
      Registry.BiologyKnownInputsReferenceReceipt.clinicalValidityAcceptedIsFalse
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; genomeToConnectomeClosurePromoted =
      Registry.BiologyKnownInputsReferenceReceipt.genomeToConnectomeClosurePromoted
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; genomeToConnectomeClosurePromotedIsFalse =
      Registry.BiologyKnownInputsReferenceReceipt.genomeToConnectomeClosurePromotedIsFalse
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; brainStateRecoveryPromoted =
      Registry.BiologyKnownInputsReferenceReceipt.brainStateRecoveryPromoted
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; brainStateRecoveryPromotedIsFalse =
      Registry.BiologyKnownInputsReferenceReceipt.brainStateRecoveryPromotedIsFalse
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; externalInputOnly =
      Registry.BiologyKnownInputsReferenceReceipt.externalInputOnly
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; externalInputOnlyIsTrue =
      Registry.BiologyKnownInputsReferenceReceipt.externalInputOnlyIsTrue
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  }

record BiologyFiniteScopeClarification : Set₁ where
  field
    geneticCodeBridge : FiniteGeneticCodeBridge
    supervoxelChecksumScope : SupervoxelChecksumScope
    falsePromotionGuards : BiologyFalsePromotionGuards
    legitimateFiniteStructurePopulated : Bool
    legitimateFiniteStructurePopulatedIsTrue :
      legitimateFiniteStructurePopulated ≡ true
    biologicalCausationRequiresExternalAuthority : Bool
    biologicalCausationRequiresExternalAuthorityIsTrue :
      biologicalCausationRequiresExternalAuthority ≡ true
    promotesBiologicalOrClinicalClaim : Bool
    promotesBiologicalOrClinicalClaimIsFalse :
      promotesBiologicalOrClinicalClaim ≡ false
    validationCommand : String

open BiologyFiniteScopeClarification public

canonicalBiologyFiniteScopeClarification :
  BiologyFiniteScopeClarification
canonicalBiologyFiniteScopeClarification = record
  { geneticCodeBridge = canonicalFiniteGeneticCodeBridge
  ; supervoxelChecksumScope = canonicalSupervoxelChecksumScope
  ; falsePromotionGuards = canonicalBiologyFalsePromotionGuards
  ; legitimateFiniteStructurePopulated = true
  ; legitimateFiniteStructurePopulatedIsTrue = refl
  ; biologicalCausationRequiresExternalAuthority = true
  ; biologicalCausationRequiresExternalAuthorityIsTrue = refl
  ; promotesBiologicalOrClinicalClaim = false
  ; promotesBiologicalOrClinicalClaimIsFalse = refl
  ; validationCommand =
      "agda -i . DASHI/Promotion/BiologyFiniteScopeClarification.agda"
  }
