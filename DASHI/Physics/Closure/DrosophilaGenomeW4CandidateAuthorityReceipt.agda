module DASHI.Physics.Closure.DrosophilaGenomeW4CandidateAuthorityReceipt where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Drosophila Release 6 genome candidate authority/checksum packet.
--
-- This is not a W4 physical-calibration receipt.  It records a locally
-- checksum-bound public genome/CDS artifact that may later support a W4
-- chemistry-law or Candidate256 calibration proposal.  The constructorless
-- Candidate256 physical-calibration authority token remains uninhabited.

data DrosophilaGenomeW4CandidateStatus : Set where
  candidateAuthorityAndChecksumBoundSelectionOnly :
    DrosophilaGenomeW4CandidateStatus

record DrosophilaGenomeW4CandidateAuthorityReceipt : Setω where
  field
    status :
      DrosophilaGenomeW4CandidateStatus

    organism :
      String

    assemblyAccession :
      String

    assemblyName :
      String

    release6ReferenceDOI :
      String

    release6ReferencePubMed :
      String

    rejectedPriorDOI :
      String

    rejectedPriorDOIReason :
      String

    ncbiDatasetsURL :
      String

    ncbiFTPDirectory :
      String

    authorityMetadataSHA256 :
      String

    genomicFASTASHA256 :
      String

    genomicSequenceCount :
      Nat

    genomicTotalBases :
      Nat

    cdsFASTASHA256 :
      String

    cdsSequenceCount :
      Nat

    cdsTotalBases :
      Nat

    totalACGTCodons :
      Nat

    distinctACGTCodons :
      Nat

    maxCodon :
      String

    maxCodonCount :
      Nat

    minNonzeroCodon :
      String

    minNonzeroCodonCount :
      Nat

    codonNonuniformWitness :
      Bool

    acceptedAuthorityRouteCandidate :
      Bool

    checksumBoundSelectionCandidate :
      Bool

    fastaChecksumBound :
      Bool

    cdsCodonWitnessBound :
      Bool

    constructsCalibrationLaw :
      Bool

    constructsCandidate256PhysicalCalibrationAuthorityToken :
      Bool

    constructsCandidate256PhysicalCalibrationExternalReceipt :
      Bool

    constructsBrainAtomicChemistryHandoffProof :
      Bool

    promotesW4 :
      Bool

    promotesBrainLane :
      Bool

    promotesPhysicsLane :
      Bool

    claimsUnification :
      Bool

    artifactPacket :
      String

    boundary :
      List String

canonicalDrosophilaGenomeW4CandidateAuthorityReceipt :
  DrosophilaGenomeW4CandidateAuthorityReceipt
canonicalDrosophilaGenomeW4CandidateAuthorityReceipt =
  record
    { status =
        candidateAuthorityAndChecksumBoundSelectionOnly
    ; organism =
        "Drosophila melanogaster"
    ; assemblyAccession =
        "GCF_000001215.4"
    ; assemblyName =
        "Release 6 plus ISO1 MT"
    ; release6ReferenceDOI =
        "10.1101/gr.185579.114"
    ; release6ReferencePubMed =
        "25589440"
    ; rejectedPriorDOI =
        "10.1126/science.1237175"
    ; rejectedPriorDOIReason =
        "not the Drosophila Release 6 reference sequence paper"
    ; ncbiDatasetsURL =
        "https://www.ncbi.nlm.nih.gov/datasets/genome/GCF_000001215.4/"
    ; ncbiFTPDirectory =
        "https://ftp.ncbi.nlm.nih.gov/genomes/all/GCF/000/001/215/GCF_000001215.4_Release_6_plus_ISO1_MT/"
    ; authorityMetadataSHA256 =
        "8e68338ea742454d7854721773f7d302b060ad53ffb79fae7b3f70996f02b902"
    ; genomicFASTASHA256 =
        "e69e907b5e87ce756236dcef93e82001cfd08f1a0ed5f22e36cbbd3a87ebc57d"
    ; genomicSequenceCount =
        1870
    ; genomicTotalBases =
        143726002
    ; cdsFASTASHA256 =
        "3f379cec1d952f9a1c22e2b6dd9ff8eefce6da97ffb198cde93dc0a17c40da01"
    ; cdsSequenceCount =
        30802
    ; cdsTotalBases =
        61229245
    ; totalACGTCodons =
        20409720
    ; distinctACGTCodons =
        64
    ; maxCodon =
        "GAG"
    ; maxCodonCount =
        867771
    ; minNonzeroCodon =
        "TGA"
    ; minNonzeroCodonCount =
        8978
    ; codonNonuniformWitness =
        true
    ; acceptedAuthorityRouteCandidate =
        true
    ; checksumBoundSelectionCandidate =
        true
    ; fastaChecksumBound =
        true
    ; cdsCodonWitnessBound =
        true
    ; constructsCalibrationLaw =
        false
    ; constructsCandidate256PhysicalCalibrationAuthorityToken =
        false
    ; constructsCandidate256PhysicalCalibrationExternalReceipt =
        false
    ; constructsBrainAtomicChemistryHandoffProof =
        false
    ; promotesW4 =
        false
    ; promotesBrainLane =
        false
    ; promotesPhysicsLane =
        false
    ; claimsUnification =
        false
    ; artifactPacket =
        "scripts/data/genome/drosophila_release6_authority_packet.json"
    ; boundary =
        "This packet binds the public Drosophila Release 6 authority route and local FASTA checksums"
        ∷ "The CDS codon-frequency witness is non-uniform and checksum-bound"
        ∷ "The prior DOI 10.1126/science.1237175 is explicitly rejected for this authority route"
        ∷ "This receipt does not prove a TSFV-compatible calibration law"
        ∷ "This receipt does not construct Candidate256PhysicalCalibrationAuthorityToken"
        ∷ "This receipt does not inhabit Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "This receipt does not connect codon statistics to BrainAtomicChemistryHandoffProfile"
        ∷ "No W4, Brain, physics, biological-recovery, or unification promotion is claimed"
        ∷ []
    }
