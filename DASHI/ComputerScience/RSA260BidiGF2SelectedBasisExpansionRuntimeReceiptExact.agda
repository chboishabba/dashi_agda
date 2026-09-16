module DASHI.ComputerScience.RSA260BidiGF2SelectedBasisExpansionRuntimeReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiGF2SelectedBasisExpansionCertificateExact as Cert

------------------------------------------------------------------------
-- SELECTED-BASIS EXPANSION RUNTIME RECEIPT
--
-- A local certificate emitter now compares each factor packet's basis/mask
-- expansion against the independent pre-codec coefficient bytes rather than
-- against a row reconstructed from the same factor packet.
--
-- Discovery portfolio result:
--   10 generators
--   28 factor-mode coefficient layers
--   224 checked source rows
--   224/224 expansions equal the original pre-codec rows
--
-- This is still runtime evidence.  The generic proof-carrying verifier exists,
-- but these JSON certificates have not yet been compiled into Agda terms and
-- kernel-checked.  The producer's Gaussian-elimination/basis-search algorithm is
-- also deliberately not promoted to a theorem.
------------------------------------------------------------------------

certificateBoundary : Cert.GF2SelectedBasisExpansionCertificateBoundary
certificateBoundary = Cert.canonicalGF2SelectedBasisExpansionCertificateBoundary

record SelectedBasisExpansionRuntimeReceipt : Set where
  constructor selected-basis-expansion-runtime-receipt
  field
    runtimePath : String
    runtimeGitBlob : String
    runtimeSHA256 : String
    outputPath : String
    outputGitBlob : String
    outputSHA256 : String
    portfolioSize : Nat
    factorLayerCount : Nat
    checkedRowCount : Nat
    expectedRowsReadFromIndependentPrecodecReceipt : Bool
    everyFactorRowExpandsToOriginal : Bool
    exactLocalRuntimeExecuted : Bool
    runtimeCommittedToProducerRepository : Bool
open SelectedBasisExpansionRuntimeReceipt public

currentSelectedBasisExpansionRuntimeReceipt :
  SelectedBasisExpansionRuntimeReceipt
currentSelectedBasisExpansionRuntimeReceipt =
  selected-basis-expansion-runtime-receipt
    "/mnt/data/rsa260_selected_basis_expansion_certificates.py"
    "a1b89884e6cc05cdbbeba6b6484a97e9a7362b09"
    "fc160e58ad1407c48b3c1d07fd1b1b5fcbec3d0c83ac60c100b9a129f249164e"
    "/mnt/data/rsa260_selected_basis_expansion_certificates.json"
    "134c6e1fd78c7cd1ff778d69a929eb9bcedae037"
    "14b28c04086b14ff7548e1ce0738700152ca116fcfd7f677ed964557c0edc359"
    10
    28
    224
    true
    true
    true
    false

record SelectedBasisExpansionRuntimeBoundary : Set where
  constructor selected-basis-expansion-runtime-boundary
  field
    proofCarryingVerifierInherited : Bool
    independentPrecodecExpectedRowsUsed : Bool
    twentyEightFactorLayersChecked : Bool
    twoHundredTwentyFourRowsChecked : Bool
    allCheckedExpansionsMatchOriginalRows : Bool
    producerBasisSearchAlgorithmProved : Bool
    jsonCertificatesCompiledIntoAgdaTerms : Bool
    formalAgdaExpansionCertificatesKernelChecked : Bool
    packedByteWeldProved : Bool
    productionRSA260CustodyPaid : Bool
open SelectedBasisExpansionRuntimeBoundary public

canonicalSelectedBasisExpansionRuntimeBoundary :
  SelectedBasisExpansionRuntimeBoundary
canonicalSelectedBasisExpansionRuntimeBoundary =
  selected-basis-expansion-runtime-boundary
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- The Pareto frontier moves again.  Proving the coordinate-search algorithm is
-- no longer the shortest route to replay trust.  We have concrete expansion
-- witnesses; the next step is to compile/weld those witnesses to the formal
-- coordinate carrier so the Agda checker can discharge the equalities.
------------------------------------------------------------------------

data SelectedBasisExpansionRuntimeResidual : Set where
  compileRuntimeCertificatesIntoAgdaCoordinateTerms : SelectedBasisExpansionRuntimeResidual
  weldRuntimeBasisMaskBytesToFormalCoordinates : SelectedBasisExpansionRuntimeResidual
  kernelCheckFormalExpansionCertificates : SelectedBasisExpansionRuntimeResidual
  provePackedEightBitRowRepresentationExact : SelectedBasisExpansionRuntimeResidual
  compileCertifiedFactorPacketIntoHybridLayerCodec : SelectedBasisExpansionRuntimeResidual
  acquireSameObjectAStarOrFSols : SelectedBasisExpansionRuntimeResidual

firstSelectedBasisExpansionRuntimeResidual :
  SelectedBasisExpansionRuntimeResidual
firstSelectedBasisExpansionRuntimeResidual =
  compileRuntimeCertificatesIntoAgdaCoordinateTerms

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data RuntimeExpansionReceiptMeansFormalProof : Set where
data ExpansionMatchMeansBasisSearchAlgorithmProof : Set where
data SyntheticCertificateMeansProductionCustody : Set where

runtimeExpansionReceiptDoesNotCreateFormalProof :
  RuntimeExpansionReceiptMeansFormalProof → ⊥
runtimeExpansionReceiptDoesNotCreateFormalProof ()

expansionMatchDoesNotProveBasisSearchAlgorithm :
  ExpansionMatchMeansBasisSearchAlgorithmProof → ⊥
expansionMatchDoesNotProveBasisSearchAlgorithmProof ()

syntheticCertificateDoesNotCreateProductionCustody :
  SyntheticCertificateMeansProductionCustody → ⊥
syntheticCertificateDoesNotCreateProductionCustody ()
