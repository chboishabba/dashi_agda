module DASHI.Physics.Chemistry.AmmoniaSCIReleasedArtifactExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- AUTHOR-RELEASED NH3 COMPUTATIONAL ARTIFACT
--
-- The associated paper points to github.com/danieli4444/SCI_VQE as its open
-- data/code repository. The repository contains a concrete 64x64 NH3
-- selected-CI matrix plus run JSON. These are an author-released data carrier,
-- not independent scientific authority and not DASHI authorship.
--
-- The released CI_result geometry/energy and the final paper's tabulated
-- benchmark are numerically different, so they remain distinct computational
-- objects under the repo's same-object attribution rule.
------------------------------------------------------------------------

authorReleasedSCIVQERepository : Source.AttributedSource
authorReleasedSCIVQERepository =
  Source.mkNoDOISource
    "Daniel Yoffe; Noga Entin; Amir Natan; Adi Makmal"
    "SCI_VQE author-released code and data repository"
    "Research artifact linked by the data/code availability statement of Quantum Science and Technology 10 (2025) 015020"
    "2024"
    "https://github.com/danieli4444/SCI_VQE"
    (Source.namedSourceKind "author-released research code/data repository")
    "access/data carrier for the authors' released NH3 geometry, CI-result metadata and selected-CI matrices; not independent scientific authority and not DASHI authorship"
    Source.publicAttribution

record ReleasedSelectedCIArtifact : Set where
  constructor releasedSelectedCIArtifact
  field
    molecule : String
    basis : String
    artifactPath : String
    gitBlobSHA : String
    byteSize : Nat
    matrixDimension : Nat
    selectedGroundEnergySign : String
    selectedGroundEnergyNanoHartreeMagnitude : Nat
    energySourcePath : String
    energySourceBlobSHA : String
    repositorySource : Source.AttributedSource
    interpretation : String

open ReleasedSelectedCIArtifact public

nh3SelectedCI64Artifact : ReleasedSelectedCIArtifact
nh3SelectedCI64Artifact =
  releasedSelectedCIArtifact
    "NH3"
    "STO-3G"
    "NH3/CI_matrices/NH3_cimat__64.out"
    "07541705a0305e75dab1de5bc1b8324d66fee778"
    103176
    64
    "negative Hartree total-energy value"
    55517555010
    "NH3/NH3_Fri Sep 30 02:42:39 2022.json"
    "b5560bfc019289512fcf1498b12d9f07a57e1972"
    authorReleasedSCIVQERepository
    "the JSON exact_energy_list entry at 64 configurations is -55.517555009641335 Ha; stored integer is rounded |E| in nanoHartree units (55.517555010 Ha); the matrix file is the corresponding released 64x64 selected-CI Hamiltonian artifact"

record ReleasedFCIRunMetadata : Set where
  constructor releasedFCIRunMetadata
  field
    metadataPath : String
    gitBlobSHA : String
    basis : String
    configurationCount : Nat
    groundEnergySign : String
    groundEnergyNanoHartreeMagnitude : Nat
    nuclearRepulsionNanoHartree : Nat
    geometry : String
    repositorySource : Source.AttributedSource

open ReleasedFCIRunMetadata public

nh3ReleasedFCIRunMetadata : ReleasedFCIRunMetadata
nh3ReleasedFCIRunMetadata =
  releasedFCIRunMetadata
    "NH3/CI_result.json"
    "0a9f5e54ea5d790c6dff110090e34d498a7a1607"
    "STO-3G"
    3136
    "negative Hartree total-energy value"
    55519414318
    11939959419
    "N (0,0,0.2851841); H (-0.4697490,0.8136292,-0.0950614); H (-0.4697490,-0.8136292,-0.0950614); H (0.9394980,0,-0.0950614); symmetry c1"
    authorReleasedSCIVQERepository

record ReleasedArtifactBoundary : Set where
  constructor releasedArtifactBoundary
  field
    authorReleasedMatrixIdentityPaid : Bool
    authorReleasedMatrixIdentityPaidIsTrue : authorReleasedMatrixIdentityPaid ≡ true
    authorReleasedRunGeometryPaid : Bool
    authorReleasedRunGeometryPaidIsTrue : authorReleasedRunGeometryPaid ≡ true
    authorReleasedSelectedEnergyPaid : Bool
    authorReleasedSelectedEnergyPaidIsTrue : authorReleasedSelectedEnergyPaid ≡ true
    authorReleasedFCIRunEnergyPaid : Bool
    authorReleasedFCIRunEnergyPaidIsTrue : authorReleasedFCIRunEnergyPaid ≡ true
    paperBenchmarkAndArtifactAreSameNumericalObject : Bool
    paperBenchmarkAndArtifactAreSameNumericalObjectIsFalse : paperBenchmarkAndArtifactAreSameNumericalObject ≡ false
    matrixBytesVendoredIntoDASHI : Bool
    matrixBytesVendoredIntoDASHIIsFalse : matrixBytesVendoredIntoDASHI ≡ false
    matrixIndependentlyRediagonalizedByDASHI : Bool
    matrixIndependentlyRediagonalizedByDASHIIsFalse : matrixIndependentlyRediagonalizedByDASHI ≡ false
    releasedRepositoryCreatesIndependentAuthority : Bool
    releasedRepositoryCreatesIndependentAuthorityIsFalse : releasedRepositoryCreatesIndependentAuthority ≡ false

open ReleasedArtifactBoundary public

canonicalReleasedArtifactBoundary : ReleasedArtifactBoundary
canonicalReleasedArtifactBoundary =
  releasedArtifactBoundary true refl true refl true refl true refl false refl false refl false refl false refl
