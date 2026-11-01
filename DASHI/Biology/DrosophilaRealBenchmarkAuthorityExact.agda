module DASHI.Biology.DrosophilaRealBenchmarkAuthorityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Real-data benchmark authority: repository identity, exact artifact identity,
-- digest verification, biological resolution, and consumer promotion remain
-- separate coordinates.
------------------------------------------------------------------------

data ArtifactVerificationLevel : Set where
  missing : ArtifactVerificationLevel
  present : ArtifactVerificationLevel
  digested : ArtifactVerificationLevel
  hashVerified : ArtifactVerificationLevel

data BenchmarkResolution : Set where
  neuronIdentityResolution : BenchmarkResolution
  cellTypeResolution : BenchmarkResolution
  regionNeuropilResolution : BenchmarkResolution
  motorModuleResolution : BenchmarkResolution

data BenchmarkConsumer : Set where
  structureFunctionConsumer : BenchmarkConsumer
  effectorConsumer : BenchmarkConsumer
  behaviourConsumer : BenchmarkConsumer
  semanticConsumer : BenchmarkConsumer

data NullControl : Set where
  degreePreservingRewire : NullControl
  registrationPermutation : NullControl
  spatialOrNeuropilMatched : NullControl
  directEdgeBaseline : NullControl
  pathAwareBaseline : NullControl

record ArtifactAuthority : Set where
  field
    artifactKey : String
    scientificAuthorOrConsortium : String
    scientificTitle : String
    scientificStableIdentifier : String
    repositoryStableIdentifier : String
    resolvedFilename : String
    expectedSHA256 : String
    directDownloadResolved : Bool

open ArtifactAuthority public

record RealBenchmarkReceipt : Set₁ where
  field
    Artifact : Set
    consumer : BenchmarkConsumer
    requiredArtifacts : List Artifact
    verificationLevel : Artifact → ArtifactVerificationLevel
    resolution : BenchmarkResolution
    heldOutSplitVerified : Bool
    registrationResidualVerified : Bool
    outputReceiptVerified : Bool
    nullControls : List NullControl
    consumerActive : Bool

open RealBenchmarkReceipt public

record RealBenchmarkBoundary : Set where
  constructor realBenchmarkBoundary
  field
    doiLandingPageIsNotArtifactFile : Bool
    filePresenceIsNotHashVerification : Bool
    repositoryDigestIsNotExpectedDigest : Bool
    sameRegionDoesNotImplySameNeuron : Bool
    crossAnimalMotorAtlasDoesNotImplySameAnimalIdentity : Bool
    regionBenchmarkMayPrecedeNeuronBenchmark : Bool
    nullControlsRequiredForComparativeClaim : Bool
    biologicalHoldoutPreferredToOrdinalSplit : Bool
    semanticConsumerPresentButInactive : Bool
    mockExecutionDoesNotPromoteEmpiricalClaim : Bool

canonicalRealBenchmarkBoundary : RealBenchmarkBoundary
canonicalRealBenchmarkBoundary =
  realBenchmarkBoundary true true true true true true true true true true

------------------------------------------------------------------------
-- Explicit scientific provenance used by this tranche.
------------------------------------------------------------------------

record ScientificSourceReading : Set where
  constructor sourceReading
  field
    authorOrConsortium : String
    title : String
    stableIdentifier : String
    boundedReading : String

open ScientificSourceReading public

gauthey2026 : ScientificSourceReading
gauthey2026 = sourceReading
  "Wayan Gauthey; Albert Lin; Osama M. Ahmed; Andrew M. Leifer; Mala Murthy; Stephan Y. Thiberge"
  "High-speed whole-brain imaging in Drosophila"
  "doi:10.1038/s41467-026-72437-1; data:doi:10.5281/zenodo.17618684"
  "functional and synchronized behavioural producer; observation does not equal latent neural state"

bifrost2024 : ScientificSourceReading
bifrost2024 = sourceReading
  "Bella E. Brezovec; Andrew B. Berger; Yukun A. Hao; Albert Lin; Osama M. Ahmed; Diego A. Pacheco; Stephan Y. Thiberge; Mala Murthy; Thomas R. Clandinin"
  "BIFROST: A method for registering diverse imaging datasets of the Drosophila brain"
  "doi:10.1073/pnas.2322687121; data:doi:10.5061/dryad.8pk0p2nx1; data:doi:10.5281/zenodo.11097259"
  "registration producer; region or coordinate correspondence is not direct neuron identity"

azevedo2024 : ScientificSourceReading
azevedo2024 = sourceReading
  "Anthony Azevedo; Ellen Lesser; Jasper S. Phelps; Brandon Mark et al."
  "Connectomic reconstruction of a female Drosophila ventral nerve cord"
  "doi:10.1038/s41586-024-07389-x"
  "motor-neuron-to-muscle atlas producer; female cross-animal mapping does not imply MaleCNS same-animal identity"

record ScientificSourceBoundary : Set where
  constructor scientificSourceBoundary
  field
    sourceIdentityDoesNotImportTheorem : Bool
    paperDOIDoesNotResolveDatasetFile : Bool
    methodProvenanceDistinctFromDatasetProvenance : Bool

canonicalScientificSourceBoundary : ScientificSourceBoundary
canonicalScientificSourceBoundary = scientificSourceBoundary true true true
