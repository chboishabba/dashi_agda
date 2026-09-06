module DASHI.Biology.DrosophilaGautheyAtlasRegistrationSourceBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Public-code boundary for the Gauthey local-atlas registration route.
--
-- Scientific source:
-- Wayan Gauthey; Albert Lin; Osama M. Ahmed; Andrew M. Leifer; Mala Murthy;
-- Stephan Y. Thiberge, "High-speed whole-brain imaging in Drosophila",
-- DOI 10.1038/s41467-026-72437-1;
-- analysis code github:murthylab/lightbead-analysis.
--
-- The public repository README declares ANTsPy for the signal-extraction
-- pipeline and contains batch_tiff_to_local_atlas_AL.sh. That launcher invokes
-- tiff_to_local_atlas.py, but the audited public repository does not provide
-- the referenced implementation. Therefore launcher presence is not an
-- executable transform receipt and does not close trial/anatomy -> atlas.
------------------------------------------------------------------------

record PublicAtlasSourceAudit : Set where
  constructor publicAtlasSourceAudit
  field
    repositoryIdentifier : String
    launcherIdentifier : String
    referencedImplementationIdentifier : String
    launcherPresent : Bool
    referencedImplementationPresent : Bool
    antsPyDependencyDeclared : Bool
    executableTransformReceiptOwned : Bool
    externalRegistrationPaymentRequired : Bool

open PublicAtlasSourceAudit public

canonicalPublicAtlasSourceAudit : PublicAtlasSourceAudit
canonicalPublicAtlasSourceAudit =
  publicAtlasSourceAudit
    "github:murthylab/lightbead-analysis"
    "dellaserver_processing/batch_tiff_to_local_atlas_AL.sh"
    "dellaserver_processing/tiff_to_local_atlas.py"
    true
    false
    true
    false
    true

record AtlasRegistrationSourceBoundary : Set where
  constructor atlasRegistrationSourceBoundary
  field
    launcherDoesNotImplyImplementation : Bool
    dependencyDeclarationDoesNotImplyExecutedTransform : Bool
    referencedScriptNameDoesNotImplyRecoverableTransformArtifact : Bool
    registrationMethodDoesNotImplySameObjectRegistration : Bool
    atlasRegistrationDoesNotImplyMaleCNSNeuronIdentity : Bool

open AtlasRegistrationSourceBoundary public

canonicalAtlasRegistrationSourceBoundary : AtlasRegistrationSourceBoundary
canonicalAtlasRegistrationSourceBoundary =
  atlasRegistrationSourceBoundary true true true true true

paymentBProducerKind : String
paymentBProducerKind =
  "external trial/anatomical-image -> atlas transform receipt with fixed/moving image provenance and registration residual"
