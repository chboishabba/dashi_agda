module DASHI.Physics.Closure.HEPDataITIRAuthorityAdapterDiagnostic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataEmpiricalSourceCandidateDiagnostic as HEP

------------------------------------------------------------------------
-- HEP-F: ITIR provenance adapter diagnostic.
--
-- The sibling ITIR repo already has generic normalized-source/provenance
-- scaffolding.  This module records that fact without treating those generic
-- files as a HEPData-specific authority adapter, authority token, W3 receipt,
-- or projection theorem.

data ITIRNormalizedProvenanceScaffold : Set where
  normalizedSourcePython :
    ITIRNormalizedProvenanceScaffold
  sourceIdentityPython :
    ITIRNormalizedProvenanceScaffold
  suiteNormalizedArtifactPython :
    ITIRNormalizedProvenanceScaffold

canonicalITIRNormalizedProvenanceScaffold :
  List ITIRNormalizedProvenanceScaffold
canonicalITIRNormalizedProvenanceScaffold =
  normalizedSourcePython
  ∷ sourceIdentityPython
  ∷ suiteNormalizedArtifactPython
  ∷ []

canonicalITIRNormalizedProvenanceScaffoldPaths :
  List String
canonicalITIRNormalizedProvenanceScaffoldPaths =
  "../ITIR-suite/SensibLaw/src/sources/normalized_source.py"
  ∷ "../ITIR-suite/SensibLaw/src/reporting/source_identity.py"
  ∷ "../ITIR-suite/SensibLaw/src/policy/suite_normalized_artifact.py"
  ∷ []

data HEPDataITIRAuthorityAdapterStatus : Set where
  genericScaffoldPresentHEPDataAuthorityAdapterAbsent :
    HEPDataITIRAuthorityAdapterStatus

data HEPDataITIRAuthorityAdapterRequiredField : Set where
  rawHEPDataAuthorityIdentity :
    HEPDataITIRAuthorityAdapterRequiredField
  cachedArtifactChecksum :
    HEPDataITIRAuthorityAdapterRequiredField
  localNPZHash :
    HEPDataITIRAuthorityAdapterRequiredField
  sourceCitationTableIdentity :
    HEPDataITIRAuthorityAdapterRequiredField
  derivedProjectionBoundary :
    HEPDataITIRAuthorityAdapterRequiredField
  acceptedAuthorityHandoff :
    HEPDataITIRAuthorityAdapterRequiredField

canonicalHEPDataITIRAuthorityAdapterRequiredFields :
  List HEPDataITIRAuthorityAdapterRequiredField
canonicalHEPDataITIRAuthorityAdapterRequiredFields =
  rawHEPDataAuthorityIdentity
  ∷ cachedArtifactChecksum
  ∷ localNPZHash
  ∷ sourceCitationTableIdentity
  ∷ derivedProjectionBoundary
  ∷ acceptedAuthorityHandoff
  ∷ []

canonicalHEPDataITIRAuthorityAdapterRequiredFieldNames :
  List String
canonicalHEPDataITIRAuthorityAdapterRequiredFieldNames =
  "raw HEPData authority identity"
  ∷ "cached artifact checksum"
  ∷ "local NPZ hash"
  ∷ "source/citation/table identity"
  ∷ "derived-projection boundary"
  ∷ "accepted-authority handoff"
  ∷ []

data HEPDataITIRAuthorityAdapterMissingSurface : Set where
  missingHEPDataSpecificNormalizedSourceBinding :
    HEPDataITIRAuthorityAdapterMissingSurface
  missingHEPDataSpecificSourceIdentityBinding :
    HEPDataITIRAuthorityAdapterMissingSurface
  missingHEPDataSpecificSuiteArtifactBinding :
    HEPDataITIRAuthorityAdapterMissingSurface
  missingHEPDataAuthorityAdapterImplementation :
    HEPDataITIRAuthorityAdapterMissingSurface
  missingHEPDataAuthorityTokenSource :
    HEPDataITIRAuthorityAdapterMissingSurface
  missingAcceptedAuthorityReceiptHandoff :
    HEPDataITIRAuthorityAdapterMissingSurface

canonicalHEPDataITIRAuthorityAdapterMissingSurfaces :
  List HEPDataITIRAuthorityAdapterMissingSurface
canonicalHEPDataITIRAuthorityAdapterMissingSurfaces =
  missingHEPDataSpecificNormalizedSourceBinding
  ∷ missingHEPDataSpecificSourceIdentityBinding
  ∷ missingHEPDataSpecificSuiteArtifactBinding
  ∷ missingHEPDataAuthorityAdapterImplementation
  ∷ missingHEPDataAuthorityTokenSource
  ∷ missingAcceptedAuthorityReceiptHandoff
  ∷ []

record HEPDataITIRAuthorityAdapterDiagnostic : Setω where
  field
    sourceCandidateDiagnostic :
      HEP.HEPDataEmpiricalSourceCandidateDiagnostic

    sourceCandidatesStillNonPromoting :
      HEP.HEPDataEmpiricalSourceCandidateDiagnostic.candidateStatus
        sourceCandidateDiagnostic
      ≡
      HEP.sourceCandidatesPresentButNonPromoting

    itirScaffold :
      List ITIRNormalizedProvenanceScaffold

    itirScaffoldIsCanonical :
      itirScaffold ≡ canonicalITIRNormalizedProvenanceScaffold

    itirScaffoldPaths :
      List String

    itirScaffoldPathsAreCanonical :
      itirScaffoldPaths ≡ canonicalITIRNormalizedProvenanceScaffoldPaths

    adapterStatus :
      HEPDataITIRAuthorityAdapterStatus

    requiredAdapterFields :
      List HEPDataITIRAuthorityAdapterRequiredField

    requiredAdapterFieldsAreCanonical :
      requiredAdapterFields
      ≡
      canonicalHEPDataITIRAuthorityAdapterRequiredFields

    requiredAdapterFieldNames :
      List String

    requiredAdapterFieldNamesAreCanonical :
      requiredAdapterFieldNames
      ≡
      canonicalHEPDataITIRAuthorityAdapterRequiredFieldNames

    missingAdapterSurfaces :
      List HEPDataITIRAuthorityAdapterMissingSurface

    missingAdapterSurfacesAreCanonical :
      missingAdapterSurfaces
      ≡
      canonicalHEPDataITIRAuthorityAdapterMissingSurfaces

    absentHEPDataSpecificAuthoritySurfaces :
      List String

    acceptedAuthorityHandoffTarget :
      String

    derivedProjectionBoundaryText :
      String

    nonPromotionBoundary :
      List String

canonicalHEPDataITIRAuthorityAdapterDiagnostic :
  HEPDataITIRAuthorityAdapterDiagnostic
canonicalHEPDataITIRAuthorityAdapterDiagnostic =
  record
    { sourceCandidateDiagnostic =
        HEP.canonicalHEPDataEmpiricalSourceCandidateDiagnostic
    ; sourceCandidatesStillNonPromoting =
        refl
    ; itirScaffold =
        canonicalITIRNormalizedProvenanceScaffold
    ; itirScaffoldIsCanonical =
        refl
    ; itirScaffoldPaths =
        canonicalITIRNormalizedProvenanceScaffoldPaths
    ; itirScaffoldPathsAreCanonical =
        refl
    ; adapterStatus =
        genericScaffoldPresentHEPDataAuthorityAdapterAbsent
    ; requiredAdapterFields =
        canonicalHEPDataITIRAuthorityAdapterRequiredFields
    ; requiredAdapterFieldsAreCanonical =
        refl
    ; requiredAdapterFieldNames =
        canonicalHEPDataITIRAuthorityAdapterRequiredFieldNames
    ; requiredAdapterFieldNamesAreCanonical =
        refl
    ; missingAdapterSurfaces =
        canonicalHEPDataITIRAuthorityAdapterMissingSurfaces
    ; missingAdapterSurfacesAreCanonical =
        refl
    ; absentHEPDataSpecificAuthoritySurfaces =
        "HEPData-specific ITIR normalized-source adapter"
        ∷ "HEPData-specific source identity authority binding"
        ∷ "HEPData-specific suite normalized artifact authority binding"
        ∷ "HEPData-specific accepted-authority token source"
        ∷ []
    ; acceptedAuthorityHandoffTarget =
        "external W3 accepted-authority receipt route; not constructed by this HEP-F diagnostic"
    ; derivedProjectionBoundaryText =
        "Derived HEPData projections may be cached and identified, but they do not become theorem-side empirical authority without an accepted-authority handoff"
    ; nonPromotionBoundary =
        "normalized_source.py, source_identity.py, and suite_normalized_artifact.py are generic ITIR provenance scaffolding only"
        ∷ "No HEPData-specific ITIR authority adapter is present or constructed here"
        ∷ "No HEPData-specific accepted-authority token is present or constructed here"
        ∷ "The required adapter fields are named, but no field payload is supplied by this diagnostic"
        ∷ "This module does not promote W3 accepted empirical authority or any MeasurementSurface -> DashiState projection"
        ∷ []
    }
