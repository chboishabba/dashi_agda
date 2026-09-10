module DASHI.ComputerScience.GodelCoquandT4ExternalImportRoadmapReceiptExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- COQUAND T4 EXTERNAL IMPORT ROADMAP
--
-- This mirrors DASHI's existing external-formal-import governance: locating a
-- machine-checked theorem on GitHub does not make it a local Agda dependency.
-- Promotion requires an exact source revision, lawful dependency intake,
-- compatibility/typecheck, the adapter payment, and then a local theorem
-- receipt on the imported carrier.
------------------------------------------------------------------------

data T4ImportStatus : Set where
  externalSourceVerified
  revisionPinned
  licenseIntakeOpen
  localDependencyPresent
  adapterTypechecked
  theoremPaymentsTypechecked
  importedAndKernelChecked : T4ImportStatus

record CoquandT4ExternalImportReceipt : Set where
  constructor coquandT4ExternalImportReceipt
  field
    sourceRepository : String
    sourceRevision : String
    sourceRevisionDate : String
    sourceLanguage : String
    sourceSafeDisciplineObserved : Bool
    sourceNoPostulatesClaimObserved : Bool
    minimumAgdaVersion : String
    sourceCheckedAgdaVersions : String
    repositoryLicenseMetadataPresent : Bool
    repositoryLicenseFileLocated : Bool
    licenseIntakeResolved : Bool
    localDependencyPresent : Bool
    externalArithmeticSourceInhabited : Bool
    externalSubstitutionPaymentInhabited : Bool
    externalDiagonalPaymentInhabited : Bool
    externalProvabilityPaymentInhabited : Bool
    localKernelReplayObserved : Bool
    status : T4ImportStatus
    nextExecutableSteps : List String

open CoquandT4ExternalImportReceipt public

canonicalCoquandT4ExternalImportReceipt : CoquandT4ExternalImportReceipt
canonicalCoquandT4ExternalImportReceipt =
  coquandT4ExternalImportReceipt
    "coquand/agda-godel-tree"
    "5475628ea4b648f956dce4baee7d0273ba257730"
    "2026-07-12"
    "Agda"
    true
    true
    "2.7+"
    "2.7 and 2.9.0"
    false
    false
    false
    false
    false
    false
    false
    false
    false
    licenseIntakeOpen
    ("resolve upstream licensing/permission before copying or vendoring source"
     ∷ "make the exact pinned T4/BRA source available to the DASHI Agda toolchain without changing its source identities"
     ∷ "typecheck the pinned upstream headline modules under a compatible Agda environment"
     ∷ "inhabit the generic ExternalArithmeticSource and ExternalArithmetisedSubstitution payments from the actual imported T4 carrier"
     ∷ "inhabit the finished external diagonal and Loeb/Goedel-II payment records on that same carrier"
     ∷ "compile those payments through the existing DASHI adapter/result compilers"
     ∷ "obtain a local exact-head kernel receipt for the focused CS validation root"
     ∷ [])

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PublicRepositoryImpliesLicenseToVendor : Set where
data SourceSafeBuildImpliesLocalKernelReplay : Set where
data PinnedRevisionImpliesDependencyPresent : Set where
data ExternalTheoremImpliesPaymentInhabitant : Set where

publicDoesNotImplyVendoringPermission :
  PublicRepositoryImpliesLicenseToVendor → ⊥
publicDoesNotImplyVendoringPermission ()

sourceBuildDoesNotEqualLocalReplay :
  SourceSafeBuildImpliesLocalKernelReplay → ⊥
sourceBuildDoesNotEqualLocalReplay ()

pinDoesNotCreateDependency : PinnedRevisionImpliesDependencyPresent → ⊥
pinDoesNotCreateDependency ()

externalTheoremDoesNotCreatePayment :
  ExternalTheoremImpliesPaymentInhabitant → ⊥
externalTheoremDoesNotCreatePayment ()

record CoquandT4ImportBoundary : Set where
  constructor coquandT4ImportBoundary
  field
    exactRevisionPinned : Bool
    upstreamSafeDisciplineObserved : Bool
    upstreamLicenseResolved : Bool
    localDependencyAvailable : Bool
    mathematicalReproofIsCurrentBlocker : Bool
    dependencyIntakeIsCurrentBlocker : Bool
    localKernelReplayComplete : Bool

canonicalCoquandT4ImportBoundary : CoquandT4ImportBoundary
canonicalCoquandT4ImportBoundary =
  coquandT4ImportBoundary true true false false false true false
