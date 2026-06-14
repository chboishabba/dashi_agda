module DASHI.Physics.Closure.AgdaPhysicsParityRoadmapReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Agda/PhysLean parity roadmap receipt.
--
-- This module is intentionally standalone.  Parallel workers may still be
-- adding the concrete layer modules, so the composition below records layer
-- and interface names as strings instead of importing unstable neighbours.
-- It is a checked receipt for roadmap ergonomics: naming, reusable theorem
-- APIs, example rows, automation/search affordances, package governance, and
-- explicit non-promotion until an external authority token exists.

data ⊥ : Set where

modulePath : String
modulePath =
  "DASHI/Physics/Closure/AgdaPhysicsParityRoadmapReceipt.agda"

roadmapName : String
roadmapName =
  "Agda physics parity with PhysLean theorem ergonomics roadmap"

roadmapRound : Nat
roadmapRound = 6

workerLane : String
workerLane = "worker-6-theorem-ergonomics-parity-roadmap"

data ParityLayer : Set where
  infrastructureLayer :
    ParityLayer
  domainLibraryLayer :
    ParityLayer
  theoremErgonomicsLayer :
    ParityLayer
  examplesRegressionLayer :
    ParityLayer
  automationSearchLayer :
    ParityLayer
  packageRoadmapGovernanceLayer :
    ParityLayer

canonicalParityLayers : List ParityLayer
canonicalParityLayers =
  infrastructureLayer
  ∷ domainLibraryLayer
  ∷ theoremErgonomicsLayer
  ∷ examplesRegressionLayer
  ∷ automationSearchLayer
  ∷ packageRoadmapGovernanceLayer
  ∷ []

data LayerStatus : Set where
  presentAsNamedInterface :
    LayerStatus
  recordedAsRoadmapTarget :
    LayerStatus
  blockedPendingAuthority :
    LayerStatus

data EvidenceMode : Set where
  checkedLocalReceipt :
    EvidenceMode
  stringNamedInterface :
    EvidenceMode
  futureModuleBoundary :
    EvidenceMode

data PromotionVerdict : Set where
  notPromoted :
    PromotionVerdict
  authorityRequired :
    PromotionVerdict

data ErgonomicFacet : Set where
  coherentNames :
    ErgonomicFacet
  reusableTheoremAPI :
    ErgonomicFacet
  examplesAndRegressionRows :
    ErgonomicFacet
  tacticOrAutomationAnalogue :
    ErgonomicFacet
  searchAndNavigationIndex :
    ErgonomicFacet
  packageLevelRoadmap :
    ErgonomicFacet

canonicalErgonomicFacets : List ErgonomicFacet
canonicalErgonomicFacets =
  coherentNames
  ∷ reusableTheoremAPI
  ∷ examplesAndRegressionRows
  ∷ tacticOrAutomationAnalogue
  ∷ searchAndNavigationIndex
  ∷ packageLevelRoadmap
  ∷ []

record LayerReceipt : Set where
  constructor mkLayerReceipt
  field
    layer :
      ParityLayer
    layerCode :
      String
    interfaceName :
      String
    physLeanAnalogue :
      String
    dashiSurface :
      String
    status :
      LayerStatus
    evidenceMode :
      EvidenceMode
    interfaceNamed :
      Bool
    interfaceNamedIsTrue :
      interfaceNamed ≡ true
    moduleImported :
      Bool
    moduleImportedIsFalse :
      moduleImported ≡ false
    verifiedByThisModule :
      Bool
    verifiedByThisModuleIsTrue :
      verifiedByThisModule ≡ true
    promoted :
      Bool
    promotedIsFalse :
      promoted ≡ false
    verdict :
      PromotionVerdict
    nextAction :
      String

infrastructureReceipt : LayerReceipt
infrastructureReceipt =
  mkLayerReceipt
    infrastructureLayer
    "L1-infrastructure"
    "AgdaPhysicsInfrastructureSurface"
    "mathlib/import/build/search infrastructure"
    "DASHI foundation imports, primitive receipt vocabulary, check target"
    presentAsNamedInterface
    stringNamedInterface
    true
    refl
    false
    refl
    true
    refl
    false
    refl
    notPromoted
    "Keep import-light receipts checkable while integration modules stabilize."

domainLibraryReceipt : LayerReceipt
domainLibraryReceipt =
  mkLayerReceipt
    domainLibraryLayer
    "L2-domain-library"
    "AgdaPhysicsDomainLibrarySurface"
    "PhysLean physics structures and theorem namespaces"
    "DASHI Physics/Closure named theorem and boundary modules"
    recordedAsRoadmapTarget
    stringNamedInterface
    true
    refl
    false
    refl
    true
    refl
    false
    refl
    notPromoted
    "Index domain surfaces by stable interface names before depending on modules."

theoremErgonomicsReceipt : LayerReceipt
theoremErgonomicsReceipt =
  mkLayerReceipt
    theoremErgonomicsLayer
    "L3-theorem-ergonomics"
    "AgdaPhysicsTheoremErgonomicsAPI"
    "coherent theorem names, reusable lemmas, theorem search affordances"
    "canonical receipt rows for naming, API reuse, examples, and obligations"
    presentAsNamedInterface
    checkedLocalReceipt
    true
    refl
    false
    refl
    true
    refl
    false
    refl
    notPromoted
    "Expose reusable theorem-shape rows rather than one-off sprint claims."

examplesRegressionReceipt : LayerReceipt
examplesRegressionReceipt =
  mkLayerReceipt
    examplesRegressionLayer
    "L4-examples-regression"
    "AgdaPhysicsExamplesRegressionSurface"
    "examples, tests, and small canonical instances"
    "receipt-level example obligations and regression names"
    recordedAsRoadmapTarget
    futureModuleBoundary
    true
    refl
    false
    refl
    true
    refl
    false
    refl
    notPromoted
    "Attach concrete examples only after their provider modules are stable."

automationSearchReceipt : LayerReceipt
automationSearchReceipt =
  mkLayerReceipt
    automationSearchLayer
    "L5-automation-search"
    "AgdaPhysicsAutomationSearchNavigationSurface"
    "simp/tactic/search/navigation equivalents where possible"
    "normalized names, search keys, rewrite candidates, and navigation tags"
    recordedAsRoadmapTarget
    stringNamedInterface
    true
    refl
    false
    refl
    true
    refl
    false
    refl
    notPromoted
    "Record automation candidates without claiming unavailable tactics."

packageRoadmapGovernanceReceipt : LayerReceipt
packageRoadmapGovernanceReceipt =
  mkLayerReceipt
    packageRoadmapGovernanceLayer
    "L6-package-roadmap-governance"
    "AgdaPhysicsPackageRoadmapGovernanceSurface"
    "package-level roadmap, maintainership, and promotion governance"
    "non-promoting authority boundary and integration checklist"
    blockedPendingAuthority
    checkedLocalReceipt
    true
    refl
    false
    refl
    true
    refl
    false
    refl
    authorityRequired
    "Require explicit authority before any parity-complete or physics promotion claim."

canonicalLayerReceipts : List LayerReceipt
canonicalLayerReceipts =
  infrastructureReceipt
  ∷ domainLibraryReceipt
  ∷ theoremErgonomicsReceipt
  ∷ examplesRegressionReceipt
  ∷ automationSearchReceipt
  ∷ packageRoadmapGovernanceReceipt
  ∷ []

record TheoremAPIShape : Set where
  constructor mkTheoremAPIShape
  field
    facet :
      ErgonomicFacet
    apiName :
      String
    requiredShape :
      String
    reusable :
      Bool
    reusableIsTrue :
      reusable ≡ true
    localExampleRequired :
      Bool
    automationClaimed :
      Bool
    automationClaimedIsFalse :
      automationClaimed ≡ false
    promotionClaimed :
      Bool
    promotionClaimedIsFalse :
      promotionClaimed ≡ false

namePolicyAPI : TheoremAPIShape
namePolicyAPI =
  mkTheoremAPIShape
    coherentNames
    "AgdaPhysicsNamePolicy"
    "module path, theorem noun, boundary status, and receipt suffix are explicit"
    true
    refl
    true
    false
    refl
    false
    refl

reusableTheoremSurfaceAPI : TheoremAPIShape
reusableTheoremSurfaceAPI =
  mkTheoremAPIShape
    reusableTheoremAPI
    "AgdaPhysicsReusableTheoremSurface"
    "records expose fields that downstream receipts can project and prove equal"
    true
    refl
    true
    false
    refl
    false
    refl

exampleRegressionAPI : TheoremAPIShape
exampleRegressionAPI =
  mkTheoremAPIShape
    examplesAndRegressionRows
    "AgdaPhysicsExampleRegressionRows"
    "examples are named as obligations until concrete checked providers exist"
    true
    refl
    true
    false
    refl
    false
    refl

automationAnalogueAPI : TheoremAPIShape
automationAnalogueAPI =
  mkTheoremAPIShape
    tacticOrAutomationAnalogue
    "AgdaPhysicsAutomationAnalogue"
    "rewrite/search/tactic candidates are listed, not asserted as available"
    true
    refl
    false
    false
    refl
    false
    refl

searchNavigationAPI : TheoremAPIShape
searchNavigationAPI =
  mkTheoremAPIShape
    searchAndNavigationIndex
    "AgdaPhysicsSearchNavigationIndex"
    "stable strings connect concepts to modules without importing race targets"
    true
    refl
    false
    false
    refl
    false
    refl

packageRoadmapAPI : TheoremAPIShape
packageRoadmapAPI =
  mkTheoremAPIShape
    packageLevelRoadmap
    "AgdaPhysicsPackageRoadmap"
    "layer receipts compose into one canonical non-promoting roadmap receipt"
    true
    refl
    false
    false
    refl
    false
    refl

canonicalTheoremAPIShapes : List TheoremAPIShape
canonicalTheoremAPIShapes =
  namePolicyAPI
  ∷ reusableTheoremSurfaceAPI
  ∷ exampleRegressionAPI
  ∷ automationAnalogueAPI
  ∷ searchNavigationAPI
  ∷ packageRoadmapAPI
  ∷ []

record SearchNavigationKey : Set where
  constructor mkSearchNavigationKey
  field
    key :
      String
    layer :
      ParityLayer
    facet :
      ErgonomicFacet
    targetInterface :
      String
    importSafeNow :
      Bool
    importSafeNowIsFalse :
      importSafeNow ≡ false
    searchRecorded :
      Bool
    searchRecordedIsTrue :
      searchRecorded ≡ true

canonicalSearchKeys : List SearchNavigationKey
canonicalSearchKeys =
  mkSearchNavigationKey
    "parity:infrastructure:receipt-vocabulary"
    infrastructureLayer
    coherentNames
    "AgdaPhysicsInfrastructureSurface"
    false
    refl
    true
    refl
  ∷ mkSearchNavigationKey
    "parity:domain:physics-closure"
    domainLibraryLayer
    reusableTheoremAPI
    "AgdaPhysicsDomainLibrarySurface"
    false
    refl
    true
    refl
  ∷ mkSearchNavigationKey
    "parity:ergonomics:theorem-api"
    theoremErgonomicsLayer
    reusableTheoremAPI
    "AgdaPhysicsTheoremErgonomicsAPI"
    false
    refl
    true
    refl
  ∷ mkSearchNavigationKey
    "parity:examples:regression"
    examplesRegressionLayer
    examplesAndRegressionRows
    "AgdaPhysicsExamplesRegressionSurface"
    false
    refl
    true
    refl
  ∷ mkSearchNavigationKey
    "parity:automation:search-navigation"
    automationSearchLayer
    searchAndNavigationIndex
    "AgdaPhysicsAutomationSearchNavigationSurface"
    false
    refl
    true
    refl
  ∷ mkSearchNavigationKey
    "parity:governance:no-promotion"
    packageRoadmapGovernanceLayer
    packageLevelRoadmap
    "AgdaPhysicsPackageRoadmapGovernanceSurface"
    false
    refl
    true
    refl
  ∷ []

data ParityPromotionAuthorityToken : Set where

parityPromotionImpossibleHere :
  ParityPromotionAuthorityToken →
  ⊥
parityPromotionImpossibleHere ()

record AgdaPhysicsParityRoadmapReceipt : Set where
  constructor mkAgdaPhysicsParityRoadmapReceipt
  field
    receiptModulePath :
      String
    receiptName :
      String
    receiptWorkerLane :
      String
    layers :
      List ParityLayer
    layersAreCanonical :
      layers ≡ canonicalParityLayers
    layerReceipts :
      List LayerReceipt
    layerReceiptsAreCanonical :
      layerReceipts ≡ canonicalLayerReceipts
    theoremFacets :
      List ErgonomicFacet
    theoremFacetsAreCanonical :
      theoremFacets ≡ canonicalErgonomicFacets
    theoremAPIs :
      List TheoremAPIShape
    theoremAPIsAreCanonical :
      theoremAPIs ≡ canonicalTheoremAPIShapes
    searchKeys :
      List SearchNavigationKey
    searchKeysAreCanonical :
      searchKeys ≡ canonicalSearchKeys
    sixLayerCompositionRecorded :
      Bool
    sixLayerCompositionRecordedIsTrue :
      sixLayerCompositionRecorded ≡ true
    dependsOnConcurrentWorkerModules :
      Bool
    dependsOnConcurrentWorkerModulesIsFalse :
      dependsOnConcurrentWorkerModules ≡ false
    aggregateImportsEdited :
      Bool
    aggregateImportsEditedIsFalse :
      aggregateImportsEdited ≡ false
    grPDEParityBoundaryEdited :
      Bool
    grPDEParityBoundaryEditedIsFalse :
      grPDEParityBoundaryEdited ≡ false
    explicitTrueFalseFieldsPresent :
      Bool
    explicitTrueFalseFieldsPresentIsTrue :
      explicitTrueFalseFieldsPresent ≡ true
    physLeanParityCompleteClaimed :
      Bool
    physLeanParityCompleteClaimedIsFalse :
      physLeanParityCompleteClaimed ≡ false
    physicsTheoremPromotionClaimed :
      Bool
    physicsTheoremPromotionClaimedIsFalse :
      physicsTheoremPromotionClaimed ≡ false
    authorityTokenPresent :
      Bool
    authorityTokenPresentIsFalse :
      authorityTokenPresent ≡ false
    promotionVerdict :
      PromotionVerdict
    packageRoadmapSummary :
      String

canonicalAgdaPhysicsParityRoadmapReceipt :
  AgdaPhysicsParityRoadmapReceipt
canonicalAgdaPhysicsParityRoadmapReceipt =
  mkAgdaPhysicsParityRoadmapReceipt
    modulePath
    roadmapName
    workerLane
    canonicalParityLayers
    refl
    canonicalLayerReceipts
    refl
    canonicalErgonomicFacets
    refl
    canonicalTheoremAPIShapes
    refl
    canonicalSearchKeys
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    authorityRequired
    "Six Agda physics parity layers are recorded as checked, import-safe roadmap interfaces; theorem ergonomics are reusable receipt rows; no PhysLean parity-complete or physics promotion claim is made without authority."

canonicalReceiptNoConcurrentDependencies :
  AgdaPhysicsParityRoadmapReceipt.dependsOnConcurrentWorkerModules
    canonicalAgdaPhysicsParityRoadmapReceipt
  ≡
  false
canonicalReceiptNoConcurrentDependencies = refl

canonicalReceiptNoAggregateImportEdit :
  AgdaPhysicsParityRoadmapReceipt.aggregateImportsEdited
    canonicalAgdaPhysicsParityRoadmapReceipt
  ≡
  false
canonicalReceiptNoAggregateImportEdit = refl

canonicalReceiptNoGRPDEBoundaryEdit :
  AgdaPhysicsParityRoadmapReceipt.grPDEParityBoundaryEdited
    canonicalAgdaPhysicsParityRoadmapReceipt
  ≡
  false
canonicalReceiptNoGRPDEBoundaryEdit = refl

canonicalReceiptNoPhysLeanParityPromotion :
  AgdaPhysicsParityRoadmapReceipt.physLeanParityCompleteClaimed
    canonicalAgdaPhysicsParityRoadmapReceipt
  ≡
  false
canonicalReceiptNoPhysLeanParityPromotion = refl

canonicalReceiptNoPhysicsTheoremPromotion :
  AgdaPhysicsParityRoadmapReceipt.physicsTheoremPromotionClaimed
    canonicalAgdaPhysicsParityRoadmapReceipt
  ≡
  false
canonicalReceiptNoPhysicsTheoremPromotion = refl

canonicalReceiptHasSixLayerRecord :
  AgdaPhysicsParityRoadmapReceipt.sixLayerCompositionRecorded
    canonicalAgdaPhysicsParityRoadmapReceipt
  ≡
  true
canonicalReceiptHasSixLayerRecord = refl
