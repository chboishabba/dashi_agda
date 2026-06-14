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
  authorityRequiredVerdict :
    PromotionVerdict

data ParityPromotionAuthorityToken : Set where

parityPromotionImpossibleHere :
  ParityPromotionAuthorityToken →
  ⊥
parityPromotionImpossibleHere ()

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

finiteYMSpectralTheoremStableInterfaceName : String
finiteYMSpectralTheoremStableInterfaceName =
  "finiteYMSpectralTheorem"

finiteYMSpectralTheoremInputs : List String
finiteYMSpectralTheoremInputs =
  "finite-dimensional Hilbert space"
  ∷ "ordered basis"
  ∷ "discrete YM Hamiltonian matrix"
  ∷ "finite gauge action"
  ∷ []

finiteYMSpectralTheoremOutputs : List String
finiteYMSpectralTheoremOutputs =
  "orthonormal eigenbasis"
  ∷ "real eigenvalue spectrum"
  ∷ "finite spectral decomposition"
  ∷ "gauge-compatible Hamiltonian receipt"
  ∷ []

finiteYMSpectralDefinitionalReflObligations : List String
finiteYMSpectralDefinitionalReflObligations =
  "dimension=length basis"
  ∷ "finite Jacobi check"
  ∷ "finite CCR matrix law"
  ∷ []

finiteYMSpectralExplicitProofObligations : List String
finiteYMSpectralExplicitProofObligations =
  "spanning"
  ∷ "linear independence"
  ∷ "Cauchy completeness"
  ∷ "spectral theorem"
  ∷ "gauge invariance"
  ∷ []

finiteYMSpectralTheoremProofObligationNames : List String
finiteYMSpectralTheoremProofObligationNames =
  "dimension=length basis"
  ∷ "finite Jacobi check"
  ∷ "finite CCR matrix law"
  ∷ "spanning"
  ∷ "linear independence"
  ∷ "Cauchy completeness"
  ∷ "spectral theorem"
  ∷ "gauge invariance"
  ∷ []

finiteYMSpectralNavigationKeys : List String
finiteYMSpectralNavigationKeys =
  "finite-YM"
  ∷ "spectral-theorem"
  ∷ "discrete-Hamiltonian"
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
    authorityRequiredVerdict
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
    stableInterfaceName :
      String
    inputs :
      List String
    outputs :
      List String
    proofObligationNames :
      List String
    authorityRequired :
      Bool
    authorityRequiredIsTrue :
      authorityRequired ≡ true
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
    "AgdaPhysicsNamePolicy"
    ("module path"
    ∷ "theorem noun"
    ∷ "boundary status"
    ∷ [])
    ("stable receipt name"
    ∷ "searchable interface name"
    ∷ [])
    ("coherent names"
    ∷ [])
    true
    refl
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
    "AgdaPhysicsReusableTheoremSurface"
    ("record fields"
    ∷ "projection names"
    ∷ [])
    ("downstream reusable theorem API"
    ∷ [])
    ("field projection equality"
    ∷ [])
    true
    refl
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
    "AgdaPhysicsExampleRegressionRows"
    ("example name"
    ∷ "regression import"
    ∷ [])
    ("canonical example receipt"
    ∷ [])
    ("example remains non-promoted"
    ∷ [])
    true
    refl
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
    "AgdaPhysicsAutomationAnalogue"
    ("obligation name"
    ∷ "automation class"
    ∷ [])
    ("definitional refl obligations"
    ∷ "explicit proof obligations"
    ∷ [])
    ("automation classification recorded"
    ∷ [])
    true
    refl
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
    "AgdaPhysicsSearchNavigationIndex"
    ("search key"
    ∷ "target interface"
    ∷ [])
    ("navigation index row"
    ∷ [])
    ("search key recorded"
    ∷ [])
    true
    refl
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
    "AgdaPhysicsPackageRoadmap"
    ("layer receipts"
    ∷ "authority boundary"
    ∷ [])
    ("non-promoting roadmap receipt"
    ∷ [])
    ("authority token required"
    ∷ [])
    true
    refl
    "layer receipts compose into one canonical non-promoting roadmap receipt"
    true
    refl
    false
    false
    refl
    false
    refl

finiteYMSpectralTheoremAPI : TheoremAPIShape
finiteYMSpectralTheoremAPI =
  mkTheoremAPIShape
    reusableTheoremAPI
    "FiniteYMSpectralTheoremAPI"
    finiteYMSpectralTheoremStableInterfaceName
    finiteYMSpectralTheoremInputs
    finiteYMSpectralTheoremOutputs
    finiteYMSpectralTheoremProofObligationNames
    true
    refl
    "finite-dimensional discrete Yang-Mills Hamiltonian spectral theorem API"
    true
    refl
    true
    false
    refl
    false
    refl

finiteYMSpectralTheoremAPIStableInterfaceNameIsExact :
  TheoremAPIShape.stableInterfaceName finiteYMSpectralTheoremAPI
  ≡
  finiteYMSpectralTheoremStableInterfaceName
finiteYMSpectralTheoremAPIStableInterfaceNameIsExact = refl

finiteYMSpectralTheoremAPIInputsAreExact :
  TheoremAPIShape.inputs finiteYMSpectralTheoremAPI
  ≡
  finiteYMSpectralTheoremInputs
finiteYMSpectralTheoremAPIInputsAreExact = refl

finiteYMSpectralTheoremAPIOutputsAreExact :
  TheoremAPIShape.outputs finiteYMSpectralTheoremAPI
  ≡
  finiteYMSpectralTheoremOutputs
finiteYMSpectralTheoremAPIOutputsAreExact = refl

finiteYMSpectralTheoremAPIProofObligationsAreExact :
  TheoremAPIShape.proofObligationNames finiteYMSpectralTheoremAPI
  ≡
  finiteYMSpectralTheoremProofObligationNames
finiteYMSpectralTheoremAPIProofObligationsAreExact = refl

finiteYMSpectralTheoremAPIAuthorityRequired :
  TheoremAPIShape.authorityRequired finiteYMSpectralTheoremAPI
  ≡
  true
finiteYMSpectralTheoremAPIAuthorityRequired = refl

canonicalTheoremAPIShapes : List TheoremAPIShape
canonicalTheoremAPIShapes =
  namePolicyAPI
  ∷ reusableTheoremSurfaceAPI
  ∷ finiteYMSpectralTheoremAPI
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
    keys :
      List String
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

finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKey :
  SearchNavigationKey
finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKey =
  mkSearchNavigationKey
    "parity:example:finite-dimensional-spectral-theorem:discrete-ym-hamiltonian"
    finiteYMSpectralNavigationKeys
    examplesRegressionLayer
    examplesAndRegressionRows
    "CanonicalParityExampleReceipt"
    false
    refl
    true
    refl

finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKeysAreExact :
  SearchNavigationKey.keys
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKey
  ≡
  finiteYMSpectralNavigationKeys
finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKeysAreExact =
  refl

canonicalSearchKeys : List SearchNavigationKey
canonicalSearchKeys =
  mkSearchNavigationKey
    "parity:infrastructure:receipt-vocabulary"
    ("receipt-vocabulary" ∷ [])
    infrastructureLayer
    coherentNames
    "AgdaPhysicsInfrastructureSurface"
    false
    refl
    true
    refl
  ∷ mkSearchNavigationKey
    "parity:domain:physics-closure"
    ("physics-closure" ∷ [])
    domainLibraryLayer
    reusableTheoremAPI
    "AgdaPhysicsDomainLibrarySurface"
    false
    refl
    true
    refl
  ∷ mkSearchNavigationKey
    "parity:ergonomics:theorem-api"
    ("theorem-api" ∷ [])
    theoremErgonomicsLayer
    reusableTheoremAPI
    "AgdaPhysicsTheoremErgonomicsAPI"
    false
    refl
    true
    refl
  ∷ mkSearchNavigationKey
    "parity:examples:regression"
    ("examples-regression" ∷ [])
    examplesRegressionLayer
    examplesAndRegressionRows
    "AgdaPhysicsExamplesRegressionSurface"
    false
    refl
    true
    refl
  ∷ mkSearchNavigationKey
    "parity:automation:search-navigation"
    ("automation-search-navigation" ∷ [])
    automationSearchLayer
    searchAndNavigationIndex
    "AgdaPhysicsAutomationSearchNavigationSurface"
    false
    refl
    true
    refl
  ∷ mkSearchNavigationKey
    "parity:governance:no-promotion"
    ("no-promotion" ∷ [])
    packageRoadmapGovernanceLayer
    packageLevelRoadmap
    "AgdaPhysicsPackageRoadmapGovernanceSurface"
    false
    refl
    true
    refl
  ∷ finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKey
  ∷ []

record CanonicalParityExampleReceipt : Set where
  constructor mkCanonicalParityExampleReceipt
  field
    interfaceName :
      String
    theoremAPIShape :
      TheoremAPIShape
    searchNavigationKey :
      SearchNavigationKey
    linearAnalysisConsumed :
      Bool
    linearAnalysisConsumedIsTrue :
      linearAnalysisConsumed ≡ true
    lieGaugeConsumed :
      Bool
    lieGaugeConsumedIsTrue :
      lieGaugeConsumed ≡ true
    qftConsumed :
      Bool
    qftConsumedIsTrue :
      qftConsumed ≡ true
    grPDEConsumed :
      Bool
    grPDEConsumedIsFalse :
      grPDEConsumed ≡ false
    examplePromoted :
      Bool
    examplePromotedIsFalse :
      examplePromoted ≡ false
    regressionImport :
      String
    dischargeByRefl :
      List String
    dischargeByReflIsCanonical :
      dischargeByRefl ≡ finiteYMSpectralDefinitionalReflObligations
    requiresExplicitProof :
      List String
    requiresExplicitProofIsCanonical :
      requiresExplicitProof ≡ finiteYMSpectralExplicitProofObligations
    noPromotionWithoutAuthority :
      ParityPromotionAuthorityToken →
      ⊥

finiteDimensionalSpectralTheoremDiscreteYMHamiltonianReceipt :
  CanonicalParityExampleReceipt
finiteDimensionalSpectralTheoremDiscreteYMHamiltonianReceipt =
  mkCanonicalParityExampleReceipt
    "finite-discrete-YM-Hamiltonian-spectral-example"
    finiteYMSpectralTheoremAPI
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKey
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    "DASHI.Physics.Examples.DiscreteYMHamiltonianSpectralTheoremRegression"
    finiteYMSpectralDefinitionalReflObligations
    refl
    finiteYMSpectralExplicitProofObligations
    refl
    parityPromotionImpossibleHere

finiteDimensionalSpectralTheoremDiscreteYMHamiltonianInterfaceNameIsExact :
  CanonicalParityExampleReceipt.interfaceName
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianReceipt
  ≡
  "finite-discrete-YM-Hamiltonian-spectral-example"
finiteDimensionalSpectralTheoremDiscreteYMHamiltonianInterfaceNameIsExact =
  refl

finiteDimensionalSpectralTheoremDiscreteYMHamiltonianTheoremAPIIsExact :
  CanonicalParityExampleReceipt.theoremAPIShape
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianReceipt
  ≡
  finiteYMSpectralTheoremAPI
finiteDimensionalSpectralTheoremDiscreteYMHamiltonianTheoremAPIIsExact =
  refl

finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKeyIsExact :
  CanonicalParityExampleReceipt.searchNavigationKey
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianReceipt
  ≡
  finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKey
finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKeyIsExact =
  refl

finiteDimensionalSpectralTheoremDiscreteYMHamiltonianDischargeByReflIsExact :
  CanonicalParityExampleReceipt.dischargeByRefl
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianReceipt
  ≡
  finiteYMSpectralDefinitionalReflObligations
finiteDimensionalSpectralTheoremDiscreteYMHamiltonianDischargeByReflIsExact =
  refl

finiteDimensionalSpectralTheoremDiscreteYMHamiltonianRequiresExplicitProofIsExact :
  CanonicalParityExampleReceipt.requiresExplicitProof
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianReceipt
  ≡
  finiteYMSpectralExplicitProofObligations
finiteDimensionalSpectralTheoremDiscreteYMHamiltonianRequiresExplicitProofIsExact =
  refl

finiteDimensionalSpectralTheoremDiscreteYMHamiltonianNotPromoted :
  CanonicalParityExampleReceipt.examplePromoted
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianReceipt
  ≡
  false
finiteDimensionalSpectralTheoremDiscreteYMHamiltonianNotPromoted =
  refl

finiteDimensionalSpectralTheoremDiscreteYMHamiltonianNoPromotionWithoutAuthority :
  ParityPromotionAuthorityToken →
  ⊥
finiteDimensionalSpectralTheoremDiscreteYMHamiltonianNoPromotionWithoutAuthority =
  CanonicalParityExampleReceipt.noPromotionWithoutAuthority
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianReceipt

canonicalParityExampleReceipts : List CanonicalParityExampleReceipt
canonicalParityExampleReceipts =
  finiteDimensionalSpectralTheoremDiscreteYMHamiltonianReceipt
  ∷ []

data AutomationDischargeClass : Set where
  definitionalReflDischarge :
    AutomationDischargeClass
  explicitProofObligation :
    AutomationDischargeClass

record AutomationSearchDischargeClassification : Set where
  constructor mkAutomationSearchDischargeClassification
  field
    classificationName :
      String
    searchNavigationKey :
      SearchNavigationKey
    dischargeClass :
      AutomationDischargeClass
    dischargeByRefl :
      Bool
    requiresExplicitProof :
      Bool
    classificationRecorded :
      Bool
    classificationRecordedIsTrue :
      classificationRecorded ≡ true
    promotionClaimed :
      Bool
    promotionClaimedIsFalse :
      promotionClaimed ≡ false

dimensionLengthBasisDischargeClassification :
  AutomationSearchDischargeClassification
dimensionLengthBasisDischargeClassification =
  mkAutomationSearchDischargeClassification
    "dimension=length basis"
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKey
    definitionalReflDischarge
    true
    false
    true
    refl
    false
    refl

finiteJacobiCheckDischargeClassification :
  AutomationSearchDischargeClassification
finiteJacobiCheckDischargeClassification =
  mkAutomationSearchDischargeClassification
    "finite Jacobi check"
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKey
    definitionalReflDischarge
    true
    false
    true
    refl
    false
    refl

finiteCCRMatrixLawDischargeClassification :
  AutomationSearchDischargeClassification
finiteCCRMatrixLawDischargeClassification =
  mkAutomationSearchDischargeClassification
    "finite CCR matrix law"
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKey
    definitionalReflDischarge
    true
    false
    true
    refl
    false
    refl

spanningExplicitProofClassification :
  AutomationSearchDischargeClassification
spanningExplicitProofClassification =
  mkAutomationSearchDischargeClassification
    "spanning"
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKey
    explicitProofObligation
    false
    true
    true
    refl
    false
    refl

linearIndependenceExplicitProofClassification :
  AutomationSearchDischargeClassification
linearIndependenceExplicitProofClassification =
  mkAutomationSearchDischargeClassification
    "linear independence"
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKey
    explicitProofObligation
    false
    true
    true
    refl
    false
    refl

cauchyCompletenessExplicitProofClassification :
  AutomationSearchDischargeClassification
cauchyCompletenessExplicitProofClassification =
  mkAutomationSearchDischargeClassification
    "Cauchy completeness"
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKey
    explicitProofObligation
    false
    true
    true
    refl
    false
    refl

spectralTheoremExplicitProofClassification :
  AutomationSearchDischargeClassification
spectralTheoremExplicitProofClassification =
  mkAutomationSearchDischargeClassification
    "spectral theorem"
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKey
    explicitProofObligation
    false
    true
    true
    refl
    false
    refl

gaugeInvarianceExplicitProofClassification :
  AutomationSearchDischargeClassification
gaugeInvarianceExplicitProofClassification =
  mkAutomationSearchDischargeClassification
    "gauge invariance"
    finiteDimensionalSpectralTheoremDiscreteYMHamiltonianSearchKey
    explicitProofObligation
    false
    true
    true
    refl
    false
    refl

canonicalAutomationSearchDischargeClassifications :
  List AutomationSearchDischargeClassification
canonicalAutomationSearchDischargeClassifications =
  dimensionLengthBasisDischargeClassification
  ∷ finiteJacobiCheckDischargeClassification
  ∷ finiteCCRMatrixLawDischargeClassification
  ∷ spanningExplicitProofClassification
  ∷ linearIndependenceExplicitProofClassification
  ∷ cauchyCompletenessExplicitProofClassification
  ∷ spectralTheoremExplicitProofClassification
  ∷ gaugeInvarianceExplicitProofClassification
  ∷ []

data PackageGovernancePromotionAuthorityToken : Set where

packageGovernancePromotionImpossibleHere :
  PackageGovernancePromotionAuthorityToken →
  ⊥
packageGovernancePromotionImpossibleHere ()

record PackageGovernanceNoPromotionBoundary : Set where
  constructor mkPackageGovernanceNoPromotionBoundary
  field
    boundaryName :
      String
    packageGovernanceRecorded :
      Bool
    packageGovernanceRecordedIsTrue :
      packageGovernanceRecorded ≡ true
    authorityTokenPresent :
      Bool
    authorityTokenPresentIsFalse :
      authorityTokenPresent ≡ false
    noPromotionAuthorityBoundary :
      Bool
    noPromotionAuthorityBoundaryIsTrue :
      noPromotionAuthorityBoundary ≡ true
    examplePromotionAllowed :
      Bool
    examplePromotionAllowedIsFalse :
      examplePromotionAllowed ≡ false
    packagePromotionAllowed :
      Bool
    packagePromotionAllowedIsFalse :
      packagePromotionAllowed ≡ false
    noPackagePromotionWithoutAuthority :
      PackageGovernancePromotionAuthorityToken →
      ⊥

canonicalPackageGovernanceNoPromotionBoundary :
  PackageGovernanceNoPromotionBoundary
canonicalPackageGovernanceNoPromotionBoundary =
  mkPackageGovernanceNoPromotionBoundary
    "package-governance/no-promotion authority token boundary"
    true
    refl
    false
    refl
    true
    refl
    false
    refl
    false
    refl
    packageGovernancePromotionImpossibleHere

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
    parityExampleReceipts :
      List CanonicalParityExampleReceipt
    parityExampleReceiptsAreCanonical :
      parityExampleReceipts ≡ canonicalParityExampleReceipts
    automationSearchDischargeClassifications :
      List AutomationSearchDischargeClassification
    automationSearchDischargeClassificationsAreCanonical :
      automationSearchDischargeClassifications
        ≡
        canonicalAutomationSearchDischargeClassifications
    packageGovernanceNoPromotionBoundary :
      PackageGovernanceNoPromotionBoundary
    packageGovernanceNoPromotionBoundaryIsCanonical :
      packageGovernanceNoPromotionBoundary
        ≡
        canonicalPackageGovernanceNoPromotionBoundary
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
    canonicalParityExampleReceipts
    refl
    canonicalAutomationSearchDischargeClassifications
    refl
    canonicalPackageGovernanceNoPromotionBoundary
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
    authorityRequiredVerdict
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
