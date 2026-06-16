module DASHI.Core.FormalLensQualificationCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdapterCanonicalityCore as Adapter
import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.BridgeRequirementCore as Bridge
import DASHI.Core.CandidateOnlyCore as Candidate
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Reusable formal-lens qualification core.
--
-- A formal lens names an inspection grammar only.  Qualification rows can
-- say which thresholds and residual boundaries are visible, but they do not
-- promote analytic, empirical, clinical, physical, theorem, metaphysical,
-- external, governance, or promotion authority.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Formal-lens vocabulary.

data FormalLens : Set where
  SymbolicRational :
    FormalLens

  Operator :
    FormalLens

  Functional :
    FormalLens

  Hamiltonian :
    FormalLens

  GradientFlow :
    FormalLens

  ResistiveTransport :
    FormalLens

  Spectral :
    FormalLens

  Group :
    FormalLens

  Category :
    FormalLens

  Number :
    FormalLens

  Lattice :
    FormalLens

  Topological :
    FormalLens

  Probabilistic :
    FormalLens

  Graph :
    FormalLens

  Information :
    FormalLens

  NamedFormalLens :
    String →
    FormalLens

canonicalFormalLenses : List FormalLens
canonicalFormalLenses =
  SymbolicRational
  ∷ Operator
  ∷ Functional
  ∷ Hamiltonian
  ∷ GradientFlow
  ∷ ResistiveTransport
  ∷ Spectral
  ∷ Group
  ∷ Category
  ∷ Number
  ∷ Lattice
  ∷ Topological
  ∷ Probabilistic
  ∷ Graph
  ∷ Information
  ∷ []

canonicalFormalLensCount : Nat
canonicalFormalLensCount =
  listCount canonicalFormalLenses

------------------------------------------------------------------------
-- Threshold, role, and residual boundary vocabulary.

data QualificationRole : Set where
  sourceLensRole :
    QualificationRole

  targetLensRole :
    QualificationRole

  residualBoundaryRole :
    QualificationRole

  thresholdWitnessRole :
    QualificationRole

  adapterConsumerRole :
    QualificationRole

  namedQualificationRole :
    String →
    QualificationRole

data ThresholdLabel : Set where
  requiredThresholdLabel :
    ThresholdLabel

  metThresholdLabel :
    ThresholdLabel

  missingThresholdLabel :
    ThresholdLabel

  namedThresholdLabel :
    String →
    ThresholdLabel

data ThresholdStatus : Set where
  thresholdRequired :
    ThresholdStatus

  thresholdMet :
    ThresholdStatus

  thresholdMissing :
    ThresholdStatus

data ResidualBoundaryLabel : Set where
  explicitResidualBoundary :
    ResidualBoundaryLabel

  explicitOpenResidualBoundary :
    ResidualBoundaryLabel

  explicitMissingThresholdResidualBoundary :
    ResidualBoundaryLabel

  explicitBridgeResidualBoundary :
    ResidualBoundaryLabel

  explicitAdapterResidualBoundary :
    ResidualBoundaryLabel

  namedResidualBoundary :
    String →
    ResidualBoundaryLabel

thresholdStatusRequired :
  ThresholdStatus →
  Bool
thresholdStatusRequired thresholdRequired =
  true
thresholdStatusRequired thresholdMet =
  true
thresholdStatusRequired thresholdMissing =
  true

thresholdStatusMet :
  ThresholdStatus →
  Bool
thresholdStatusMet thresholdRequired =
  false
thresholdStatusMet thresholdMet =
  true
thresholdStatusMet thresholdMissing =
  false

thresholdStatusMissing :
  ThresholdStatus →
  Bool
thresholdStatusMissing thresholdRequired =
  false
thresholdStatusMissing thresholdMet =
  false
thresholdStatusMissing thresholdMissing =
  true

record ThresholdRow : Set where
  constructor thresholdRow
  field
    thresholdRowLabel :
      String

    thresholdRowRole :
      QualificationRole

    thresholdRowStatus :
      ThresholdStatus

    thresholdRowBoundary :
      ResidualBoundaryLabel

    thresholdRequiredFlag :
      Bool

    thresholdMetFlag :
      Bool

    thresholdMissingFlag :
      Bool

open ThresholdRow public

record ThresholdRowReceipt
  (row : ThresholdRow) :
  Set where
  constructor thresholdRowReceipt
  field
    thresholdRequiredMatchesStatus :
      thresholdRequiredFlag row
      ≡
      thresholdStatusRequired (thresholdRowStatus row)

    thresholdMetMatchesStatus :
      thresholdMetFlag row
      ≡
      thresholdStatusMet (thresholdRowStatus row)

    thresholdMissingMatchesStatus :
      thresholdMissingFlag row
      ≡
      thresholdStatusMissing (thresholdRowStatus row)

open ThresholdRowReceipt public

mkThresholdRow :
  String →
  QualificationRole →
  ThresholdStatus →
  ResidualBoundaryLabel →
  ThresholdRow
mkThresholdRow label role status boundary =
  thresholdRow
    label
    role
    status
    boundary
    (thresholdStatusRequired status)
    (thresholdStatusMet status)
    (thresholdStatusMissing status)

canonicalRequiredThresholdRow : ThresholdRow
canonicalRequiredThresholdRow =
  mkThresholdRow
    "formal lens threshold required"
    thresholdWitnessRole
    thresholdRequired
    explicitOpenResidualBoundary

canonicalMetThresholdRow : ThresholdRow
canonicalMetThresholdRow =
  mkThresholdRow
    "formal lens threshold met"
    thresholdWitnessRole
    thresholdMet
    explicitResidualBoundary

canonicalMissingThresholdRow : ThresholdRow
canonicalMissingThresholdRow =
  mkThresholdRow
    "formal lens threshold missing"
    thresholdWitnessRole
    thresholdMissing
    explicitMissingThresholdResidualBoundary

canonicalRequiredThresholdRowReceipt :
  ThresholdRowReceipt canonicalRequiredThresholdRow
canonicalRequiredThresholdRowReceipt =
  thresholdRowReceipt refl refl refl

canonicalMetThresholdRowReceipt :
  ThresholdRowReceipt canonicalMetThresholdRow
canonicalMetThresholdRowReceipt =
  thresholdRowReceipt refl refl refl

canonicalMissingThresholdRowReceipt :
  ThresholdRowReceipt canonicalMissingThresholdRow
canonicalMissingThresholdRowReceipt =
  thresholdRowReceipt refl refl refl

canonicalThresholdRows : List ThresholdRow
canonicalThresholdRows =
  canonicalRequiredThresholdRow
  ∷ canonicalMetThresholdRow
  ∷ canonicalMissingThresholdRow
  ∷ []

canonicalThresholdRowCount : Nat
canonicalThresholdRowCount =
  listCount canonicalThresholdRows

------------------------------------------------------------------------
-- Canonical adapters consumed by qualification surfaces.

canonicalCandidateOnlyCoreAdapter :
  Adapter.AdapterCanonicalityReceipt
    Candidate.CandidateOnlyRow
    Candidate.canonicalRowCandidateOnlyRow
canonicalCandidateOnlyCoreAdapter =
  Adapter.mkCanonicalAdapterReceipt
    "formal lens candidate-only core adapter"
    "DASHI.Core.FormalLensQualificationCore"
    "Candidate.canonicalRowCandidateOnlyRow"
    Adapter.receiptAdapterKind
    Candidate.canonicalRowCandidateOnlyRow

canonicalAuthorityNonPromotionCoreAdapter :
  Adapter.AdapterCanonicalityReceipt
    Authority.AuthorityNonPromotionBundle
    Authority.canonicalAuthorityNonPromotionBundle
canonicalAuthorityNonPromotionCoreAdapter =
  Adapter.mkCanonicalAdapterReceipt
    "formal lens authority non-promotion core adapter"
    "DASHI.Core.FormalLensQualificationCore"
    "Authority.canonicalAuthorityNonPromotionBundle"
    Adapter.authorityAdapterKind
    Authority.canonicalAuthorityNonPromotionBundle

canonicalBridgeRequirementCoreAdapter :
  Adapter.AdapterCanonicalityReceipt
    Bridge.BridgeRequirementCoreReceipt
    Bridge.canonicalBridgeRequirementCoreReceipt
canonicalBridgeRequirementCoreAdapter =
  Adapter.mkCanonicalAdapterReceipt
    "formal lens bridge requirement core adapter"
    "DASHI.Core.FormalLensQualificationCore"
    "Bridge.canonicalBridgeRequirementCoreReceipt"
    Adapter.bridgeAdapterKind
    Bridge.canonicalBridgeRequirementCoreReceipt

canonicalAdapterCanonicalityCoreAdapter :
  Adapter.AdapterCanonicalityReceipt
    Adapter.AdapterSurface
    Adapter.canonicalAdapter
canonicalAdapterCanonicalityCoreAdapter =
  Adapter.canonicalAdapterCanonicalityReceipt

------------------------------------------------------------------------
-- Candidate and bridge rows used by the canonical qualification surfaces.

genericFormalLensCandidateRow : Candidate.CandidateOnlyRow
genericFormalLensCandidateRow =
  Candidate.mkCandidateOnlyRow
    "formal lens qualification candidate"
    "DASHI.Core.FormalLensQualificationCore"
    "genericFormalLensCandidateRow"
    Candidate.rowCandidateKind
    Candidate.rowCandidateOnlyStatus
    "formal-lens qualification records an inspection grammar only"
    "domain acceptance, support, authority, and promotion remain external"

genericFormalLensCandidateReceipt :
  Candidate.CandidateOnlyReceipt genericFormalLensCandidateRow
genericFormalLensCandidateReceipt =
  Candidate.mkCandidateOnlyReceipt
    genericFormalLensCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

gradientResistiveCandidateRow : Candidate.CandidateOnlyRow
gradientResistiveCandidateRow =
  Candidate.mkCandidateOnlyRow
    "gradient-flow resistive-transport candidate"
    "DASHI.Core.FormalLensQualificationCore"
    "gradientResistiveCandidateRow"
    Candidate.operatorCandidateKind
    Candidate.operatorCandidateOnlyStatus
    "gradient-flow and resistive-transport lenses share a candidate residual row"
    "analytic PDE, physical transport, empirical fit, and theorem authority remain absent"

gradientResistiveCandidateReceipt :
  Candidate.CandidateOnlyReceipt gradientResistiveCandidateRow
gradientResistiveCandidateReceipt =
  Candidate.mkCandidateOnlyReceipt
    gradientResistiveCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

genericFormalLensBridgeRow : Bridge.BridgeRequirementRow
genericFormalLensBridgeRow =
  Bridge.canonicalBridgeRequirementRow
    "formal lens source"
    "formal lens target"
    Bridge.bridgeSuppliedCandidateOnly
    true
    true
    true

genericFormalLensBridgeReceipt :
  Bridge.BridgeRequirementRowReceipt genericFormalLensBridgeRow
genericFormalLensBridgeReceipt =
  Bridge.bridgeRequirementRowReceipt refl refl refl

gradientResistiveBridgeRow : Bridge.BridgeRequirementRow
gradientResistiveBridgeRow =
  Bridge.canonicalBridgeRequirementRow
    "gradient flow"
    "resistive transport"
    Bridge.transportMapRequired
    true
    false
    false

gradientResistiveBridgeReceipt :
  Bridge.BridgeRequirementRowReceipt gradientResistiveBridgeRow
gradientResistiveBridgeReceipt =
  Bridge.bridgeRequirementRowReceipt refl refl refl

------------------------------------------------------------------------
-- Qualification surface and receipt.

record FormalLensQualificationSurface : Set where
  constructor formalLensQualificationSurface
  field
    qualificationLabel :
      String

    qualificationOwner :
      String

    qualificationSurface :
      String

    sourceLens :
      FormalLens

    targetLens :
      FormalLens

    qualificationRole :
      QualificationRole

    threshold :
      ThresholdRow

    thresholdReceipt :
      ThresholdRowReceipt threshold

    residualBoundary :
      ResidualBoundaryLabel

    candidateRow :
      Candidate.CandidateOnlyRow

    candidateReceipt :
      Candidate.CandidateOnlyReceipt candidateRow

    authorityBundle :
      Authority.AuthorityNonPromotionBundle

    bridgeRow :
      Bridge.BridgeRequirementRow

    bridgeReceipt :
      Bridge.BridgeRequirementRowReceipt bridgeRow

    candidateCoreAdapter :
      Adapter.AdapterCanonicalityReceipt
        Candidate.CandidateOnlyRow
        Candidate.canonicalRowCandidateOnlyRow

    authorityCoreAdapter :
      Adapter.AdapterCanonicalityReceipt
        Authority.AuthorityNonPromotionBundle
        Authority.canonicalAuthorityNonPromotionBundle

    bridgeCoreAdapter :
      Adapter.AdapterCanonicalityReceipt
        Bridge.BridgeRequirementCoreReceipt
        Bridge.canonicalBridgeRequirementCoreReceipt

    adapterCoreAdapter :
      Adapter.AdapterCanonicalityReceipt
        Adapter.AdapterSurface
        Adapter.canonicalAdapter

    qualificationStatement :
      String

    qualificationRemainingGap :
      String

    qualificationCandidateOnly :
      Bool

    qualificationPromoted :
      Bool

    analyticAuthority :
      Bool

    empiricalAuthority :
      Bool

    clinicalAuthority :
      Bool

    physicalAuthority :
      Bool

    theoremAuthority :
      Bool

    metaphysicalAuthority :
      Bool

    externalAuthority :
      Bool

    governanceAuthority :
      Bool

    promotionAuthority :
      Bool

open FormalLensQualificationSurface public

record FormalLensQualificationReceipt
  (surface : FormalLensQualificationSurface) :
  Set where
  constructor formalLensQualificationReceipt
  field
    receiptCandidateOnlyIsTrue :
      qualificationCandidateOnly surface ≡ true

    receiptPromotedIsFalse :
      qualificationPromoted surface ≡ false

    receiptAnalyticAuthorityFalse :
      analyticAuthority surface ≡ false

    receiptEmpiricalAuthorityFalse :
      empiricalAuthority surface ≡ false

    receiptClinicalAuthorityFalse :
      clinicalAuthority surface ≡ false

    receiptPhysicalAuthorityFalse :
      physicalAuthority surface ≡ false

    receiptTheoremAuthorityFalse :
      theoremAuthority surface ≡ false

    receiptMetaphysicalAuthorityFalse :
      metaphysicalAuthority surface ≡ false

    receiptExternalAuthorityFalse :
      externalAuthority surface ≡ false

    receiptGovernanceAuthorityFalse :
      governanceAuthority surface ≡ false

    receiptPromotionAuthorityFalse :
      promotionAuthority surface ≡ false

    receiptAuthorityBundleNonPromoting :
      Authority.promotesAnyAuthority (authorityBundle surface) ≡ false

    receiptBridgeAuthorityPromotionFalse :
      Bridge.rowAuthorityPromotion (bridgeRow surface) ≡ false

    receiptBridgeTransportMapAuthorityFalse :
      Bridge.rowTransportMapAuthority (bridgeRow surface) ≡ false

    receiptBridgeBackgroundAuthorityFalse :
      Bridge.rowBackgroundBridgeAuthority (bridgeRow surface) ≡ false

    receiptCandidateAdapterCanonical :
      Adapter.adapter (candidateCoreAdapter surface)
      ≡
      Candidate.canonicalRowCandidateOnlyRow

    receiptAuthorityAdapterCanonical :
      Adapter.adapter (authorityCoreAdapter surface)
      ≡
      Authority.canonicalAuthorityNonPromotionBundle

    receiptBridgeAdapterCanonical :
      Adapter.adapter (bridgeCoreAdapter surface)
      ≡
      Bridge.canonicalBridgeRequirementCoreReceipt

    receiptAdapterAdapterCanonical :
      Adapter.adapter (adapterCoreAdapter surface)
      ≡
      Adapter.canonicalAdapter

open FormalLensQualificationReceipt public

mkFormalLensQualificationSurface :
  String →
  String →
  String →
  FormalLens →
  FormalLens →
  QualificationRole →
  (threshold : ThresholdRow) →
  ThresholdRowReceipt threshold →
  ResidualBoundaryLabel →
  (candidateRow : Candidate.CandidateOnlyRow) →
  Candidate.CandidateOnlyReceipt candidateRow →
  (bridgeRow : Bridge.BridgeRequirementRow) →
  Bridge.BridgeRequirementRowReceipt bridgeRow →
  String →
  String →
  FormalLensQualificationSurface
mkFormalLensQualificationSurface
  label
  owner
  surface
  source
  target
  role
  thresholdRowValue
  thresholdRowReceiptValue
  boundary
  candidateRowValue
  candidateReceiptValue
  bridgeRowValue
  bridgeReceiptValue
  statement
  remainingGap =
  formalLensQualificationSurface
    label
    owner
    surface
    source
    target
    role
    thresholdRowValue
    thresholdRowReceiptValue
    boundary
    candidateRowValue
    candidateReceiptValue
    Authority.canonicalAuthorityNonPromotionBundle
    bridgeRowValue
    bridgeReceiptValue
    canonicalCandidateOnlyCoreAdapter
    canonicalAuthorityNonPromotionCoreAdapter
    canonicalBridgeRequirementCoreAdapter
    canonicalAdapterCanonicalityCoreAdapter
    statement
    remainingGap
    true
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false

mkFormalLensQualificationReceipt :
  (surface : FormalLensQualificationSurface) →
  qualificationCandidateOnly surface ≡ true →
  qualificationPromoted surface ≡ false →
  analyticAuthority surface ≡ false →
  empiricalAuthority surface ≡ false →
  clinicalAuthority surface ≡ false →
  physicalAuthority surface ≡ false →
  theoremAuthority surface ≡ false →
  metaphysicalAuthority surface ≡ false →
  externalAuthority surface ≡ false →
  governanceAuthority surface ≡ false →
  promotionAuthority surface ≡ false →
  Authority.promotesAnyAuthority (authorityBundle surface) ≡ false →
  Bridge.rowAuthorityPromotion (bridgeRow surface) ≡ false →
  Bridge.rowTransportMapAuthority (bridgeRow surface) ≡ false →
  Bridge.rowBackgroundBridgeAuthority (bridgeRow surface) ≡ false →
  Adapter.adapter (candidateCoreAdapter surface)
    ≡
    Candidate.canonicalRowCandidateOnlyRow →
  Adapter.adapter (authorityCoreAdapter surface)
    ≡
    Authority.canonicalAuthorityNonPromotionBundle →
  Adapter.adapter (bridgeCoreAdapter surface)
    ≡
    Bridge.canonicalBridgeRequirementCoreReceipt →
  Adapter.adapter (adapterCoreAdapter surface)
    ≡
    Adapter.canonicalAdapter →
  FormalLensQualificationReceipt surface
mkFormalLensQualificationReceipt
  surface
  candidateOnlyProof
  promotedProof
  analyticProof
  empiricalProof
  clinicalProof
  physicalProof
  theoremProof
  metaphysicalProof
  externalProof
  governanceProof
  promotionProof
  authorityBundleProof
  bridgeAuthorityProof
  bridgeTransportProof
  bridgeBackgroundProof
  candidateAdapterProof
  authorityAdapterProof
  bridgeAdapterProof
  adapterAdapterProof =
  formalLensQualificationReceipt
    candidateOnlyProof
    promotedProof
    analyticProof
    empiricalProof
    clinicalProof
    physicalProof
    theoremProof
    metaphysicalProof
    externalProof
    governanceProof
    promotionProof
    authorityBundleProof
    bridgeAuthorityProof
    bridgeTransportProof
    bridgeBackgroundProof
    candidateAdapterProof
    authorityAdapterProof
    bridgeAdapterProof
    adapterAdapterProof

------------------------------------------------------------------------
-- Projection lemmas.

qualificationIsCandidateOnly :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  qualificationCandidateOnly surface ≡ true
qualificationIsCandidateOnly receipt =
  receiptCandidateOnlyIsTrue receipt

qualificationPromotedFalse :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  qualificationPromoted surface ≡ false
qualificationPromotedFalse receipt =
  receiptPromotedIsFalse receipt

qualificationAnalyticAuthorityFalse :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  analyticAuthority surface ≡ false
qualificationAnalyticAuthorityFalse receipt =
  receiptAnalyticAuthorityFalse receipt

qualificationEmpiricalAuthorityFalse :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  empiricalAuthority surface ≡ false
qualificationEmpiricalAuthorityFalse receipt =
  receiptEmpiricalAuthorityFalse receipt

qualificationClinicalAuthorityFalse :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  clinicalAuthority surface ≡ false
qualificationClinicalAuthorityFalse receipt =
  receiptClinicalAuthorityFalse receipt

qualificationPhysicalAuthorityFalse :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  physicalAuthority surface ≡ false
qualificationPhysicalAuthorityFalse receipt =
  receiptPhysicalAuthorityFalse receipt

qualificationTheoremAuthorityFalse :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  theoremAuthority surface ≡ false
qualificationTheoremAuthorityFalse receipt =
  receiptTheoremAuthorityFalse receipt

qualificationMetaphysicalAuthorityFalse :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  metaphysicalAuthority surface ≡ false
qualificationMetaphysicalAuthorityFalse receipt =
  receiptMetaphysicalAuthorityFalse receipt

qualificationExternalAuthorityFalse :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  externalAuthority surface ≡ false
qualificationExternalAuthorityFalse receipt =
  receiptExternalAuthorityFalse receipt

qualificationGovernanceAuthorityFalse :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  governanceAuthority surface ≡ false
qualificationGovernanceAuthorityFalse receipt =
  receiptGovernanceAuthorityFalse receipt

qualificationPromotionAuthorityFalse :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  promotionAuthority surface ≡ false
qualificationPromotionAuthorityFalse receipt =
  receiptPromotionAuthorityFalse receipt

qualificationCandidateAdapterCanonical :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  Adapter.adapter (candidateCoreAdapter surface)
  ≡
  Candidate.canonicalRowCandidateOnlyRow
qualificationCandidateAdapterCanonical receipt =
  receiptCandidateAdapterCanonical receipt

qualificationAuthorityAdapterCanonical :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  Adapter.adapter (authorityCoreAdapter surface)
  ≡
  Authority.canonicalAuthorityNonPromotionBundle
qualificationAuthorityAdapterCanonical receipt =
  receiptAuthorityAdapterCanonical receipt

qualificationBridgeAdapterCanonical :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  Adapter.adapter (bridgeCoreAdapter surface)
  ≡
  Bridge.canonicalBridgeRequirementCoreReceipt
qualificationBridgeAdapterCanonical receipt =
  receiptBridgeAdapterCanonical receipt

qualificationAdapterAdapterCanonical :
  {surface : FormalLensQualificationSurface} →
  FormalLensQualificationReceipt surface →
  Adapter.adapter (adapterCoreAdapter surface)
  ≡
  Adapter.canonicalAdapter
qualificationAdapterAdapterCanonical receipt =
  receiptAdapterAdapterCanonical receipt

------------------------------------------------------------------------
-- Canonical qualification surfaces and receipts.

canonicalGenericFormalLensQualificationSurface :
  FormalLensQualificationSurface
canonicalGenericFormalLensQualificationSurface =
  mkFormalLensQualificationSurface
    "generic formal-lens qualification"
    "DASHI.Core.FormalLensQualificationCore"
    "canonicalGenericFormalLensQualificationSurface"
    (NamedFormalLens "generic formal lens")
    (NamedFormalLens "generic residual target")
    sourceLensRole
    canonicalRequiredThresholdRow
    canonicalRequiredThresholdRowReceipt
    explicitOpenResidualBoundary
    genericFormalLensCandidateRow
    genericFormalLensCandidateReceipt
    genericFormalLensBridgeRow
    genericFormalLensBridgeReceipt
    "generic formal-lens qualification records the lens, threshold, residual boundary, and canonical core adapters"
    "no domain authority, theorem authority, external acceptance, or governance promotion is supplied here"

canonicalGenericFormalLensQualificationReceipt :
  FormalLensQualificationReceipt
    canonicalGenericFormalLensQualificationSurface
canonicalGenericFormalLensQualificationReceipt =
  mkFormalLensQualificationReceipt
    canonicalGenericFormalLensQualificationSurface
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalGradientResistiveQualificationSurface :
  FormalLensQualificationSurface
canonicalGradientResistiveQualificationSurface =
  mkFormalLensQualificationSurface
    "gradient-flow resistive-transport qualification"
    "DASHI.Core.FormalLensQualificationCore"
    "canonicalGradientResistiveQualificationSurface"
    GradientFlow
    ResistiveTransport
    residualBoundaryRole
    canonicalMissingThresholdRow
    canonicalMissingThresholdRowReceipt
    explicitMissingThresholdResidualBoundary
    gradientResistiveCandidateRow
    gradientResistiveCandidateReceipt
    gradientResistiveBridgeRow
    gradientResistiveBridgeReceipt
    "gradient-flow and resistive-transport are related only as a candidate residual-boundary row"
    "missing transport threshold, analytic PDE proof, physical law, empirical validation, and theorem authority remain open"

canonicalGradientResistiveQualificationReceipt :
  FormalLensQualificationReceipt
    canonicalGradientResistiveQualificationSurface
canonicalGradientResistiveQualificationReceipt =
  mkFormalLensQualificationReceipt
    canonicalGradientResistiveQualificationSurface
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

genericQualificationSourceLens :
  sourceLens canonicalGenericFormalLensQualificationSurface
  ≡
  NamedFormalLens "generic formal lens"
genericQualificationSourceLens =
  refl

genericQualificationThresholdRequired :
  thresholdRowStatus (threshold canonicalGenericFormalLensQualificationSurface)
  ≡
  thresholdRequired
genericQualificationThresholdRequired =
  refl

genericQualificationPromotedFalse :
  qualificationPromoted canonicalGenericFormalLensQualificationSurface
  ≡
  false
genericQualificationPromotedFalse =
  qualificationPromotedFalse canonicalGenericFormalLensQualificationReceipt

gradientResistiveSourceLens :
  sourceLens canonicalGradientResistiveQualificationSurface
  ≡
  GradientFlow
gradientResistiveSourceLens =
  refl

gradientResistiveTargetLens :
  targetLens canonicalGradientResistiveQualificationSurface
  ≡
  ResistiveTransport
gradientResistiveTargetLens =
  refl

gradientResistiveThresholdMissing :
  thresholdRowStatus (threshold canonicalGradientResistiveQualificationSurface)
  ≡
  thresholdMissing
gradientResistiveThresholdMissing =
  refl

gradientResistivePromotedFalse :
  qualificationPromoted canonicalGradientResistiveQualificationSurface
  ≡
  false
gradientResistivePromotedFalse =
  qualificationPromotedFalse canonicalGradientResistiveQualificationReceipt

gradientResistivePhysicalAuthorityFalse :
  physicalAuthority canonicalGradientResistiveQualificationSurface
  ≡
  false
gradientResistivePhysicalAuthorityFalse =
  qualificationPhysicalAuthorityFalse
    canonicalGradientResistiveQualificationReceipt

gradientResistiveTheoremAuthorityFalse :
  theoremAuthority canonicalGradientResistiveQualificationSurface
  ≡
  false
gradientResistiveTheoremAuthorityFalse =
  qualificationTheoremAuthorityFalse
    canonicalGradientResistiveQualificationReceipt

canonicalFormalLensQualificationSurfaces :
  List FormalLensQualificationSurface
canonicalFormalLensQualificationSurfaces =
  canonicalGenericFormalLensQualificationSurface
  ∷ canonicalGradientResistiveQualificationSurface
  ∷ []

canonicalFormalLensQualificationSurfaceCount : Nat
canonicalFormalLensQualificationSurfaceCount =
  listCount canonicalFormalLensQualificationSurfaces

data AllQualificationSurfacesFailClosed :
  List FormalLensQualificationSurface →
  Set where
  allQualificationSurfacesFailClosedNil :
    AllQualificationSurfacesFailClosed []

  allQualificationSurfacesFailClosedCons :
    ∀ {surface surfaces} →
    qualificationPromoted surface ≡ false →
    analyticAuthority surface ≡ false →
    empiricalAuthority surface ≡ false →
    clinicalAuthority surface ≡ false →
    physicalAuthority surface ≡ false →
    theoremAuthority surface ≡ false →
    metaphysicalAuthority surface ≡ false →
    externalAuthority surface ≡ false →
    governanceAuthority surface ≡ false →
    promotionAuthority surface ≡ false →
    AllQualificationSurfacesFailClosed surfaces →
    AllQualificationSurfacesFailClosed (surface ∷ surfaces)

canonicalFormalLensQualificationSurfacesFailClosed :
  AllQualificationSurfacesFailClosed
    canonicalFormalLensQualificationSurfaces
canonicalFormalLensQualificationSurfacesFailClosed =
  allQualificationSurfacesFailClosedCons
    (qualificationPromotedFalse
      canonicalGenericFormalLensQualificationReceipt)
    (qualificationAnalyticAuthorityFalse
      canonicalGenericFormalLensQualificationReceipt)
    (qualificationEmpiricalAuthorityFalse
      canonicalGenericFormalLensQualificationReceipt)
    (qualificationClinicalAuthorityFalse
      canonicalGenericFormalLensQualificationReceipt)
    (qualificationPhysicalAuthorityFalse
      canonicalGenericFormalLensQualificationReceipt)
    (qualificationTheoremAuthorityFalse
      canonicalGenericFormalLensQualificationReceipt)
    (qualificationMetaphysicalAuthorityFalse
      canonicalGenericFormalLensQualificationReceipt)
    (qualificationExternalAuthorityFalse
      canonicalGenericFormalLensQualificationReceipt)
    (qualificationGovernanceAuthorityFalse
      canonicalGenericFormalLensQualificationReceipt)
    (qualificationPromotionAuthorityFalse
      canonicalGenericFormalLensQualificationReceipt)
    (allQualificationSurfacesFailClosedCons
      (qualificationPromotedFalse
        canonicalGradientResistiveQualificationReceipt)
      (qualificationAnalyticAuthorityFalse
        canonicalGradientResistiveQualificationReceipt)
      (qualificationEmpiricalAuthorityFalse
        canonicalGradientResistiveQualificationReceipt)
      (qualificationClinicalAuthorityFalse
        canonicalGradientResistiveQualificationReceipt)
      (qualificationPhysicalAuthorityFalse
        canonicalGradientResistiveQualificationReceipt)
      (qualificationTheoremAuthorityFalse
        canonicalGradientResistiveQualificationReceipt)
      (qualificationMetaphysicalAuthorityFalse
        canonicalGradientResistiveQualificationReceipt)
      (qualificationExternalAuthorityFalse
        canonicalGradientResistiveQualificationReceipt)
      (qualificationGovernanceAuthorityFalse
        canonicalGradientResistiveQualificationReceipt)
      (qualificationPromotionAuthorityFalse
        canonicalGradientResistiveQualificationReceipt)
      allQualificationSurfacesFailClosedNil)

------------------------------------------------------------------------
-- Generic receipt adapter.

formalLensQualificationGenericReceipt :
  FormalLensQualificationSurface →
  GenericReceipt.GenericReceipt
formalLensQualificationGenericReceipt surface =
  GenericReceipt.mkNonPromotingReceipt
    (qualificationLabel surface)
    (qualificationOwner surface)
    (qualificationSurface surface)
    (qualificationStatement surface)
    (qualificationRemainingGap surface)
    "agda -i . DASHI/Core/FormalLensQualificationCore.agda"

canonicalGenericFormalLensQualificationGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalGenericFormalLensQualificationGenericReceipt =
  formalLensQualificationGenericReceipt
    canonicalGenericFormalLensQualificationSurface

canonicalGradientResistiveQualificationGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalGradientResistiveQualificationGenericReceipt =
  formalLensQualificationGenericReceipt
    canonicalGradientResistiveQualificationSurface

canonicalGenericFormalLensQualificationGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim
    canonicalGenericFormalLensQualificationGenericReceipt
  ≡
  false
canonicalGenericFormalLensQualificationGenericReceiptNonPromoting =
  refl

canonicalGradientResistiveQualificationGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim
    canonicalGradientResistiveQualificationGenericReceipt
  ≡
  false
canonicalGradientResistiveQualificationGenericReceiptNonPromoting =
  refl

canonicalFormalLensQualificationGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalFormalLensQualificationGenericReceipts =
  canonicalGenericFormalLensQualificationGenericReceipt
  ∷ canonicalGradientResistiveQualificationGenericReceipt
  ∷ []

canonicalFormalLensQualificationGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting
    canonicalFormalLensQualificationGenericReceipts
canonicalFormalLensQualificationGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalFormalLensQualificationGenericReceipts
