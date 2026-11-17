module DASHI.Interop.MeditationQiBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.CandidateFunctionalCore as FunctionalCore
import DASHI.Core.AdapterCanonicalityCore as AdapterCanon
import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Core.FormalLensQualificationCore as FormalLensCore
import DASHI.Core.OperatorShapeNonAuthorityCore as OperatorShapeNA
import DASHI.Interop.InterMediaCarrierBridge as IM
import DASHI.Interop.QiCarrierFieldBridge as Qi
import DASHI.Promotion.AuthorityBoundaryCore as AuthorityBoundaryCore

open FormalLensCore
  using
    ( FormalLens
    ; SymbolicRational
    ; Operator
    ; Functional
    ; Hamiltonian
    ; GradientFlow
    ; ResistiveTransport
    ; Spectral
    ; Category
    )

------------------------------------------------------------------------
-- Meditation as inner carrier-field governance.
--
-- This is an interpretive receipt surface.  It records attention, breath,
-- awareness, grounding, labeling, and compassion operators as candidate
-- carrier-field governance rows.  It does not establish clinical safety,
-- metaphysical truth, admissibility, or reciprocal-practice authority.

data MindCarrier : Set where
  mindCarrier :
    MindCarrier

data AttentionField : Set where
  focusedAttentionField :
    AttentionField

  openAttentionField :
    AttentionField

data BreathField : Set where
  breathRhythmField :
    BreathField

data BodySensationField : Set where
  embodiedSensationField :
    BodySensationField

data ThoughtStream : Set where
  arisingThoughtStream :
    ThoughtStream

data AffectField : Set where
  valenceAffectField :
    AffectField

data AwarenessBoundary : Set where
  boundedAwarenessBoundary :
    AwarenessBoundary

  openAwarenessBoundary :
    AwarenessBoundary

data ResidualField : Set where
  residualMindNoiseField :
    ResidualField

data IntentionYi : Set where
  nonForcingIntentionYi :
    IntentionYi

record MeditationState : Set where
  constructor meditationState
  field
    mindCarrierField :
      MindCarrier

    attentionField :
      AttentionField

    breathField :
      BreathField

    bodySensationField :
      BodySensationField

    thoughtStream :
      ThoughtStream

    affectField :
      AffectField

    awarenessBoundary :
      AwarenessBoundary

    residualField :
      ResidualField

    intentionYi :
      IntentionYi

open MeditationState public

canonicalMeditationState : MeditationState
canonicalMeditationState =
  meditationState
    mindCarrier
    openAttentionField
    breathRhythmField
    embodiedSensationField
    arisingThoughtStream
    valenceAffectField
    openAwarenessBoundary
    residualMindNoiseField
    nonForcingIntentionYi

data FlowStateDimension : Set where
  intensityDimension :
    FlowStateDimension

  directionDimension :
    FlowStateDimension

  velocityDimension :
    FlowStateDimension

  coherenceDimension :
    FlowStateDimension

  stickinessDimension :
    FlowStateDimension

  spaciousnessDimension :
    FlowStateDimension

  valenceDimension :
    FlowStateDimension

  recurrenceDimension :
    FlowStateDimension

  embodimentDimension :
    FlowStateDimension

  renewalDimension :
    FlowStateDimension

canonicalFlowStateDimensions : List FlowStateDimension
canonicalFlowStateDimensions =
  intensityDimension
  ∷ directionDimension
  ∷ velocityDimension
  ∷ coherenceDimension
  ∷ stickinessDimension
  ∷ spaciousnessDimension
  ∷ valenceDimension
  ∷ recurrenceDimension
  ∷ embodimentDimension
  ∷ renewalDimension
  ∷ []

data MeditationOperator : Set where
  breathAnchorOperator :
    MeditationOperator

  bodyScanOperator :
    MeditationOperator

  openMonitoringOperator :
    MeditationOperator

  mettaOperator :
    MeditationOperator

  labelingOperator :
    MeditationOperator

  notingOperator :
    MeditationOperator

  concentrationOperator :
    MeditationOperator

  inquiryOperator :
    MeditationOperator

  groundingOperator :
    MeditationOperator

  equanimityOperator :
    MeditationOperator

  releaseOperator :
    MeditationOperator

canonicalMeditationOperators : List MeditationOperator
canonicalMeditationOperators =
  breathAnchorOperator
  ∷ bodyScanOperator
  ∷ openMonitoringOperator
  ∷ mettaOperator
  ∷ labelingOperator
  ∷ notingOperator
  ∷ concentrationOperator
  ∷ inquiryOperator
  ∷ groundingOperator
  ∷ equanimityOperator
  ∷ releaseOperator
  ∷ []

data MeditationHamiltonianTerm : Set where
  agitationTerm :
    MeditationHamiltonianTerm

  dullnessTerm :
    MeditationHamiltonianTerm

  dissociationTerm :
    MeditationHamiltonianTerm

  ruminationTerm :
    MeditationHamiltonianTerm

  compulsiveGraspingTerm :
    MeditationHamiltonianTerm

  avoidanceTerm :
    MeditationHamiltonianTerm

  affectFloodingTerm :
    MeditationHamiltonianTerm

  selfAttackTerm :
    MeditationHamiltonianTerm

  clarityCreditTerm :
    MeditationHamiltonianTerm

  embodimentCreditTerm :
    MeditationHamiltonianTerm

  equanimityCreditTerm :
    MeditationHamiltonianTerm

  compassionCreditTerm :
    MeditationHamiltonianTerm

  renewalCreditTerm :
    MeditationHamiltonianTerm

canonicalMeditationHamiltonianTerms :
  List MeditationHamiltonianTerm
canonicalMeditationHamiltonianTerms =
  agitationTerm
  ∷ dullnessTerm
  ∷ dissociationTerm
  ∷ ruminationTerm
  ∷ compulsiveGraspingTerm
  ∷ avoidanceTerm
  ∷ affectFloodingTerm
  ∷ selfAttackTerm
  ∷ clarityCreditTerm
  ∷ embodimentCreditTerm
  ∷ equanimityCreditTerm
  ∷ compassionCreditTerm
  ∷ renewalCreditTerm
  ∷ []

data MeditationSpectralMode : Set where
  ruminationMode :
    MeditationSpectralMode

  intrusionMode :
    MeditationSpectralMode

  dullnessMode :
    MeditationSpectralMode

  bodyPresenceMode :
    MeditationSpectralMode

  breathRhythmMode :
    MeditationSpectralMode

  selfAttackMode :
    MeditationSpectralMode

  openAwarenessMode :
    MeditationSpectralMode

  compassionMode :
    MeditationSpectralMode

canonicalMeditationSpectralModes : List MeditationSpectralMode
canonicalMeditationSpectralModes =
  ruminationMode
  ∷ intrusionMode
  ∷ dullnessMode
  ∷ bodyPresenceMode
  ∷ breathRhythmMode
  ∷ selfAttackMode
  ∷ openAwarenessMode
  ∷ compassionMode
  ∷ []

data MeditationBoundaryGate : Set where
  breathAnchorGate :
    MeditationBoundaryGate

  bodySensationGate :
    MeditationBoundaryGate

  openAwarenessGate :
    MeditationBoundaryGate

  traumaContentGate :
    MeditationBoundaryGate

  groundingGate :
    MeditationBoundaryGate

canonicalMeditationBoundaryGates : List MeditationBoundaryGate
canonicalMeditationBoundaryGates =
  breathAnchorGate
  ∷ bodySensationGate
  ∷ openAwarenessGate
  ∷ traumaContentGate
  ∷ groundingGate
  ∷ []

data MeditationSafetyRoute : Set where
  observeLabelMetaboliseRoute :
    MeditationSafetyRoute

  groundNarrowOpenEyesMoveSeekSupportRoute :
    MeditationSafetyRoute

  refuseDeepeningReturnExternalCarrierRoute :
    MeditationSafetyRoute

canonicalMeditationSafetyRoutes : List MeditationSafetyRoute
canonicalMeditationSafetyRoutes =
  observeLabelMetaboliseRoute
  ∷ groundNarrowOpenEyesMoveSeekSupportRoute
  ∷ refuseDeepeningReturnExternalCarrierRoute
  ∷ []

------------------------------------------------------------------------
-- Formal-lens qualification adapter surface.

MeditationFormalLens : Set
MeditationFormalLens =
  FormalLens

canonicalMeditationFormalLenses : List MeditationFormalLens
canonicalMeditationFormalLenses =
  SymbolicRational
  ∷ Operator
  ∷ Functional
  ∷ Hamiltonian
  ∷ GradientFlow
  ∷ ResistiveTransport
  ∷ Spectral
  ∷ Category
  ∷ []

meditationFormalLensCandidateOnlyRow :
  CandidateOnly.CandidateOnlyRow
meditationFormalLensCandidateOnlyRow =
  CandidateOnly.mkCandidateOnlyRow
    "meditation formal-lens qualification candidate"
    "DASHI.Interop.MeditationQiBridge"
    "MeditationFormalLensQualificationSurface"
    (CandidateOnly.namedCandidateKind "formal-lens qualification")
    (CandidateOnly.namedCandidateOnlyStatus "formal-lens qualification")
    "Meditation attention, operator, Hamiltonian, functional, spectral, and gradient-flow readings are symbolic-rational candidate lenses only."
    "Clinical, spiritual, metaphysical, analytic Hamiltonian, spectral theorem, empirical, theorem, Clay, and promotion authority remain outside this adapter."

meditationFormalLensCandidateOnlyReceipt :
  CandidateOnly.CandidateOnlyReceipt
    meditationFormalLensCandidateOnlyRow
meditationFormalLensCandidateOnlyReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    meditationFormalLensCandidateOnlyRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

meditationFormalLensAuthorityNonPromotionBundle :
  AuthorityNA.AuthorityNonPromotionBundle
meditationFormalLensAuthorityNonPromotionBundle =
  AuthorityNA.mkClosedAuthorityNonPromotionBundle
    "meditation formal-lens qualification authority non-promotion adapter"

meditationFormalLensAuthorityNonPromotionAllFalse :
  AuthorityNA.AllAuthorityKindsFalse
    meditationFormalLensAuthorityNonPromotionBundle
    AuthorityNA.canonicalAuthorityKinds
meditationFormalLensAuthorityNonPromotionAllFalse =
  AuthorityNA.proveAllAuthorityKindsFalse
    meditationFormalLensAuthorityNonPromotionBundle
    AuthorityNA.canonicalAuthorityKinds

meditationFormalLensListCanonicalityReceipt :
  AdapterCanon.AdapterCanonicalityReceipt
    (List MeditationFormalLens)
    canonicalMeditationFormalLenses
meditationFormalLensListCanonicalityReceipt =
  AdapterCanon.mkCanonicalAdapterReceipt
    "meditation formal-lens list canonicality"
    "DASHI.Interop.MeditationQiBridge"
    "canonicalMeditationFormalLenses"
    (AdapterCanon.namedAdapterKind "formal-lens list")
    canonicalMeditationFormalLenses

meditationAttentionOperatorFormalLensCoreSurface :
  FormalLensCore.FormalLensQualificationSurface
meditationAttentionOperatorFormalLensCoreSurface =
  FormalLensCore.mkFormalLensQualificationSurface
    "meditation attention operator formal-lens qualification"
    "DASHI.Interop.MeditationQiBridge"
    "meditationAttentionOperatorFormalLensCoreSurface"
    SymbolicRational
    Operator
    FormalLensCore.adapterConsumerRole
    FormalLensCore.canonicalRequiredThresholdRow
    FormalLensCore.canonicalRequiredThresholdRowReceipt
    FormalLensCore.explicitAdapterResidualBoundary
    meditationFormalLensCandidateOnlyRow
    meditationFormalLensCandidateOnlyReceipt
    FormalLensCore.genericFormalLensBridgeRow
    FormalLensCore.genericFormalLensBridgeReceipt
    "Meditation attention/operator readings are symbolic-rational formal-lens qualifications only."
    "No analytic Hamiltonian, spectral theorem, empirical, clinical, spiritual, metaphysical, theorem, Clay, governance, or promotion authority is supplied."

meditationAttentionOperatorFormalLensCoreReceipt :
  FormalLensCore.FormalLensQualificationReceipt
    meditationAttentionOperatorFormalLensCoreSurface
meditationAttentionOperatorFormalLensCoreReceipt =
  FormalLensCore.mkFormalLensQualificationReceipt
    meditationAttentionOperatorFormalLensCoreSurface
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

record MeditationFormalLensQualificationSurface : Set where
  constructor meditationFormalLensQualificationSurface
  field
    candidateOnlyCoreAdapter :
      CandidateOnly.CandidateOnlyReceipt
        meditationFormalLensCandidateOnlyRow

    candidateOnlyCoreAdapterIsCanonical :
      candidateOnlyCoreAdapter
      ≡
      meditationFormalLensCandidateOnlyReceipt

    authorityNonPromotionCoreAdapter :
      AuthorityNA.AuthorityNonPromotionBundle

    authorityNonPromotionCoreAdapterIsCanonical :
      authorityNonPromotionCoreAdapter
      ≡
      meditationFormalLensAuthorityNonPromotionBundle

    authorityNonPromotionCoreAdapterAllFalse :
      AuthorityNA.AllAuthorityKindsFalse
        authorityNonPromotionCoreAdapter
        AuthorityNA.canonicalAuthorityKinds

    formalLensCanonicalityAdapter :
      AdapterCanon.AdapterCanonicalityReceipt
        (List MeditationFormalLens)
        canonicalMeditationFormalLenses

    formalLensCanonicalityAdapterIsCanonical :
      formalLensCanonicalityAdapter
      ≡
      meditationFormalLensListCanonicalityReceipt

    formalLensQualificationCoreAdapter :
      FormalLensCore.FormalLensQualificationSurface

    formalLensQualificationCoreAdapterIsCanonical :
      formalLensQualificationCoreAdapter
      ≡
      meditationAttentionOperatorFormalLensCoreSurface

    formalLensQualificationCoreReceipt :
      FormalLensCore.FormalLensQualificationReceipt
        formalLensQualificationCoreAdapter

    formalLensReadings :
      List MeditationFormalLens

    formalLensReadingsAreCanonical :
      formalLensReadings ≡ canonicalMeditationFormalLenses

    symbolicRationalReading :
      MeditationFormalLens

    symbolicRationalReadingIsCanonical :
      symbolicRationalReading ≡ SymbolicRational

    attentionOperatorReading :
      MeditationFormalLens

    attentionOperatorReadingIsCanonical :
      attentionOperatorReading ≡ Operator

    meditationFunctionalReading :
      MeditationFormalLens

    meditationFunctionalReadingIsCanonical :
      meditationFunctionalReading ≡ Functional

    meditationHamiltonianReading :
      MeditationFormalLens

    meditationHamiltonianReadingIsCanonical :
      meditationHamiltonianReading ≡ Hamiltonian

    meditationGradientFlowReading :
      MeditationFormalLens

    meditationGradientFlowReadingIsCanonical :
      meditationGradientFlowReading ≡ GradientFlow

    meditationResistiveTransportReading :
      MeditationFormalLens

    meditationResistiveTransportReadingIsCanonical :
      meditationResistiveTransportReading ≡ ResistiveTransport

    meditationSpectralReading :
      MeditationFormalLens

    meditationSpectralReadingIsCanonical :
      meditationSpectralReading ≡ Spectral

    meditationCategoryReading :
      MeditationFormalLens

    meditationCategoryReadingIsCanonical :
      meditationCategoryReading ≡ Category

    formalLensCandidateOnly :
      Bool

    formalLensCandidateOnlyIsTrue :
      formalLensCandidateOnly ≡ true

    formalLensSymbolicRationalOnly :
      Bool

    formalLensSymbolicRationalOnlyIsTrue :
      formalLensSymbolicRationalOnly ≡ true

    formalLensClinicalAuthorityPromoted :
      Bool

    formalLensClinicalAuthorityPromotedIsFalse :
      formalLensClinicalAuthorityPromoted ≡ false

    formalLensSpiritualAuthorityPromoted :
      Bool

    formalLensSpiritualAuthorityPromotedIsFalse :
      formalLensSpiritualAuthorityPromoted ≡ false

    formalLensMetaphysicalAuthorityPromoted :
      Bool

    formalLensMetaphysicalAuthorityPromotedIsFalse :
      formalLensMetaphysicalAuthorityPromoted ≡ false

    formalLensAnalyticHamiltonianAuthorityPromoted :
      Bool

    formalLensAnalyticHamiltonianAuthorityPromotedIsFalse :
      formalLensAnalyticHamiltonianAuthorityPromoted ≡ false

    formalLensSpectralTheoremAuthorityPromoted :
      Bool

    formalLensSpectralTheoremAuthorityPromotedIsFalse :
      formalLensSpectralTheoremAuthorityPromoted ≡ false

    formalLensEmpiricalAuthorityPromoted :
      Bool

    formalLensEmpiricalAuthorityPromotedIsFalse :
      formalLensEmpiricalAuthorityPromoted ≡ false

    formalLensTheoremAuthorityPromoted :
      Bool

    formalLensTheoremAuthorityPromotedIsFalse :
      formalLensTheoremAuthorityPromoted ≡ false

    formalLensClayAuthorityPromoted :
      Bool

    formalLensClayAuthorityPromotedIsFalse :
      formalLensClayAuthorityPromoted ≡ false

    formalLensPromotionAuthorityPromoted :
      Bool

    formalLensPromotionAuthorityPromotedIsFalse :
      formalLensPromotionAuthorityPromoted ≡ false

open MeditationFormalLensQualificationSurface public

canonicalMeditationFormalLensQualificationSurface :
  MeditationFormalLensQualificationSurface
canonicalMeditationFormalLensQualificationSurface =
  meditationFormalLensQualificationSurface
    meditationFormalLensCandidateOnlyReceipt
    refl
    meditationFormalLensAuthorityNonPromotionBundle
    refl
    meditationFormalLensAuthorityNonPromotionAllFalse
    meditationFormalLensListCanonicalityReceipt
    refl
    meditationAttentionOperatorFormalLensCoreSurface
    refl
    meditationAttentionOperatorFormalLensCoreReceipt
    canonicalMeditationFormalLenses
    refl
    SymbolicRational
    refl
    Operator
    refl
    Functional
    refl
    Hamiltonian
    refl
    GradientFlow
    refl
    ResistiveTransport
    refl
    Spectral
    refl
    Category
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalMeditationFormalLensQualificationAdapterCanonicality :
  AdapterCanon.AdapterCanonicalityReceipt
    MeditationFormalLensQualificationSurface
    canonicalMeditationFormalLensQualificationSurface
canonicalMeditationFormalLensQualificationAdapterCanonicality =
  AdapterCanon.mkCanonicalAdapterReceipt
    "meditation formal-lens qualification surface canonicality"
    "DASHI.Interop.MeditationQiBridge"
    "canonicalMeditationFormalLensQualificationSurface"
    (AdapterCanon.namedAdapterKind "formal-lens qualification surface")
    canonicalMeditationFormalLensQualificationSurface

data MeditationPromotion : Set where

meditationPromotionImpossible :
  MeditationPromotion →
  ⊥
meditationPromotionImpossible ()

record SweetgrassMeditationGate : Set where
  constructor sweetgrassMeditationGate
  field
    innerShengMindQi :
      Bool

    outerReciprocalPractice :
      Bool

    fullAdmission :
      Bool

    innerShengMindQiRecorded :
      innerShengMindQi ≡ true

    outerReciprocalPracticeNotSupplied :
      outerReciprocalPractice ≡ false

    fullAdmissionFalseWithoutOuterGate :
      fullAdmission ≡ false

open SweetgrassMeditationGate public

canonicalSweetgrassMeditationGate : SweetgrassMeditationGate
canonicalSweetgrassMeditationGate =
  sweetgrassMeditationGate true false false refl refl refl

record MeditationAuthorityBoundarySurface : Set where
  constructor meditationAuthorityBoundarySurface
  field
    authorityBoundarySurfaceReceipt :
      AuthorityBoundaryCore.AuthorityBoundaryReceipt

    authorityBoundarySurfaceReceiptIsCanonical :
      authorityBoundarySurfaceReceipt ≡
      AuthorityBoundaryCore.canonicalRuntimeAuthorityBoundaryReceipt

    authorityBoundarySurfaceCandidateOnlyTrue :
      CandidateOnly.candidateOnly
        (AuthorityBoundaryCore.receiptCandidateRow
          authorityBoundarySurfaceReceipt)
      ≡ true

    authorityBoundarySurfaceBundlePromotesAnyAuthorityFalse :
      AuthorityNA.promotesAnyAuthority
        (AuthorityBoundaryCore.receiptAuthorityBundle
          authorityBoundarySurfaceReceipt)
      ≡ false

    authorityBoundarySurfacePromoted :
      Bool

    authorityBoundarySurfacePromotedIsFalse :
      authorityBoundarySurfacePromoted ≡ false

    authorityBoundarySurfaceBlockedAuthorityKinds :
      List AuthorityNA.AuthorityKind

    authorityBoundarySurfaceBlockedAuthorityKindsAreCanonical :
      authorityBoundarySurfaceBlockedAuthorityKinds ≡
      AuthorityNA.canonicalAuthorityKinds

    authorityBoundarySurfaceBlockedAuthorityKindsFalse :
      AuthorityNA.AllAuthorityKindsFalse
        (AuthorityBoundaryCore.receiptAuthorityBundle
          authorityBoundarySurfaceReceipt)
        authorityBoundarySurfaceBlockedAuthorityKinds

    authorityBoundarySurfaceTruthAuthorityPromoted :
      Bool

    authorityBoundarySurfaceTruthAuthorityPromotedIsFalse :
      authorityBoundarySurfaceTruthAuthorityPromoted ≡ false

    authorityBoundarySurfaceClinicalAuthorityPromoted :
      Bool

    authorityBoundarySurfaceClinicalAuthorityPromotedIsFalse :
      authorityBoundarySurfaceClinicalAuthorityPromoted ≡ false

    authorityBoundarySurfaceMetaphysicalAuthorityPromoted :
      Bool

    authorityBoundarySurfaceMetaphysicalAuthorityPromotedIsFalse :
      authorityBoundarySurfaceMetaphysicalAuthorityPromoted ≡ false

    authorityBoundarySurfaceReciprocalPracticeAuthorityPromoted :
      Bool

    authorityBoundarySurfaceReciprocalPracticeAuthorityPromotedIsFalse :
      authorityBoundarySurfaceReciprocalPracticeAuthorityPromoted ≡ false

open MeditationAuthorityBoundarySurface public

canonicalMeditationAuthorityBoundarySurface :
  MeditationAuthorityBoundarySurface
canonicalMeditationAuthorityBoundarySurface =
  meditationAuthorityBoundarySurface
    AuthorityBoundaryCore.canonicalRuntimeAuthorityBoundaryReceipt
    refl
    (AuthorityBoundaryCore.authorityBoundaryCandidateOnlyIsTrue
      AuthorityBoundaryCore.canonicalRuntimeAuthorityBoundaryReceipt)
    (AuthorityBoundaryCore.authorityBoundaryBundlePromotesAnyAuthorityIsFalse
      AuthorityBoundaryCore.canonicalRuntimeAuthorityBoundaryReceipt)
    false
    refl
    AuthorityNA.canonicalAuthorityKinds
    refl
    (AuthorityBoundaryCore.authorityBoundaryBlockedAuthorityKindsFalse
      AuthorityBoundaryCore.canonicalRuntimeAuthorityBoundaryReceipt)
    false
    refl
    false
    refl
    false
    refl
    false
    refl

record MeditationQiBridgeReceipt : Set where
  constructor meditationQiBridgeReceipt
  field
    interMediaAdapter :
      IM.InterMediaCarrierBridgeReceipt

    interMediaAdapterIsCanonical :
      interMediaAdapter ≡ IM.canonicalInterMediaCarrierBridgeReceipt

    qiCarrierAdapter :
      Qi.QiCarrierFieldBridgeReceipt

    qiCarrierAdapterIsCanonical :
      qiCarrierAdapter ≡ Qi.canonicalQiCarrierFieldBridgeReceipt

    candidateFunctionalCoreAdapter :
      FunctionalCore.CandidateFunctionalSurface

    candidateFunctionalCoreAdapterIsCanonical :
      candidateFunctionalCoreAdapter
      ≡
      FunctionalCore.canonicalMeditationLikeFunctionalSurface

    operatorShapeNonAuthorityCoreAdapter :
      OperatorShapeNA.OperatorShapeCandidateReceipt

    operatorShapeNonAuthorityCoreAdapterIsCanonical :
      operatorShapeNonAuthorityCoreAdapter
      ≡
      OperatorShapeNA.canonicalOperatorShapeCandidateReceipt

    formalLensQualificationAdapter :
      MeditationFormalLensQualificationSurface

    formalLensQualificationAdapterIsCanonical :
      formalLensQualificationAdapter
      ≡
      canonicalMeditationFormalLensQualificationSurface

    formalLensQualificationAdapterCanonicalityCore :
      AdapterCanon.AdapterCanonicalityReceipt
        MeditationFormalLensQualificationSurface
        canonicalMeditationFormalLensQualificationSurface

    formalLensQualificationAdapterCanonicalityCoreIsCanonical :
      formalLensQualificationAdapterCanonicalityCore
      ≡
      canonicalMeditationFormalLensQualificationAdapterCanonicality

    meditationStateSnapshot :
      MeditationState

    meditationStateSnapshotIsCanonical :
      meditationStateSnapshot ≡ canonicalMeditationState

    flowStateDimensions :
      List FlowStateDimension

    flowStateDimensionsAreCanonical :
      flowStateDimensions ≡ canonicalFlowStateDimensions

    operators :
      List MeditationOperator

    operatorsAreCanonical :
      operators ≡ canonicalMeditationOperators

    hamiltonianTerms :
      List MeditationHamiltonianTerm

    hamiltonianTermsAreCanonical :
      hamiltonianTerms ≡ canonicalMeditationHamiltonianTerms

    spectralModes :
      List MeditationSpectralMode

    spectralModesAreCanonical :
      spectralModes ≡ canonicalMeditationSpectralModes

    boundaryGates :
      List MeditationBoundaryGate

    boundaryGatesAreCanonical :
      boundaryGates ≡ canonicalMeditationBoundaryGates

    safetyRoutes :
      List MeditationSafetyRoute

    safetyRoutesAreCanonical :
      safetyRoutes ≡ canonicalMeditationSafetyRoutes

    sweetgrassGate :
      SweetgrassMeditationGate

    sweetgrassGateIsCanonical :
      sweetgrassGate ≡ canonicalSweetgrassMeditationGate

    reducesFusionOperatorRecorded :
      Bool

    reducesFusionOperatorRecordedIsTrue :
      reducesFusionOperatorRecorded ≡ true

    clinicalAuthorityPromoted :
      Bool

    clinicalAuthorityPromotedIsFalse :
      clinicalAuthorityPromoted ≡ false

    metaphysicalAuthorityPromoted :
      Bool

    metaphysicalAuthorityPromotedIsFalse :
      metaphysicalAuthorityPromoted ≡ false

    truthAuthorityPromoted :
      Bool

    truthAuthorityPromotedIsFalse :
      truthAuthorityPromoted ≡ false

    reciprocalPracticeAuthorityPromoted :
      Bool

    reciprocalPracticeAuthorityPromotedIsFalse :
      reciprocalPracticeAuthorityPromoted ≡ false

    promotions :
      List MeditationPromotion

    promotionsEmpty :
      promotions ≡ []

    promotionImpossible :
      MeditationPromotion →
      ⊥

open MeditationQiBridgeReceipt public

canonicalMeditationQiBridgeReceipt : MeditationQiBridgeReceipt
canonicalMeditationQiBridgeReceipt =
  meditationQiBridgeReceipt
    IM.canonicalInterMediaCarrierBridgeReceipt
    refl
    Qi.canonicalQiCarrierFieldBridgeReceipt
    refl
    FunctionalCore.canonicalMeditationLikeFunctionalSurface
    refl
    OperatorShapeNA.canonicalOperatorShapeCandidateReceipt
    refl
    canonicalMeditationFormalLensQualificationSurface
    refl
    canonicalMeditationFormalLensQualificationAdapterCanonicality
    refl
    canonicalMeditationState
    refl
    canonicalFlowStateDimensions
    refl
    canonicalMeditationOperators
    refl
    canonicalMeditationHamiltonianTerms
    refl
    canonicalMeditationSpectralModes
    refl
    canonicalMeditationBoundaryGates
    refl
    canonicalMeditationSafetyRoutes
    refl
    canonicalSweetgrassMeditationGate
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    []
    refl
    meditationPromotionImpossible

canonicalMeditationQiInterMediaCanonical :
  interMediaAdapter canonicalMeditationQiBridgeReceipt
  ≡
  IM.canonicalInterMediaCarrierBridgeReceipt
canonicalMeditationQiInterMediaCanonical =
  refl

canonicalMeditationQiQiCarrierCanonical :
  qiCarrierAdapter canonicalMeditationQiBridgeReceipt
  ≡
  Qi.canonicalQiCarrierFieldBridgeReceipt
canonicalMeditationQiQiCarrierCanonical =
  refl

canonicalMeditationQiFunctionalCoreCanonical :
  candidateFunctionalCoreAdapter canonicalMeditationQiBridgeReceipt
  ≡
  FunctionalCore.canonicalMeditationLikeFunctionalSurface
canonicalMeditationQiFunctionalCoreCanonical =
  refl

canonicalMeditationQiFunctionalCoreClinicalAuthorityFalse :
  FunctionalCore.clinicalAuthority
    (candidateFunctionalCoreAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  false
canonicalMeditationQiFunctionalCoreClinicalAuthorityFalse =
  refl

canonicalMeditationQiOperatorShapeCoreCanonical :
  operatorShapeNonAuthorityCoreAdapter canonicalMeditationQiBridgeReceipt
  ≡
  OperatorShapeNA.canonicalOperatorShapeCandidateReceipt
canonicalMeditationQiOperatorShapeCoreCanonical =
  refl

canonicalMeditationQiOperatorShapeTheoremAuthorityFalse :
  OperatorShapeNA.actualTheoremAuthority
    (operatorShapeNonAuthorityCoreAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  false
canonicalMeditationQiOperatorShapeTheoremAuthorityFalse =
  refl

canonicalMeditationQiFormalLensAdapterCanonical :
  formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt
  ≡
  canonicalMeditationFormalLensQualificationSurface
canonicalMeditationQiFormalLensAdapterCanonical =
  refl

canonicalMeditationQiFormalLensCandidateOnly :
  formalLensCandidateOnly
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  true
canonicalMeditationQiFormalLensCandidateOnly =
  refl

canonicalMeditationQiFormalLensSymbolicRationalOnly :
  formalLensSymbolicRationalOnly
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  true
canonicalMeditationQiFormalLensSymbolicRationalOnly =
  refl

canonicalMeditationQiFormalLensCandidateCoreCandidateOnly :
  CandidateOnly.candidateOnly meditationFormalLensCandidateOnlyRow
  ≡
  true
canonicalMeditationQiFormalLensCandidateCoreCandidateOnly =
  CandidateOnly.candidateOnlyIsTrue
    (candidateOnlyCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))

canonicalMeditationQiFormalLensCandidateCorePromotedFalse :
  CandidateOnly.promoted meditationFormalLensCandidateOnlyRow
  ≡
  false
canonicalMeditationQiFormalLensCandidateCorePromotedFalse =
  CandidateOnly.candidatePromotedIsFalse
    (candidateOnlyCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))

canonicalMeditationQiFormalLensAdapterCanonicalityPromotionFalse :
  AdapterCanon.adapterPromotesAuthority
    (formalLensQualificationAdapterCanonicalityCore
      canonicalMeditationQiBridgeReceipt)
  ≡
  false
canonicalMeditationQiFormalLensAdapterCanonicalityPromotionFalse =
  refl

canonicalMeditationQiFormalLensCoreAdapterCanonical :
  formalLensQualificationCoreAdapter
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  meditationAttentionOperatorFormalLensCoreSurface
canonicalMeditationQiFormalLensCoreAdapterCanonical =
  refl

canonicalMeditationQiFormalLensCoreSourceSymbolicRational :
  FormalLensCore.sourceLens
    (formalLensQualificationCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  SymbolicRational
canonicalMeditationQiFormalLensCoreSourceSymbolicRational =
  refl

canonicalMeditationQiFormalLensCoreTargetOperator :
  FormalLensCore.targetLens
    (formalLensQualificationCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  Operator
canonicalMeditationQiFormalLensCoreTargetOperator =
  refl

canonicalMeditationQiFormalLensCoreCandidateOnly :
  FormalLensCore.qualificationCandidateOnly
    (formalLensQualificationCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  true
canonicalMeditationQiFormalLensCoreCandidateOnly =
  FormalLensCore.qualificationIsCandidateOnly
    (formalLensQualificationCoreReceipt
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))

canonicalMeditationQiFormalLensCorePromotedFalse :
  FormalLensCore.qualificationPromoted
    (formalLensQualificationCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  false
canonicalMeditationQiFormalLensCorePromotedFalse =
  FormalLensCore.qualificationPromotedFalse
    (formalLensQualificationCoreReceipt
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))

canonicalMeditationQiFormalLensCoreAnalyticAuthorityFalse :
  FormalLensCore.analyticAuthority
    (formalLensQualificationCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  false
canonicalMeditationQiFormalLensCoreAnalyticAuthorityFalse =
  FormalLensCore.qualificationAnalyticAuthorityFalse
    (formalLensQualificationCoreReceipt
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))

canonicalMeditationQiFormalLensCoreEmpiricalAuthorityFalse :
  FormalLensCore.empiricalAuthority
    (formalLensQualificationCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  false
canonicalMeditationQiFormalLensCoreEmpiricalAuthorityFalse =
  FormalLensCore.qualificationEmpiricalAuthorityFalse
    (formalLensQualificationCoreReceipt
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))

canonicalMeditationQiFormalLensCoreClinicalAuthorityFalse :
  FormalLensCore.clinicalAuthority
    (formalLensQualificationCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  false
canonicalMeditationQiFormalLensCoreClinicalAuthorityFalse =
  FormalLensCore.qualificationClinicalAuthorityFalse
    (formalLensQualificationCoreReceipt
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))

canonicalMeditationQiFormalLensCoreTheoremAuthorityFalse :
  FormalLensCore.theoremAuthority
    (formalLensQualificationCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  false
canonicalMeditationQiFormalLensCoreTheoremAuthorityFalse =
  FormalLensCore.qualificationTheoremAuthorityFalse
    (formalLensQualificationCoreReceipt
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))

canonicalMeditationQiFormalLensCoreMetaphysicalAuthorityFalse :
  FormalLensCore.metaphysicalAuthority
    (formalLensQualificationCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  false
canonicalMeditationQiFormalLensCoreMetaphysicalAuthorityFalse =
  FormalLensCore.qualificationMetaphysicalAuthorityFalse
    (formalLensQualificationCoreReceipt
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))

canonicalMeditationQiFormalLensCorePromotionAuthorityFalse :
  FormalLensCore.promotionAuthority
    (formalLensQualificationCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  false
canonicalMeditationQiFormalLensCorePromotionAuthorityFalse =
  FormalLensCore.qualificationPromotionAuthorityFalse
    (formalLensQualificationCoreReceipt
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))

canonicalMeditationQiFormalLensAttentionOperator :
  attentionOperatorReading
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  Operator
canonicalMeditationQiFormalLensAttentionOperator =
  refl

canonicalMeditationQiFormalLensHamiltonian :
  meditationHamiltonianReading
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  Hamiltonian
canonicalMeditationQiFormalLensHamiltonian =
  refl

canonicalMeditationQiFormalLensFunctional :
  meditationFunctionalReading
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  Functional
canonicalMeditationQiFormalLensFunctional =
  refl

canonicalMeditationQiFormalLensSpectral :
  meditationSpectralReading
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  Spectral
canonicalMeditationQiFormalLensSpectral =
  refl

canonicalMeditationQiFormalLensGradientFlow :
  meditationGradientFlowReading
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  GradientFlow
canonicalMeditationQiFormalLensGradientFlow =
  refl

canonicalMeditationQiFormalLensClinicalAuthorityFalse :
  formalLensClinicalAuthorityPromoted
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  false
canonicalMeditationQiFormalLensClinicalAuthorityFalse =
  refl

canonicalMeditationQiFormalLensSpiritualAuthorityFalse :
  formalLensSpiritualAuthorityPromoted
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  false
canonicalMeditationQiFormalLensSpiritualAuthorityFalse =
  refl

canonicalMeditationQiFormalLensMetaphysicalAuthorityFalse :
  formalLensMetaphysicalAuthorityPromoted
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  false
canonicalMeditationQiFormalLensMetaphysicalAuthorityFalse =
  refl

canonicalMeditationQiFormalLensAnalyticHamiltonianAuthorityFalse :
  formalLensAnalyticHamiltonianAuthorityPromoted
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  false
canonicalMeditationQiFormalLensAnalyticHamiltonianAuthorityFalse =
  refl

canonicalMeditationQiFormalLensSpectralTheoremAuthorityFalse :
  formalLensSpectralTheoremAuthorityPromoted
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  false
canonicalMeditationQiFormalLensSpectralTheoremAuthorityFalse =
  refl

canonicalMeditationQiFormalLensEmpiricalAuthorityFalse :
  formalLensEmpiricalAuthorityPromoted
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  false
canonicalMeditationQiFormalLensEmpiricalAuthorityFalse =
  refl

canonicalMeditationQiFormalLensTheoremAuthorityFalse :
  formalLensTheoremAuthorityPromoted
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  false
canonicalMeditationQiFormalLensTheoremAuthorityFalse =
  refl

canonicalMeditationQiFormalLensClayAuthorityFalse :
  formalLensClayAuthorityPromoted
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  false
canonicalMeditationQiFormalLensClayAuthorityFalse =
  refl

canonicalMeditationQiFormalLensPromotionAuthorityFalse :
  formalLensPromotionAuthorityPromoted
    (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt)
  ≡
  false
canonicalMeditationQiFormalLensPromotionAuthorityFalse =
  refl

canonicalMeditationQiFormalLensAuthorityCoreClinicalFalse :
  AuthorityNA.clinicalAuthorityFlag
    (authorityNonPromotionCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  false
canonicalMeditationQiFormalLensAuthorityCoreClinicalFalse =
  refl

canonicalMeditationQiFormalLensAuthorityCoreSpiritualFalse :
  AuthorityNA.spiritualAuthorityFlag
    (authorityNonPromotionCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  false
canonicalMeditationQiFormalLensAuthorityCoreSpiritualFalse =
  refl

canonicalMeditationQiFormalLensAuthorityCoreMetaphysicalFalse :
  AuthorityNA.metaphysicalAuthorityFlag
    (authorityNonPromotionCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  false
canonicalMeditationQiFormalLensAuthorityCoreMetaphysicalFalse =
  refl

canonicalMeditationQiFormalLensAuthorityCoreTheoremFalse :
  AuthorityNA.theoremAuthorityFlag
    (authorityNonPromotionCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  false
canonicalMeditationQiFormalLensAuthorityCoreTheoremFalse =
  refl

canonicalMeditationQiFormalLensAuthorityCoreClayFalse :
  AuthorityNA.clayAuthorityFlag
    (authorityNonPromotionCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  false
canonicalMeditationQiFormalLensAuthorityCoreClayFalse =
  refl

canonicalMeditationQiFormalLensAuthorityCoreEmpiricalFalse :
  AuthorityNA.empiricalAuthorityFlag
    (authorityNonPromotionCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  false
canonicalMeditationQiFormalLensAuthorityCoreEmpiricalFalse =
  refl

canonicalMeditationQiFormalLensAuthorityCorePromotesAnyFalse :
  AuthorityNA.promotesAnyAuthority
    (authorityNonPromotionCoreAdapter
      (formalLensQualificationAdapter canonicalMeditationQiBridgeReceipt))
  ≡
  false
canonicalMeditationQiFormalLensAuthorityCorePromotesAnyFalse =
  refl

canonicalMeditationQiClinicalAuthorityFalse :
  clinicalAuthorityPromoted canonicalMeditationQiBridgeReceipt ≡ false
canonicalMeditationQiClinicalAuthorityFalse =
  refl

canonicalMeditationQiFullAdmissionFalse :
  fullAdmission (sweetgrassGate canonicalMeditationQiBridgeReceipt) ≡ false
canonicalMeditationQiFullAdmissionFalse =
  refl

canonicalMeditationQiTruthAuthorityFalse :
  truthAuthorityPromoted canonicalMeditationQiBridgeReceipt ≡ false
canonicalMeditationQiTruthAuthorityFalse =
  refl

canonicalMeditationAuthorityBoundaryReceipt :
  AuthorityBoundaryCore.AuthorityBoundaryReceipt
canonicalMeditationAuthorityBoundaryReceipt =
  authorityBoundarySurfaceReceipt canonicalMeditationAuthorityBoundarySurface

canonicalMeditationAuthorityBoundaryReceiptIsCanonical :
  canonicalMeditationAuthorityBoundaryReceipt ≡
  AuthorityBoundaryCore.canonicalRuntimeAuthorityBoundaryReceipt
canonicalMeditationAuthorityBoundaryReceiptIsCanonical =
  authorityBoundarySurfaceReceiptIsCanonical
    canonicalMeditationAuthorityBoundarySurface

canonicalMeditationAuthorityBoundaryReceiptCandidateOnlyTrue :
  CandidateOnly.candidateOnly
    (AuthorityBoundaryCore.receiptCandidateRow
      canonicalMeditationAuthorityBoundaryReceipt)
  ≡
  true
canonicalMeditationAuthorityBoundaryReceiptCandidateOnlyTrue =
  AuthorityBoundaryCore.authorityBoundaryCandidateOnlyIsTrue
    canonicalMeditationAuthorityBoundaryReceipt

canonicalMeditationAuthorityBoundaryReceiptBundlePromotesAnyAuthorityFalse :
  AuthorityNA.promotesAnyAuthority
    (AuthorityBoundaryCore.receiptAuthorityBundle
      canonicalMeditationAuthorityBoundaryReceipt)
  ≡
  false
canonicalMeditationAuthorityBoundaryReceiptBundlePromotesAnyAuthorityFalse =
  AuthorityBoundaryCore.authorityBoundaryBundlePromotesAnyAuthorityIsFalse
    canonicalMeditationAuthorityBoundaryReceipt

canonicalMeditationAuthorityBoundaryReceiptPromotedFalse :
  AuthorityBoundaryCore.receiptBoundaryPromoted
    canonicalMeditationAuthorityBoundaryReceipt
  ≡
  false
canonicalMeditationAuthorityBoundaryReceiptPromotedFalse =
  AuthorityBoundaryCore.receiptBoundaryPromotedIsFalse
    canonicalMeditationAuthorityBoundaryReceipt

canonicalMeditationAuthorityBoundaryReceiptBlockedKindsFalse :
  AuthorityNA.AllAuthorityKindsFalse
    (AuthorityBoundaryCore.receiptAuthorityBundle
      canonicalMeditationAuthorityBoundaryReceipt)
    (AuthorityBoundaryCore.receiptBlockedAuthorityKinds
      canonicalMeditationAuthorityBoundaryReceipt)
canonicalMeditationAuthorityBoundaryReceiptBlockedKindsFalse =
  AuthorityBoundaryCore.receiptBlockedAuthorityKindsFalse
    canonicalMeditationAuthorityBoundaryReceipt

canonicalMeditationAuthorityBoundaryCandidateOnlyTrue :
  CandidateOnly.candidateOnly
    (AuthorityBoundaryCore.receiptCandidateRow
      canonicalMeditationAuthorityBoundaryReceipt)
  ≡
  true
canonicalMeditationAuthorityBoundaryCandidateOnlyTrue =
  authorityBoundarySurfaceCandidateOnlyTrue
    canonicalMeditationAuthorityBoundarySurface

canonicalMeditationAuthorityBoundaryBundlePromotesAnyAuthorityFalse :
  AuthorityNA.promotesAnyAuthority
    (AuthorityBoundaryCore.receiptAuthorityBundle
      canonicalMeditationAuthorityBoundaryReceipt)
  ≡
  false
canonicalMeditationAuthorityBoundaryBundlePromotesAnyAuthorityFalse =
  authorityBoundarySurfaceBundlePromotesAnyAuthorityFalse
    canonicalMeditationAuthorityBoundarySurface

canonicalMeditationAuthorityBoundaryPromotedFalse :
  authorityBoundarySurfacePromoted canonicalMeditationAuthorityBoundarySurface ≡ false
canonicalMeditationAuthorityBoundaryPromotedFalse =
  authorityBoundarySurfacePromotedIsFalse
    canonicalMeditationAuthorityBoundarySurface

canonicalMeditationAuthorityBoundaryBlockedKindsFalse :
  AuthorityNA.AllAuthorityKindsFalse
    (AuthorityBoundaryCore.receiptAuthorityBundle
      canonicalMeditationAuthorityBoundaryReceipt)
    (authorityBoundarySurfaceBlockedAuthorityKinds
      canonicalMeditationAuthorityBoundarySurface)
canonicalMeditationAuthorityBoundaryBlockedKindsFalse =
  authorityBoundarySurfaceBlockedAuthorityKindsFalse
    canonicalMeditationAuthorityBoundarySurface

canonicalMeditationAuthorityBoundaryBlockedKindsAreCanonical :
  authorityBoundarySurfaceBlockedAuthorityKinds
    canonicalMeditationAuthorityBoundarySurface
  ≡
  AuthorityNA.canonicalAuthorityKinds
canonicalMeditationAuthorityBoundaryBlockedKindsAreCanonical =
  authorityBoundarySurfaceBlockedAuthorityKindsAreCanonical
    canonicalMeditationAuthorityBoundarySurface

canonicalMeditationAuthorityBoundaryTruthFalse :
  authorityBoundarySurfaceTruthAuthorityPromoted
    canonicalMeditationAuthorityBoundarySurface ≡ false
canonicalMeditationAuthorityBoundaryTruthFalse =
  authorityBoundarySurfaceTruthAuthorityPromotedIsFalse
    canonicalMeditationAuthorityBoundarySurface

canonicalMeditationAuthorityBoundaryClinicalFalse :
  authorityBoundarySurfaceClinicalAuthorityPromoted
    canonicalMeditationAuthorityBoundarySurface ≡ false
canonicalMeditationAuthorityBoundaryClinicalFalse =
  authorityBoundarySurfaceClinicalAuthorityPromotedIsFalse
    canonicalMeditationAuthorityBoundarySurface

canonicalMeditationAuthorityBoundaryMetaphysicalFalse :
  authorityBoundarySurfaceMetaphysicalAuthorityPromoted
    canonicalMeditationAuthorityBoundarySurface
  ≡
  false
canonicalMeditationAuthorityBoundaryMetaphysicalFalse =
  authorityBoundarySurfaceMetaphysicalAuthorityPromotedIsFalse
    canonicalMeditationAuthorityBoundarySurface

canonicalMeditationAuthorityBoundaryReciprocalPracticeFalse :
  authorityBoundarySurfaceReciprocalPracticeAuthorityPromoted
    canonicalMeditationAuthorityBoundarySurface
  ≡
  false
canonicalMeditationAuthorityBoundaryReciprocalPracticeFalse =
  authorityBoundarySurfaceReciprocalPracticeAuthorityPromotedIsFalse
    canonicalMeditationAuthorityBoundarySurface
