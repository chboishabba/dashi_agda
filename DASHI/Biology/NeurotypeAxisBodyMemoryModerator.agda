module DASHI.Biology.NeurotypeAxisBodyMemoryModerator where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.FMRIConnectomeProxyGovernance as Proxy
import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as Intersectional
import DASHI.Biology.NeurodivergentAtlasBodyMemoryBridge as Atlas

------------------------------------------------------------------------
-- Candidate-only neurotype axis body-memory moderator.
--
-- NT / ND differences are modeled as chart and proxy moderation:
--   - chart priors shift by neurotype,
--   - sensory and masking loads are context-sensitive,
--   - transition costs can carry forward or adapt,
--   - BOLD/connectome differences remain proxy variation and do not imply
--     deficit, pathology, or brokenness.
--
-- Hard gates stay closed:
--   - no normal/broken classification,
--   - no diagnosis,
--   - no treatment,
--   - no clinical authority.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data Never : Set where

data NeurotypeAxisModeratorRoute : Set where
  candidateOnlyRoute : NeurotypeAxisModeratorRoute
  pathologyPromotionRoute : NeurotypeAxisModeratorRoute
  normalBrokenClassificationRoute : NeurotypeAxisModeratorRoute
  boldDeficitInferenceRoute : NeurotypeAxisModeratorRoute
  connectomePathologyInferenceRoute : NeurotypeAxisModeratorRoute
  diagnosisRoute : NeurotypeAxisModeratorRoute
  treatmentRoute : NeurotypeAxisModeratorRoute
  clinicalAuthorityRoute : NeurotypeAxisModeratorRoute

AdmissibleNeurotypeAxisModeratorRoute :
  NeurotypeAxisModeratorRoute →
  Set
AdmissibleNeurotypeAxisModeratorRoute candidateOnlyRoute = ⊤
AdmissibleNeurotypeAxisModeratorRoute pathologyPromotionRoute = Never
AdmissibleNeurotypeAxisModeratorRoute normalBrokenClassificationRoute = Never
AdmissibleNeurotypeAxisModeratorRoute boldDeficitInferenceRoute = Never
AdmissibleNeurotypeAxisModeratorRoute connectomePathologyInferenceRoute = Never
AdmissibleNeurotypeAxisModeratorRoute diagnosisRoute = Never
AdmissibleNeurotypeAxisModeratorRoute treatmentRoute = Never
AdmissibleNeurotypeAxisModeratorRoute clinicalAuthorityRoute = Never

pathologyPromotionRouteRejected :
  AdmissibleNeurotypeAxisModeratorRoute pathologyPromotionRoute →
  Never
pathologyPromotionRouteRejected impossible = impossible

normalBrokenClassificationRouteRejected :
  AdmissibleNeurotypeAxisModeratorRoute normalBrokenClassificationRoute →
  Never
normalBrokenClassificationRouteRejected impossible = impossible

boldDeficitInferenceRouteRejected :
  AdmissibleNeurotypeAxisModeratorRoute boldDeficitInferenceRoute →
  Never
boldDeficitInferenceRouteRejected impossible = impossible

connectomePathologyInferenceRouteRejected :
  AdmissibleNeurotypeAxisModeratorRoute connectomePathologyInferenceRoute →
  Never
connectomePathologyInferenceRouteRejected impossible = impossible

diagnosisRouteRejected :
  AdmissibleNeurotypeAxisModeratorRoute diagnosisRoute →
  Never
diagnosisRouteRejected impossible = impossible

treatmentRouteRejected :
  AdmissibleNeurotypeAxisModeratorRoute treatmentRoute →
  Never
treatmentRouteRejected impossible = impossible

clinicalAuthorityRouteRejected :
  AdmissibleNeurotypeAxisModeratorRoute clinicalAuthorityRoute →
  Never
clinicalAuthorityRouteRejected impossible = impossible

data NeurotypeKind : Set where
  neurotypicalKind : NeurotypeKind
  neurodivergentKind : NeurotypeKind
  mixedBridgeKind : NeurotypeKind
  reciprocalDifferenceKind : NeurotypeKind

data ChartPriorKind : Set where
  explicitChartPriorKind : ChartPriorKind
  accommodativeChartPriorKind : ChartPriorKind
  reciprocalChartPriorKind : ChartPriorKind
  lowAssumptionChartPriorKind : ChartPriorKind
  neurotypeAwareChartPriorKind : ChartPriorKind

data SensoryLoadKind : Set where
  lowSensoryLoadKind : SensoryLoadKind
  balancedSensoryLoadKind : SensoryLoadKind
  highSensoryLoadKind : SensoryLoadKind
  selectiveFilterSensoryLoadKind : SensoryLoadKind
  wideBandwidthSensoryLoadKind : SensoryLoadKind

data MaskingLoadKind : Set where
  lowMaskingLoadKind : MaskingLoadKind
  negotiatedMaskingLoadKind : MaskingLoadKind
  adaptiveMaskingLoadKind : MaskingLoadKind
  highMaskingLoadKind : MaskingLoadKind
  minimizedMaskingLoadKind : MaskingLoadKind

data TransitionCostKind : Set where
  lowTransitionCostKind : TransitionCostKind
  moderateTransitionCostKind : TransitionCostKind
  highTransitionCostKind : TransitionCostKind
  adaptiveTransitionCostKind : TransitionCostKind
  carryForwardTransitionCostKind : TransitionCostKind

data BiomarkerInterpretationKind : Set where
  proxyOnlyInterpretationKind : BiomarkerInterpretationKind
  contextualProxyInterpretationKind : BiomarkerInterpretationKind
  relationalProxyInterpretationKind : BiomarkerInterpretationKind
  differenceNotDeficitInterpretationKind : BiomarkerInterpretationKind
  differenceNotPathologyInterpretationKind : BiomarkerInterpretationKind

data ModeratorClaimKind : Set where
  chartPriorIsContextSensitiveClaim : ModeratorClaimKind
  sensoryLoadIsContextualClaim : ModeratorClaimKind
  maskingLoadIsCostClaim : ModeratorClaimKind
  transitionCostIsRealClaim : ModeratorClaimKind
  boldDifferenceNotDeficitClaim : ModeratorClaimKind
  connectomeDifferenceNotPathologyClaim : ModeratorClaimKind
  biomarkerIsProxyClaim : ModeratorClaimKind
  normalBrokenClassificationBlockedClaim : ModeratorClaimKind
  diagnosisBlockedClaim : ModeratorClaimKind
  treatmentBlockedClaim : ModeratorClaimKind
  clinicalAuthorityBlockedClaim : ModeratorClaimKind

data ModeratorRowTag : Set where
  neurotypicalChartRowTag : ModeratorRowTag
  neurodivergentChartRowTag : ModeratorRowTag
  mixedBridgeRowTag : ModeratorRowTag
  boldProxyRowTag : ModeratorRowTag
  connectomeProxyRowTag : ModeratorRowTag
  biomarkerRowTag : ModeratorRowTag
  boundaryRowTag : ModeratorRowTag

record NeurotypeAxisModeratorRow : Setω where
  constructor neurotypeAxisModeratorRow
  field
    rowTag :
      ModeratorRowTag

    rowNeurotypeKind :
      NeurotypeKind

    rowAxisBundle :
      List Intersectional.IntersectionalAxis

    rowChartPrior :
      ChartPriorKind

    rowSensoryLoad :
      SensoryLoadKind

    rowMaskingLoad :
      MaskingLoadKind

    rowTransitionCost :
      TransitionCostKind

    rowBiomarkerInterpretation :
      BiomarkerInterpretationKind

    rowChartPriorIsNeurotypeAware :
      Bool

    rowChartPriorIsNeurotypeAwareIsTrue :
      rowChartPriorIsNeurotypeAware ≡ true

    rowSensoryLoadIsContextual :
      Bool

    rowSensoryLoadIsContextualIsTrue :
      rowSensoryLoadIsContextual ≡ true

    rowMaskingLoadIsCost :
      Bool

    rowMaskingLoadIsCostIsTrue :
      rowMaskingLoadIsCost ≡ true

    rowTransitionCostIsReal :
      Bool

    rowTransitionCostIsRealIsTrue :
      rowTransitionCostIsReal ≡ true

    rowBoldDifferenceNotDeficit :
      Bool

    rowBoldDifferenceNotDeficitIsTrue :
      rowBoldDifferenceNotDeficit ≡ true

    rowConnectomeDifferenceNotPathology :
      Bool

    rowConnectomeDifferenceNotPathologyIsTrue :
      rowConnectomeDifferenceNotPathology ≡ true

    rowNormalBrokenClassificationBlocked :
      Bool

    rowNormalBrokenClassificationBlockedIsFalse :
      rowNormalBrokenClassificationBlocked ≡ false

    rowDiagnosisBlocked :
      Bool

    rowDiagnosisBlockedIsFalse :
      rowDiagnosisBlocked ≡ false

    rowTreatmentBlocked :
      Bool

    rowTreatmentBlockedIsFalse :
      rowTreatmentBlocked ≡ false

    rowClinicalAuthorityBlocked :
      Bool

    rowClinicalAuthorityBlockedIsFalse :
      rowClinicalAuthorityBlocked ≡ false

    rowReading :
      String

open NeurotypeAxisModeratorRow public

record NeurotypeAxisBodyMemoryModeratorSurface : Setω where
  constructor neurotypeAxisBodyMemoryModeratorSurface
  field
    NeurotypeSurface : Set
    ChartPriorSurface : Set
    SensoryLoadSurface : Set
    MaskingLoadSurface : Set
    TransitionCostSurface : Set
    BiomarkerInterpretationSurface : Set

    neurotypeToChartPrior :
      NeurotypeSurface →
      ChartPriorSurface

    neurotypeToSensoryLoad :
      NeurotypeSurface →
      SensoryLoadSurface

    neurotypeToMaskingLoad :
      NeurotypeSurface →
      MaskingLoadSurface

    neurotypeToTransitionCost :
      NeurotypeSurface →
      TransitionCostSurface

    proxyToBiomarkerInterpretation :
      Proxy.ProxySurfaceKind →
      BiomarkerInterpretationSurface

    chartPriorIsContextSensitive :
      Bool

    chartPriorIsContextSensitiveIsTrue :
      chartPriorIsContextSensitive ≡ true

    sensoryLoadIsContextual :
      Bool

    sensoryLoadIsContextualIsTrue :
      sensoryLoadIsContextual ≡ true

    maskingLoadIsCost :
      Bool

    maskingLoadIsCostIsTrue :
      maskingLoadIsCost ≡ true

    transitionCostIsReal :
      Bool

    transitionCostIsRealIsTrue :
      transitionCostIsReal ≡ true

    boldDifferenceNotDeficit :
      Bool

    boldDifferenceNotDeficitIsTrue :
      boldDifferenceNotDeficit ≡ true

    connectomeDifferenceNotPathology :
      Bool

    connectomeDifferenceNotPathologyIsTrue :
      connectomeDifferenceNotPathology ≡ true

    normalBrokenClassificationBlocked :
      Bool

    normalBrokenClassificationBlockedIsFalse :
      normalBrokenClassificationBlocked ≡ false

    diagnosisBlocked :
      Bool

    diagnosisBlockedIsFalse :
      diagnosisBlocked ≡ false

    treatmentBlocked :
      Bool

    treatmentBlockedIsFalse :
      treatmentBlocked ≡ false

    clinicalAuthorityBlocked :
      Bool

    clinicalAuthorityBlockedIsFalse :
      clinicalAuthorityBlocked ≡ false

    surfaceReading :
      String

open NeurotypeAxisBodyMemoryModeratorSurface public

record NeurotypeAxisBodyMemoryModeratorCertificate
    (moderator : NeurotypeAxisBodyMemoryModeratorSurface) : Setω where
  field
    certificateRoute :
      NeurotypeAxisModeratorRoute

    certificateRouteIsCandidateOnly :
      certificateRoute ≡ candidateOnlyRoute

    certificateRouteAdmissible :
      AdmissibleNeurotypeAxisModeratorRoute certificateRoute

    certificateRows :
      List NeurotypeAxisModeratorRow

    certificateRowsMatch :
      certificateRows ≡ canonicalNeurotypeAxisModeratorRows

    certificateRowCount :
      Nat

    certificateRowCountMatchesCanonical :
      certificateRowCount ≡ listCount canonicalNeurotypeAxisModeratorRows

    certificateClaims :
      List ModeratorClaimKind

    certificateClaimsAreCanonical :
      certificateClaims ≡ canonicalModeratorClaimKinds

    certificateChartPriorIsContextSensitive :
      Bool

    certificateChartPriorIsContextSensitiveIsTrue :
      certificateChartPriorIsContextSensitive ≡ true

    certificateSensoryLoadIsContextual :
      Bool

    certificateSensoryLoadIsContextualIsTrue :
      certificateSensoryLoadIsContextual ≡ true

    certificateMaskingLoadIsCost :
      Bool

    certificateMaskingLoadIsCostIsTrue :
      certificateMaskingLoadIsCost ≡ true

    certificateTransitionCostIsReal :
      Bool

    certificateTransitionCostIsRealIsTrue :
      certificateTransitionCostIsReal ≡ true

    certificateBoldDifferenceNotDeficit :
      Bool

    certificateBoldDifferenceNotDeficitIsTrue :
      certificateBoldDifferenceNotDeficit ≡ true

    certificateConnectomeDifferenceNotPathology :
      Bool

    certificateConnectomeDifferenceNotPathologyIsTrue :
      certificateConnectomeDifferenceNotPathology ≡ true

    certificateNormalBrokenClassificationBlocked :
      Bool

    certificateNormalBrokenClassificationBlockedIsFalse :
      certificateNormalBrokenClassificationBlocked ≡ false

    certificateDiagnosisBlocked :
      Bool

    certificateDiagnosisBlockedIsFalse :
      certificateDiagnosisBlocked ≡ false

    certificateTreatmentBlocked :
      Bool

    certificateTreatmentBlockedIsFalse :
      certificateTreatmentBlocked ≡ false

    certificateClinicalAuthorityBlocked :
      Bool

    certificateClinicalAuthorityBlockedIsFalse :
      certificateClinicalAuthorityBlocked ≡ false

    certificateReading :
      String

canonicalModeratorClaimKinds :
  List ModeratorClaimKind
canonicalModeratorClaimKinds =
  chartPriorIsContextSensitiveClaim
  ∷ sensoryLoadIsContextualClaim
  ∷ maskingLoadIsCostClaim
  ∷ transitionCostIsRealClaim
  ∷ boldDifferenceNotDeficitClaim
  ∷ connectomeDifferenceNotPathologyClaim
  ∷ biomarkerIsProxyClaim
  ∷ normalBrokenClassificationBlockedClaim
  ∷ diagnosisBlockedClaim
  ∷ treatmentBlockedClaim
  ∷ clinicalAuthorityBlockedClaim
  ∷ []

canonicalNeurotypeAxisModeratorRows :
  List NeurotypeAxisModeratorRow
canonicalNeurotypeAxisModeratorRows =
  neurotypeAxisModeratorRow
    neurotypicalChartRowTag
    neurotypicalKind
    Intersectional.canonicalIntersectionalAxes
    explicitChartPriorKind
    lowSensoryLoadKind
    lowMaskingLoadKind
    lowTransitionCostKind
    differenceNotDeficitInterpretationKind
    true
    refl
    true
    refl
    true
    refl
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
    false
    refl
    false
    refl
    "NT differences shift chart priors conservatively; the surface does not imply deficit, pathology, or brokenness."
  ∷ neurotypeAxisModeratorRow
    neurodivergentChartRowTag
    neurodivergentKind
    Intersectional.canonicalIntersectionalAxes
    accommodativeChartPriorKind
    highSensoryLoadKind
    adaptiveMaskingLoadKind
    adaptiveTransitionCostKind
    differenceNotPathologyInterpretationKind
    true
    refl
    true
    refl
    true
    refl
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
    false
    refl
    false
    refl
    "ND differences shift chart priors, sensory load, masking load, and transition cost without becoming pathology."
  ∷ neurotypeAxisModeratorRow
    mixedBridgeRowTag
    mixedBridgeKind
    Intersectional.canonicalIntersectionalAxes
    reciprocalChartPriorKind
    balancedSensoryLoadKind
    negotiatedMaskingLoadKind
    carryForwardTransitionCostKind
    contextualProxyInterpretationKind
    true
    refl
    true
    refl
    true
    refl
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
    false
    refl
    false
    refl
    "Mixed bridge rows carry reciprocal priors and negotiated load without normal/broken coding."
  ∷ neurotypeAxisModeratorRow
    boldProxyRowTag
    reciprocalDifferenceKind
    Intersectional.canonicalIntersectionalAxes
    neurotypeAwareChartPriorKind
    selectiveFilterSensoryLoadKind
    minimizedMaskingLoadKind
    moderateTransitionCostKind
    proxyOnlyInterpretationKind
    true
    refl
    true
    refl
    true
    refl
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
    false
    refl
    false
    refl
    "BOLD differences remain proxy variation and do not imply deficit, diagnosis, or authority."
  ∷ neurotypeAxisModeratorRow
    connectomeProxyRowTag
    reciprocalDifferenceKind
    Intersectional.canonicalIntersectionalAxes
    neurotypeAwareChartPriorKind
    wideBandwidthSensoryLoadKind
    adaptiveMaskingLoadKind
    moderateTransitionCostKind
    relationalProxyInterpretationKind
    true
    refl
    true
    refl
    true
    refl
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
    false
    refl
    false
    refl
    "Connectome differences remain relational proxy variation and do not imply pathology or brokenness."
  ∷ neurotypeAxisModeratorRow
    biomarkerRowTag
    mixedBridgeKind
    Intersectional.canonicalIntersectionalAxes
    lowAssumptionChartPriorKind
    balancedSensoryLoadKind
    minimizedMaskingLoadKind
    lowTransitionCostKind
    contextualProxyInterpretationKind
    true
    refl
    true
    refl
    true
    refl
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
    false
    refl
    false
    refl
    "Biomarkers stay proxy-only and are interpreted contextually, not as deficit proofs."
  ∷ neurotypeAxisModeratorRow
    boundaryRowTag
    reciprocalDifferenceKind
    Intersectional.canonicalIntersectionalAxes
    lowAssumptionChartPriorKind
    balancedSensoryLoadKind
    minimizedMaskingLoadKind
    lowTransitionCostKind
    proxyOnlyInterpretationKind
    true
    refl
    true
    refl
    true
    refl
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
    false
    refl
    false
    refl
    "Boundary row keeps the moderator candidate-only, with no normal/broken classification, diagnosis, treatment, or clinical authority."
  ∷ []

canonicalNeurotypeAxisBodyMemoryModeratorSurface :
  NeurotypeAxisBodyMemoryModeratorSurface
canonicalNeurotypeAxisBodyMemoryModeratorSurface =
  neurotypeAxisBodyMemoryModeratorSurface
    NeurotypeKind
    ChartPriorKind
    SensoryLoadKind
    MaskingLoadKind
    TransitionCostKind
    BiomarkerInterpretationKind
    (λ k →
      case k of λ where
        neurotypicalKind → explicitChartPriorKind
        neurodivergentKind → accommodativeChartPriorKind
        mixedBridgeKind → reciprocalChartPriorKind
        reciprocalDifferenceKind → neurotypeAwareChartPriorKind)
    (λ k →
      case k of λ where
        neurotypicalKind → lowSensoryLoadKind
        neurodivergentKind → highSensoryLoadKind
        mixedBridgeKind → balancedSensoryLoadKind
        reciprocalDifferenceKind → selectiveFilterSensoryLoadKind)
    (λ k →
      case k of λ where
        neurotypicalKind → lowMaskingLoadKind
        neurodivergentKind → highMaskingLoadKind
        mixedBridgeKind → negotiatedMaskingLoadKind
        reciprocalDifferenceKind → minimizedMaskingLoadKind)
    (λ k →
      case k of λ where
        neurotypicalKind → lowTransitionCostKind
        neurodivergentKind → adaptiveTransitionCostKind
        mixedBridgeKind → carryForwardTransitionCostKind
        reciprocalDifferenceKind → moderateTransitionCostKind)
    (λ p →
      case p of λ where
        Proxy.measurementProxySurface → contextualProxyInterpretationKind
        Proxy.boldSignalProxySurface → differenceNotDeficitInterpretationKind
        Proxy.connectomeGraphProxySurface → differenceNotPathologyInterpretationKind
        Proxy.functionalConnectivityProxySurface → relationalProxyInterpretationKind
        Proxy.reverseInferenceBoundarySurface → proxyOnlyInterpretationKind)
    true
    refl
    true
    refl
    true
    refl
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
    false
    refl
    false
    refl
    "Neurotype-aware surface: chart priors, sensory load, masking load, transition costs, and proxy interpretation are moderated without normal/broken classification."

canonicalNeurotypeAxisBodyMemoryModeratorCertificate :
  NeurotypeAxisBodyMemoryModeratorCertificate
    canonicalNeurotypeAxisBodyMemoryModeratorSurface
canonicalNeurotypeAxisBodyMemoryModeratorCertificate =
  record
    { certificateRoute =
        candidateOnlyRoute
    ; certificateRouteIsCandidateOnly =
        refl
    ; certificateRouteAdmissible =
        tt
    ; certificateRows =
        canonicalNeurotypeAxisModeratorRows
    ; certificateRowsMatch =
        refl
    ; certificateRowCount =
        listCount canonicalNeurotypeAxisModeratorRows
    ; certificateRowCountMatchesCanonical =
        refl
    ; certificateClaims =
        canonicalModeratorClaimKinds
    ; certificateClaimsAreCanonical =
        refl
    ; certificateChartPriorIsContextSensitive =
        true
    ; certificateChartPriorIsContextSensitiveIsTrue =
        refl
    ; certificateSensoryLoadIsContextual =
        true
    ; certificateSensoryLoadIsContextualIsTrue =
        refl
    ; certificateMaskingLoadIsCost =
        true
    ; certificateMaskingLoadIsCostIsTrue =
        refl
    ; certificateTransitionCostIsReal =
        true
    ; certificateTransitionCostIsRealIsTrue =
        refl
    ; certificateBoldDifferenceNotDeficit =
        true
    ; certificateBoldDifferenceNotDeficitIsTrue =
        refl
    ; certificateConnectomeDifferenceNotPathology =
        true
    ; certificateConnectomeDifferenceNotPathologyIsTrue =
        refl
    ; certificateNormalBrokenClassificationBlocked =
        false
    ; certificateNormalBrokenClassificationBlockedIsFalse =
        refl
    ; certificateDiagnosisBlocked =
        false
    ; certificateDiagnosisBlockedIsFalse =
        refl
    ; certificateTreatmentBlocked =
        false
    ; certificateTreatmentBlockedIsFalse =
        refl
    ; certificateClinicalAuthorityBlocked =
        false
    ; certificateClinicalAuthorityBlockedIsFalse =
        refl
    ; certificateReading =
        "Candidate-only neurotype moderator certificate: NT/ND differences modulate chart priors, sensory load, masking load, transition costs, and biomarker/proxy interpretation; BOLD/connectome variation remains proxy variation and does not imply deficit, pathology, normality, brokenness, diagnosis, treatment, or clinical authority."
    }

canonicalRouteIsCandidateOnly :
  route canonicalNeurotypeAxisBodyMemoryModeratorCertificate ≡ candidateOnlyRoute
canonicalRouteIsCandidateOnly =
  certificateRouteIsCandidateOnly canonicalNeurotypeAxisBodyMemoryModeratorCertificate

canonicalChartPriorIsContextSensitiveIsTrue :
  chartPriorIsContextSensitive
    canonicalNeurotypeAxisBodyMemoryModeratorSurface
  ≡
  true
canonicalChartPriorIsContextSensitiveIsTrue =
  chartPriorIsContextSensitiveIsTrue
    canonicalNeurotypeAxisBodyMemoryModeratorSurface

canonicalSensoryLoadIsContextualIsTrue :
  sensoryLoadIsContextual canonicalNeurotypeAxisBodyMemoryModeratorSurface ≡ true
canonicalSensoryLoadIsContextualIsTrue =
  sensoryLoadIsContextualIsTrue
    canonicalNeurotypeAxisBodyMemoryModeratorSurface

canonicalMaskingLoadIsCostIsTrue :
  maskingLoadIsCost canonicalNeurotypeAxisBodyMemoryModeratorSurface ≡ true
canonicalMaskingLoadIsCostIsTrue =
  maskingLoadIsCostIsTrue
    canonicalNeurotypeAxisBodyMemoryModeratorSurface

canonicalTransitionCostIsRealIsTrue :
  transitionCostIsReal canonicalNeurotypeAxisBodyMemoryModeratorSurface ≡ true
canonicalTransitionCostIsRealIsTrue =
  transitionCostIsRealIsTrue
    canonicalNeurotypeAxisBodyMemoryModeratorSurface

canonicalBoldDifferenceNotDeficitIsTrue :
  boldDifferenceNotDeficit canonicalNeurotypeAxisBodyMemoryModeratorSurface ≡ true
canonicalBoldDifferenceNotDeficitIsTrue =
  boldDifferenceNotDeficitIsTrue
    canonicalNeurotypeAxisBodyMemoryModeratorSurface

canonicalConnectomeDifferenceNotPathologyIsTrue :
  connectomeDifferenceNotPathology
    canonicalNeurotypeAxisBodyMemoryModeratorSurface
  ≡
  true
canonicalConnectomeDifferenceNotPathologyIsTrue =
  connectomeDifferenceNotPathologyIsTrue
    canonicalNeurotypeAxisBodyMemoryModeratorSurface

canonicalNormalBrokenClassificationBlockedIsFalse :
  normalBrokenClassificationBlocked
    canonicalNeurotypeAxisBodyMemoryModeratorSurface
  ≡
  false
canonicalNormalBrokenClassificationBlockedIsFalse =
  normalBrokenClassificationBlockedIsFalse
    canonicalNeurotypeAxisBodyMemoryModeratorSurface

canonicalDiagnosisBlockedIsFalse :
  diagnosisBlocked canonicalNeurotypeAxisBodyMemoryModeratorSurface ≡ false
canonicalDiagnosisBlockedIsFalse =
  diagnosisBlockedIsFalse canonicalNeurotypeAxisBodyMemoryModeratorSurface

canonicalTreatmentBlockedIsFalse :
  treatmentBlocked canonicalNeurotypeAxisBodyMemoryModeratorSurface ≡ false
canonicalTreatmentBlockedIsFalse =
  treatmentBlockedIsFalse canonicalNeurotypeAxisBodyMemoryModeratorSurface

canonicalClinicalAuthorityBlockedIsFalse :
  clinicalAuthorityBlocked canonicalNeurotypeAxisBodyMemoryModeratorSurface ≡
  false
canonicalClinicalAuthorityBlockedIsFalse =
  clinicalAuthorityBlockedIsFalse
    canonicalNeurotypeAxisBodyMemoryModeratorSurface

canonicalRowsAreExact :
  certificateRows canonicalNeurotypeAxisBodyMemoryModeratorCertificate ≡
  canonicalNeurotypeAxisModeratorRows
canonicalRowsAreExact =
  certificateRowsMatch canonicalNeurotypeAxisBodyMemoryModeratorCertificate

canonicalClaimsAreExact :
  certificateClaims canonicalNeurotypeAxisBodyMemoryModeratorCertificate ≡
  canonicalModeratorClaimKinds
canonicalClaimsAreExact =
  certificateClaimsAreCanonical
    canonicalNeurotypeAxisBodyMemoryModeratorCertificate

canonicalModerator :
  NeurotypeAxisBodyMemoryModeratorSurface
canonicalModerator =
  canonicalNeurotypeAxisBodyMemoryModeratorSurface
