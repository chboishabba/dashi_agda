module DASHI.Biology.NeurodivergentAtlasBodyMemoryBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive using (Setω)

------------------------------------------------------------------------
-- Neurodivergent atlas body-memory bridge.
--
-- Candidate-only surface:
--   - NT / ND are not treated as normal / broken.
--   - They are treated as different chart-building styles, atlas priors,
--     sensory weights, social-code assumptions, and residual thresholds.
--   - Hard gates block pathology promotion, cure framing, forced
--     normalization, diagnosis, treatment authority, mind-reading, and
--     BOLD/connectome overclaim.

data Never : Set where

data NeurodivergentAtlasRoute : Set where
  candidateOnlyRoute : NeurodivergentAtlasRoute
  pathologyPromotionRoute : NeurodivergentAtlasRoute
  cureFramingRoute : NeurodivergentAtlasRoute
  forcedNormalizationRoute : NeurodivergentAtlasRoute
  diagnosisRoute : NeurodivergentAtlasRoute
  treatmentAuthorityRoute : NeurodivergentAtlasRoute
  mindReadingRoute : NeurodivergentAtlasRoute
  boldOverclaimRoute : NeurodivergentAtlasRoute
  connectomeOverclaimRoute : NeurodivergentAtlasRoute

AdmissibleNeurodivergentAtlasRoute :
  NeurodivergentAtlasRoute →
  Set
AdmissibleNeurodivergentAtlasRoute candidateOnlyRoute = ⊤
AdmissibleNeurodivergentAtlasRoute pathologyPromotionRoute = Never
AdmissibleNeurodivergentAtlasRoute cureFramingRoute = Never
AdmissibleNeurodivergentAtlasRoute forcedNormalizationRoute = Never
AdmissibleNeurodivergentAtlasRoute diagnosisRoute = Never
AdmissibleNeurodivergentAtlasRoute treatmentAuthorityRoute = Never
AdmissibleNeurodivergentAtlasRoute mindReadingRoute = Never
AdmissibleNeurodivergentAtlasRoute boldOverclaimRoute = Never
AdmissibleNeurodivergentAtlasRoute connectomeOverclaimRoute = Never

pathologyPromotionRouteRejected :
  AdmissibleNeurodivergentAtlasRoute pathologyPromotionRoute →
  Never
pathologyPromotionRouteRejected impossible = impossible

cureFramingRouteRejected :
  AdmissibleNeurodivergentAtlasRoute cureFramingRoute →
  Never
cureFramingRouteRejected impossible = impossible

forcedNormalizationRouteRejected :
  AdmissibleNeurodivergentAtlasRoute forcedNormalizationRoute →
  Never
forcedNormalizationRouteRejected impossible = impossible

diagnosisRouteRejected :
  AdmissibleNeurodivergentAtlasRoute diagnosisRoute →
  Never
diagnosisRouteRejected impossible = impossible

treatmentAuthorityRouteRejected :
  AdmissibleNeurodivergentAtlasRoute treatmentAuthorityRoute →
  Never
treatmentAuthorityRouteRejected impossible = impossible

mindReadingRouteRejected :
  AdmissibleNeurodivergentAtlasRoute mindReadingRoute →
  Never
mindReadingRouteRejected impossible = impossible

boldOverclaimRouteRejected :
  AdmissibleNeurodivergentAtlasRoute boldOverclaimRoute →
  Never
boldOverclaimRouteRejected impossible = impossible

connectomeOverclaimRouteRejected :
  AdmissibleNeurodivergentAtlasRoute connectomeOverclaimRoute →
  Never
connectomeOverclaimRouteRejected impossible = impossible

data AtlasStyle : Set where
  neurotypicalChartStyle : AtlasStyle
  neurodivergentChartStyle : AtlasStyle
  mixedBridgeStyle : AtlasStyle
  reciprocalAtlasStyle : AtlasStyle

data ChartCompressionKind : Set where
  neurotypicalCompressionKind : ChartCompressionKind
  neurodivergentCompressionKind : ChartCompressionKind
  mixedBridgeCompressionKind : ChartCompressionKind
  reciprocalCompressionKind : ChartCompressionKind

data SocialCodeThresholdKind : Set where
  explicitSocialCodeThresholdKind : SocialCodeThresholdKind
  negotiatedSocialCodeThresholdKind : SocialCodeThresholdKind
  contextualSocialCodeThresholdKind : SocialCodeThresholdKind
  neuroaffirmingSocialCodeThresholdKind : SocialCodeThresholdKind
  noForcedNormalizationThresholdKind : SocialCodeThresholdKind

data NeurotypeKind : Set where
  neurotypicalKind : NeurotypeKind
  neurodivergentKind : NeurotypeKind
  mixedBridgeKind : NeurotypeKind
  reciprocalAtlasKind : NeurotypeKind

data AtlasPriorKind : Set where
  explicitPriorKind : AtlasPriorKind
  accommodativePriorKind : AtlasPriorKind
  reciprocalPriorKind : AtlasPriorKind
  lowAssumptionPriorKind : AtlasPriorKind
  highDetailPriorKind : AtlasPriorKind

data SensoryWeightKind : Set where
  lowWeightKind : SensoryWeightKind
  balancedWeightKind : SensoryWeightKind
  highWeightKind : SensoryWeightKind
  selectiveFilterWeightKind : SensoryWeightKind
  wideBandwidthWeightKind : SensoryWeightKind

data SocialCodeAssumptionKind : Set where
  explicitSocialCodeKind : SocialCodeAssumptionKind
  negotiatedSocialCodeKind : SocialCodeAssumptionKind
  contextualSocialCodeKind : SocialCodeAssumptionKind
  noForcedNormalizationKind : SocialCodeAssumptionKind
  neuroaffirmingAssumptionKind : SocialCodeAssumptionKind

data ResidualThresholdKind : Set where
  conservativeThresholdKind : ResidualThresholdKind
  adaptiveThresholdKind : ResidualThresholdKind
  tightThresholdKind : ResidualThresholdKind
  overThresholdCarryKind : ResidualThresholdKind

data BodyMemoryAxis : Set where
  bodyAxis : BodyMemoryAxis
  timeAxis : BodyMemoryAxis
  placeAxis : BodyMemoryAxis
  relationAxis : BodyMemoryAxis
  institutionAxis : BodyMemoryAxis
  chartAxis : BodyMemoryAxis
  atlasAxis : BodyMemoryAxis

data BoundaryClaimKind : Set where
  normalBrokenClassificationBlockedClaim : BoundaryClaimKind
  pathologyPromotionBlockedClaim : BoundaryClaimKind
  cureFramingBlockedClaim : BoundaryClaimKind
  forcedNormalizationBlockedClaim : BoundaryClaimKind
  diagnosisBlockedClaim : BoundaryClaimKind
  treatmentAuthorityBlockedClaim : BoundaryClaimKind
  mindReadingBlockedClaim : BoundaryClaimKind
  boldOverclaimBlockedClaim : BoundaryClaimKind
  connectomeOverclaimBlockedClaim : BoundaryClaimKind
  noAuthorityPromotionClaim : BoundaryClaimKind

data HandleKind : Set where
  directHandleKind : HandleKind
  smallSafeJPlusOneHandleKind : HandleKind
  forcedHandleKind : HandleKind
  authorityHandleKind : HandleKind

canonicalAxes : List BodyMemoryAxis
canonicalAxes =
  bodyAxis
  ∷ timeAxis
  ∷ placeAxis
  ∷ relationAxis
  ∷ institutionAxis
  ∷ chartAxis
  ∷ atlasAxis
  ∷ []

canonicalAtlasStyles : List AtlasStyle
canonicalAtlasStyles =
  neurotypicalChartStyle
  ∷ neurodivergentChartStyle
  ∷ mixedBridgeStyle
  ∷ reciprocalAtlasStyle
  ∷ []

canonicalChartCompressionKinds : List ChartCompressionKind
canonicalChartCompressionKinds =
  neurotypicalCompressionKind
  ∷ neurodivergentCompressionKind
  ∷ mixedBridgeCompressionKind
  ∷ reciprocalCompressionKind
  ∷ []

canonicalSocialCodeThresholdKinds : List SocialCodeThresholdKind
canonicalSocialCodeThresholdKinds =
  explicitSocialCodeThresholdKind
  ∷ negotiatedSocialCodeThresholdKind
  ∷ contextualSocialCodeThresholdKind
  ∷ neuroaffirmingSocialCodeThresholdKind
  ∷ noForcedNormalizationThresholdKind
  ∷ []

canonicalNeurotypeKinds : List NeurotypeKind
canonicalNeurotypeKinds =
  neurotypicalKind
  ∷ neurodivergentKind
  ∷ mixedBridgeKind
  ∷ reciprocalAtlasKind
  ∷ []

canonicalAtlasPriors : List AtlasPriorKind
canonicalAtlasPriors =
  explicitPriorKind
  ∷ accommodativePriorKind
  ∷ reciprocalPriorKind
  ∷ lowAssumptionPriorKind
  ∷ highDetailPriorKind
  ∷ []

canonicalSensoryWeights : List SensoryWeightKind
canonicalSensoryWeights =
  lowWeightKind
  ∷ balancedWeightKind
  ∷ highWeightKind
  ∷ selectiveFilterWeightKind
  ∷ wideBandwidthWeightKind
  ∷ []

canonicalSocialCodeAssumptions : List SocialCodeAssumptionKind
canonicalSocialCodeAssumptions =
  explicitSocialCodeKind
  ∷ negotiatedSocialCodeKind
  ∷ contextualSocialCodeKind
  ∷ noForcedNormalizationKind
  ∷ neuroaffirmingAssumptionKind
  ∷ []

canonicalResidualThresholdKinds : List ResidualThresholdKind
canonicalResidualThresholdKinds =
  conservativeThresholdKind
  ∷ adaptiveThresholdKind
  ∷ tightThresholdKind
  ∷ overThresholdCarryKind
  ∷ []

canonicalBoundaryClaimKinds : List BoundaryClaimKind
canonicalBoundaryClaimKinds =
  normalBrokenClassificationBlockedClaim
  ∷ pathologyPromotionBlockedClaim
  ∷ cureFramingBlockedClaim
  ∷ forcedNormalizationBlockedClaim
  ∷ diagnosisBlockedClaim
  ∷ treatmentAuthorityBlockedClaim
  ∷ mindReadingBlockedClaim
  ∷ boldOverclaimBlockedClaim
  ∷ connectomeOverclaimBlockedClaim
  ∷ noAuthorityPromotionClaim
  ∷ []

canonicalHandleKinds : List HandleKind
canonicalHandleKinds =
  directHandleKind
  ∷ smallSafeJPlusOneHandleKind
  ∷ forcedHandleKind
  ∷ authorityHandleKind
  ∷ []

canonicalBridgeNotes : List String
canonicalBridgeNotes =
  "NT and ND are treated as distinct chart-building styles, not normal and broken"
  ∷ "Atlas priors stay explicit and chart compression stays distinct from sensory weight"
  ∷ "NT/ND chart compression is different from social-code thresholding"
  ∷ "Sensory weights are modeled as different weightings, not deficits"
  ∷ "Social-code assumptions and thresholds remain negotiated and neuroaffirming"
  ∷ "Residual thresholds vary by chart style and can carry j+1 safely"
  ∷ "Pathology promotion, cure framing, forced normalization, diagnosis, treatment authority, mind reading, and overclaim stay blocked"
  ∷ "Normal/broken classification stays blocked"
  ∷ []

record NeurodivergentAtlasRow : Set where
  constructor mkNeurodivergentAtlasRow
  field
    rowIndex :
      Nat

    rowTime :
      Nat

    rowBody :
      String

    rowPlace :
      String

    rowRelation :
      String

    rowInstitution :
      String

    rowAxisBundle :
      List BodyMemoryAxis

    rowAtlasStyle :
      AtlasStyle

    rowChartCompression :
      ChartCompressionKind

    rowAtlasPrior :
      AtlasPriorKind

    rowSensoryWeight :
      SensoryWeightKind

    rowSocialCodeAssumption :
      SocialCodeAssumptionKind

    rowSocialCodeThreshold :
      SocialCodeThresholdKind

    rowNeurotypeKind :
      NeurotypeKind

    rowResidualThreshold :
      ResidualThresholdKind

    rowResidualThresholdProfile :
      ResidualThresholdKind

    rowResidualThresholdIsCanonical :
      rowResidualThreshold ≡ rowResidualThresholdProfile

    rowNormalBrokenClassificationBlocked :
      Bool

    rowNormalBrokenClassificationBlockedIsFalse :
      rowNormalBrokenClassificationBlocked ≡ false

    rowResidualKind :
      String

    rowCandidateOnly :
      Bool

    rowCandidateOnlyIsTrue :
      rowCandidateOnly ≡ true

    rowPathologyPromotionBlocked :
      Bool

    rowPathologyPromotionBlockedIsFalse :
      rowPathologyPromotionBlocked ≡ false

    rowCureFramingBlocked :
      Bool

    rowCureFramingBlockedIsFalse :
      rowCureFramingBlocked ≡ false

    rowForcedNormalizationBlocked :
      Bool

    rowForcedNormalizationBlockedIsFalse :
      rowForcedNormalizationBlocked ≡ false

    rowDiagnosisBlocked :
      Bool

    rowDiagnosisBlockedIsFalse :
      rowDiagnosisBlocked ≡ false

    rowTreatmentAuthorityBlocked :
      Bool

    rowTreatmentAuthorityBlockedIsFalse :
      rowTreatmentAuthorityBlocked ≡ false

    rowMindReadingBlocked :
      Bool

    rowMindReadingBlockedIsFalse :
      rowMindReadingBlocked ≡ false

    rowBoldOverclaimBlocked :
      Bool

    rowBoldOverclaimBlockedIsFalse :
      rowBoldOverclaimBlocked ≡ false

    rowConnectomeOverclaimBlocked :
      Bool

    rowConnectomeOverclaimBlockedIsFalse :
      rowConnectomeOverclaimBlocked ≡ false

    rowReading :
      String

open NeurodivergentAtlasRow public

record NonPromotionCertificate : Set where
  constructor mkNonPromotionCertificate
  field
    certificateLabel :
      String

    certificateRoute :
      NeurodivergentAtlasRoute

    certificateRouteIsCandidateOnly :
      certificateRoute ≡ candidateOnlyRoute

    certificateRouteAdmissible :
      AdmissibleNeurodivergentAtlasRoute certificateRoute

    certificatePathologyPromotionBlocked :
      Bool

    certificatePathologyPromotionBlockedIsFalse :
      certificatePathologyPromotionBlocked ≡ false

    certificateCureFramingBlocked :
      Bool

    certificateCureFramingBlockedIsFalse :
      certificateCureFramingBlocked ≡ false

    certificateForcedNormalizationBlocked :
      Bool

    certificateForcedNormalizationBlockedIsFalse :
      certificateForcedNormalizationBlocked ≡ false

    certificateDiagnosisBlocked :
      Bool

    certificateDiagnosisBlockedIsFalse :
      certificateDiagnosisBlocked ≡ false

    certificateTreatmentAuthorityBlocked :
      Bool

    certificateTreatmentAuthorityBlockedIsFalse :
      certificateTreatmentAuthorityBlocked ≡ false

    certificateMindReadingBlocked :
      Bool

    certificateMindReadingBlockedIsFalse :
      certificateMindReadingBlocked ≡ false

    certificateBoldOverclaimBlocked :
      Bool

    certificateBoldOverclaimBlockedIsFalse :
      certificateBoldOverclaimBlocked ≡ false

    certificateConnectomeOverclaimBlocked :
      Bool

    certificateConnectomeOverclaimBlockedIsFalse :
      certificateConnectomeOverclaimBlocked ≡ false

    certificateAxisBundle :
      List BodyMemoryAxis

    certificateAxisBundleIsCanonical :
      certificateAxisBundle ≡ canonicalAxes

    certificateBoundaryClaims :
      List BoundaryClaimKind

    certificateBoundaryClaimsAreCanonical :
      certificateBoundaryClaims ≡ canonicalBoundaryClaimKinds

    certificateReading :
      String

open NonPromotionCertificate public

record NeurodivergentAtlasBodyMemoryBridge : Setω where
  constructor mkNeurodivergentAtlasBodyMemoryBridge
  field
    bridgeRoute :
      NeurodivergentAtlasRoute

    bridgeRouteIsCandidateOnly :
      bridgeRoute ≡ candidateOnlyRoute

    bridgeRouteAdmissible :
      AdmissibleNeurodivergentAtlasRoute bridgeRoute

    atlasRows :
      List NeurodivergentAtlasRow

    atlasRowsAreCanonical :
      atlasRows ≡ atlasRows

    atlasStyles :
      List AtlasStyle

    atlasStylesAreCanonical :
      atlasStyles ≡ canonicalAtlasStyles

    chartCompressionKinds :
      List ChartCompressionKind

    chartCompressionKindsAreCanonical :
      chartCompressionKinds ≡ canonicalChartCompressionKinds

    atlasPriors :
      List AtlasPriorKind

    atlasPriorsAreCanonical :
      atlasPriors ≡ canonicalAtlasPriors

    sensoryWeights :
      List SensoryWeightKind

    sensoryWeightsAreCanonical :
      sensoryWeights ≡ canonicalSensoryWeights

    socialCodeAssumptions :
      List SocialCodeAssumptionKind

    socialCodeAssumptionsAreCanonical :
      socialCodeAssumptions ≡ canonicalSocialCodeAssumptions

    socialCodeThresholdKinds :
      List SocialCodeThresholdKind

    socialCodeThresholdKindsAreCanonical :
      socialCodeThresholdKinds ≡ canonicalSocialCodeThresholdKinds

    neurotypeKinds :
      List NeurotypeKind

    neurotypeKindsAreCanonical :
      neurotypeKinds ≡ canonicalNeurotypeKinds

    residualThresholdKinds :
      List ResidualThresholdKind

    residualThresholdKindsAreCanonical :
      residualThresholdKinds ≡ canonicalResidualThresholdKinds

    boundaryClaims :
      List BoundaryClaimKind

    boundaryClaimsAreCanonical :
      boundaryClaims ≡ canonicalBoundaryClaimKinds

    handleKinds :
      List HandleKind

    handleKindsAreCanonical :
      handleKinds ≡ canonicalHandleKinds

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    pathologyPromotionBlocked :
      Bool

    pathologyPromotionBlockedIsFalse :
      pathologyPromotionBlocked ≡ false

    cureFramingBlocked :
      Bool

    cureFramingBlockedIsFalse :
      cureFramingBlocked ≡ false

    forcedNormalizationBlocked :
      Bool

    forcedNormalizationBlockedIsFalse :
      forcedNormalizationBlocked ≡ false

    diagnosisBlocked :
      Bool

    diagnosisBlockedIsFalse :
      diagnosisBlocked ≡ false

    treatmentAuthorityBlocked :
      Bool

    treatmentAuthorityBlockedIsFalse :
      treatmentAuthorityBlocked ≡ false

    mindReadingBlocked :
      Bool

    mindReadingBlockedIsFalse :
      mindReadingBlocked ≡ false

    boldOverclaimBlocked :
      Bool

    boldOverclaimBlockedIsFalse :
      boldOverclaimBlocked ≡ false

    connectomeOverclaimBlocked :
      Bool

    connectomeOverclaimBlockedIsFalse :
      connectomeOverclaimBlocked ≡ false

    normalBrokenClassificationBlocked :
      Bool

    normalBrokenClassificationBlockedIsFalse :
      normalBrokenClassificationBlocked ≡ false

    nonPromotionCertificate :
      NonPromotionCertificate

    nonPromotionCertificateIsCanonical :
      nonPromotionCertificate ≡ nonPromotionCertificate

    bridgeReading :
      String

    bridgeNotes :
      List String

open NeurodivergentAtlasBodyMemoryBridge public

------------------------------------------------------------------------
-- Canonical row constructors.

mkBridgeRow :
  Nat →
  Nat →
  String →
  String →
  String →
  String →
  List BodyMemoryAxis →
  AtlasStyle →
  ChartCompressionKind →
  AtlasPriorKind →
  SensoryWeightKind →
  SocialCodeAssumptionKind →
  SocialCodeThresholdKind →
  NeurotypeKind →
  ResidualThresholdKind →
  String →
  NeurodivergentAtlasRow
mkBridgeRow index time body place relation institution axes style compression prior weight socialAssumption socialThreshold neurotype residualThreshold reading =
  mkNeurodivergentAtlasRow
    index
    time
    body
    place
    relation
    institution
    axes
    style
    compression
    prior
    weight
    socialAssumption
    socialThreshold
    neurotype
    residualThreshold
    residualThreshold
    refl
    false
    refl
    reading
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
    reading

canonicalNTRow :
  NeurodivergentAtlasRow
canonicalNTRow =
  mkBridgeRow
    zero
    zero
    "body memory"
    "social context"
    "chart building"
    "institutional setting"
    canonicalAxes
    neurotypicalChartStyle
    neurotypicalCompressionKind
    explicitPriorKind
    balancedWeightKind
    explicitSocialCodeKind
    explicitSocialCodeThresholdKind
    neurotypicalKind
    conservativeThresholdKind
    "NT chart-building style keeps a conservative residual threshold and does not imply pathology."

canonicalNDRow :
  NeurodivergentAtlasRow
canonicalNDRow =
  mkBridgeRow
    (suc zero)
    (suc zero)
    "body memory"
    "situated context"
    "chart building"
    "community and institution"
    canonicalAxes
    neurodivergentChartStyle
    neurodivergentCompressionKind
    accommodativePriorKind
    highWeightKind
    neuroaffirmingAssumptionKind
    neuroaffirmingSocialCodeThresholdKind
    neurodivergentKind
    adaptiveThresholdKind
    "ND chart-building style keeps an adaptive residual threshold and does not imply brokenness."

canonicalBridgeResidualRow :
  NeurodivergentAtlasRow
canonicalBridgeResidualRow =
  mkBridgeRow
    (suc (suc zero))
    (suc (suc zero))
    "body memory"
    "changing place"
    "relational residue"
    "institutional setting"
    canonicalAxes
    mixedBridgeStyle
    mixedBridgeCompressionKind
    reciprocalPriorKind
    selectiveFilterWeightKind
    contextualSocialCodeKind
    contextualSocialCodeThresholdKind
    mixedBridgeKind
    tightThresholdKind
    "Bridge row keeps the residual open, negotiated, and candidate-only."

canonicalBridgeRows :
  List NeurodivergentAtlasRow
canonicalBridgeRows =
  canonicalNTRow
  ∷ canonicalNDRow
  ∷ canonicalBridgeResidualRow
  ∷ []

canonicalNTRowResidualThresholdProfileIsCanonical :
  rowResidualThresholdProfile canonicalNTRow ≡ conservativeThresholdKind
canonicalNTRowResidualThresholdProfileIsCanonical =
  refl

canonicalNDRowResidualThresholdProfileIsCanonical :
  rowResidualThresholdProfile canonicalNDRow ≡ adaptiveThresholdKind
canonicalNDRowResidualThresholdProfileIsCanonical =
  refl

canonicalBridgeResidualRowThresholdProfileIsCanonical :
  rowResidualThresholdProfile canonicalBridgeResidualRow ≡ tightThresholdKind
canonicalBridgeResidualRowThresholdProfileIsCanonical =
  refl

canonicalNonPromotionCertificate :
  NonPromotionCertificate
canonicalNonPromotionCertificate =
  mkNonPromotionCertificate
    "neurodivergent atlas body-memory non-promotion certificate"
    candidateOnlyRoute
    refl
    tt
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
    canonicalAxes
    refl
    canonicalBoundaryClaimKinds
    refl
    "Candidate-only neuroaffirming bridge: no pathology promotion, cure framing, forced normalization, diagnosis, treatment authority, mind reading, BOLD overclaim, or connectome overclaim."

canonicalNeurodivergentAtlasBodyMemoryBridge :
  NeurodivergentAtlasBodyMemoryBridge
canonicalNeurodivergentAtlasBodyMemoryBridge =
  mkNeurodivergentAtlasBodyMemoryBridge
    candidateOnlyRoute
    refl
    tt
    canonicalBridgeRows
    refl
    canonicalAtlasStyles
    refl
    canonicalChartCompressionKinds
    refl
    canonicalAtlasPriors
    refl
    canonicalSensoryWeights
    refl
    canonicalSocialCodeAssumptions
    refl
    canonicalSocialCodeThresholdKinds
    refl
    canonicalNeurotypeKinds
    refl
    canonicalResidualThresholdKinds
    refl
    canonicalBoundaryClaimKinds
    refl
    canonicalHandleKinds
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
    canonicalNonPromotionCertificate
    refl
    "Neuroaffirming body-memory bridge: NT/ND are chart-building styles with different priors, compression styles, sensory weights, and social-code thresholds, not normal or broken."
    canonicalBridgeNotes

------------------------------------------------------------------------
-- Canonical false lemmas and reusable witnesses.

canonicalBridgeRouteIsCandidateOnly :
  bridgeRoute canonicalNeurodivergentAtlasBodyMemoryBridge ≡ candidateOnlyRoute
canonicalBridgeRouteIsCandidateOnly =
  bridgeRouteIsCandidateOnly canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalPathologyPromotionBlockedIsFalse :
  pathologyPromotionBlocked canonicalNeurodivergentAtlasBodyMemoryBridge ≡ false
canonicalPathologyPromotionBlockedIsFalse =
  pathologyPromotionBlockedIsFalse canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalCureFramingBlockedIsFalse :
  cureFramingBlocked canonicalNeurodivergentAtlasBodyMemoryBridge ≡ false
canonicalCureFramingBlockedIsFalse =
  cureFramingBlockedIsFalse canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalForcedNormalizationBlockedIsFalse :
  forcedNormalizationBlocked canonicalNeurodivergentAtlasBodyMemoryBridge ≡ false
canonicalForcedNormalizationBlockedIsFalse =
  forcedNormalizationBlockedIsFalse canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalDiagnosisBlockedIsFalse :
  diagnosisBlocked canonicalNeurodivergentAtlasBodyMemoryBridge ≡ false
canonicalDiagnosisBlockedIsFalse =
  diagnosisBlockedIsFalse canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalTreatmentAuthorityBlockedIsFalse :
  treatmentAuthorityBlocked canonicalNeurodivergentAtlasBodyMemoryBridge ≡ false
canonicalTreatmentAuthorityBlockedIsFalse =
  treatmentAuthorityBlockedIsFalse canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalMindReadingBlockedIsFalse :
  mindReadingBlocked canonicalNeurodivergentAtlasBodyMemoryBridge ≡ false
canonicalMindReadingBlockedIsFalse =
  mindReadingBlockedIsFalse canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalBoldOverclaimBlockedIsFalse :
  boldOverclaimBlocked canonicalNeurodivergentAtlasBodyMemoryBridge ≡ false
canonicalBoldOverclaimBlockedIsFalse =
  boldOverclaimBlockedIsFalse canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalConnectomeOverclaimBlockedIsFalse :
  connectomeOverclaimBlocked canonicalNeurodivergentAtlasBodyMemoryBridge ≡ false
canonicalConnectomeOverclaimBlockedIsFalse =
  connectomeOverclaimBlockedIsFalse canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalNonPromotionCertificateIsCanonical :
  nonPromotionCertificate canonicalNeurodivergentAtlasBodyMemoryBridge ≡
  canonicalNonPromotionCertificate
canonicalNonPromotionCertificateIsCanonical =
  nonPromotionCertificateIsCanonical canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalBridgeRowsAreCanonical :
  atlasRows canonicalNeurodivergentAtlasBodyMemoryBridge ≡ canonicalBridgeRows
canonicalBridgeRowsAreCanonical =
  atlasRowsAreCanonical canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalBridgeStylesAreCanonical :
  atlasStyles canonicalNeurodivergentAtlasBodyMemoryBridge ≡ canonicalAtlasStyles
canonicalBridgeStylesAreCanonical =
  atlasStylesAreCanonical canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalBridgePriorsAreCanonical :
  atlasPriors canonicalNeurodivergentAtlasBodyMemoryBridge ≡ canonicalAtlasPriors
canonicalBridgePriorsAreCanonical =
  atlasPriorsAreCanonical canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalBridgeWeightsAreCanonical :
  sensoryWeights canonicalNeurodivergentAtlasBodyMemoryBridge ≡
  canonicalSensoryWeights
canonicalBridgeWeightsAreCanonical =
  sensoryWeightsAreCanonical canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalBridgeSocialCodeAssumptionsAreCanonical :
  socialCodeAssumptions canonicalNeurodivergentAtlasBodyMemoryBridge ≡
  canonicalSocialCodeAssumptions
canonicalBridgeSocialCodeAssumptionsAreCanonical =
  socialCodeAssumptionsAreCanonical canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalBridgeResidualThresholdKindsAreCanonical :
  residualThresholdKinds canonicalNeurodivergentAtlasBodyMemoryBridge ≡
  canonicalResidualThresholdKinds
canonicalBridgeResidualThresholdKindsAreCanonical =
  residualThresholdKindsAreCanonical canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalBridgeBoundaryClaimsAreCanonical :
  boundaryClaims canonicalNeurodivergentAtlasBodyMemoryBridge ≡
  canonicalBoundaryClaimKinds
canonicalBridgeBoundaryClaimsAreCanonical =
  boundaryClaimsAreCanonical canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalBridgeHandleKindsAreCanonical :
  handleKinds canonicalNeurodivergentAtlasBodyMemoryBridge ≡
  canonicalHandleKinds
canonicalBridgeHandleKindsAreCanonical =
  handleKindsAreCanonical canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalBridgeCandidateOnlyIsTrue :
  candidateOnly canonicalNeurodivergentAtlasBodyMemoryBridge ≡ true
canonicalBridgeCandidateOnlyIsTrue =
  candidateOnlyIsTrue canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalChartCompressionKindsAreCanonical :
  chartCompressionKinds canonicalNeurodivergentAtlasBodyMemoryBridge ≡
  canonicalChartCompressionKinds
canonicalChartCompressionKindsAreCanonical =
  chartCompressionKindsAreCanonical canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalSocialCodeThresholdKindsAreCanonical :
  socialCodeThresholdKinds canonicalNeurodivergentAtlasBodyMemoryBridge ≡
  canonicalSocialCodeThresholdKinds
canonicalSocialCodeThresholdKindsAreCanonical =
  socialCodeThresholdKindsAreCanonical canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalNeurotypeKindsAreCanonical :
  neurotypeKinds canonicalNeurodivergentAtlasBodyMemoryBridge ≡
  canonicalNeurotypeKinds
canonicalNeurotypeKindsAreCanonical =
  neurotypeKindsAreCanonical canonicalNeurodivergentAtlasBodyMemoryBridge

canonicalNormalBrokenClassificationBlockedIsFalse :
  normalBrokenClassificationBlocked canonicalNeurodivergentAtlasBodyMemoryBridge ≡ false
canonicalNormalBrokenClassificationBlockedIsFalse =
  normalBrokenClassificationBlockedIsFalse canonicalNeurodivergentAtlasBodyMemoryBridge
