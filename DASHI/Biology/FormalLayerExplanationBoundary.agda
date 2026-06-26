module DASHI.Biology.FormalLayerExplanationBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Formal layer explanation boundary.
--
-- This module separates:
--   * myth / narrative / eigenvector / intuitive guide layers
--   * the typed proof surface
--   * clinical / educational / legal authority surfaces
--
-- It records that the explanation layer can guide a reader without turning
-- guidance into truth claims or authority promotions.

data RouteKind : Set where
  mythNarrativeRoute :
    RouteKind

  narrativeGuideRoute :
    RouteKind

  eigenvectorIntuitionRoute :
    RouteKind

  intuitiveGuideRoute :
    RouteKind

  typedProofSurfaceRoute :
    RouteKind

  clinicalAuthorityRoute :
    RouteKind

  educationalAuthorityRoute :
    RouteKind

  legalAuthorityRoute :
    RouteKind

routeKindName : RouteKind → String
routeKindName mythNarrativeRoute =
  "myth-narrative-route"
routeKindName narrativeGuideRoute =
  "narrative-guide-route"
routeKindName eigenvectorIntuitionRoute =
  "eigenvector-intuition-route"
routeKindName intuitiveGuideRoute =
  "intuitive-guide-route"
routeKindName typedProofSurfaceRoute =
  "typed-proof-surface-route"
routeKindName clinicalAuthorityRoute =
  "clinical-authority-route"
routeKindName educationalAuthorityRoute =
  "educational-authority-route"
routeKindName legalAuthorityRoute =
  "legal-authority-route"

routeKindIsGuideSurface : RouteKind → Bool
routeKindIsGuideSurface mythNarrativeRoute =
  true
routeKindIsGuideSurface narrativeGuideRoute =
  true
routeKindIsGuideSurface eigenvectorIntuitionRoute =
  true
routeKindIsGuideSurface intuitiveGuideRoute =
  true
routeKindIsGuideSurface typedProofSurfaceRoute =
  false
routeKindIsGuideSurface clinicalAuthorityRoute =
  false
routeKindIsGuideSurface educationalAuthorityRoute =
  false
routeKindIsGuideSurface legalAuthorityRoute =
  false

routeKindIsProofSurface : RouteKind → Bool
routeKindIsProofSurface mythNarrativeRoute =
  false
routeKindIsProofSurface narrativeGuideRoute =
  false
routeKindIsProofSurface eigenvectorIntuitionRoute =
  false
routeKindIsProofSurface intuitiveGuideRoute =
  false
routeKindIsProofSurface typedProofSurfaceRoute =
  true
routeKindIsProofSurface clinicalAuthorityRoute =
  false
routeKindIsProofSurface educationalAuthorityRoute =
  false
routeKindIsProofSurface legalAuthorityRoute =
  false

routeKindIsAuthoritySurface : RouteKind → Bool
routeKindIsAuthoritySurface mythNarrativeRoute =
  false
routeKindIsAuthoritySurface narrativeGuideRoute =
  false
routeKindIsAuthoritySurface eigenvectorIntuitionRoute =
  false
routeKindIsAuthoritySurface intuitiveGuideRoute =
  false
routeKindIsAuthoritySurface typedProofSurfaceRoute =
  false
routeKindIsAuthoritySurface clinicalAuthorityRoute =
  true
routeKindIsAuthoritySurface educationalAuthorityRoute =
  true
routeKindIsAuthoritySurface legalAuthorityRoute =
  true

canonicalRouteKinds : List RouteKind
canonicalRouteKinds =
  mythNarrativeRoute
  ∷ narrativeGuideRoute
  ∷ eigenvectorIntuitionRoute
  ∷ intuitiveGuideRoute
  ∷ typedProofSurfaceRoute
  ∷ clinicalAuthorityRoute
  ∷ educationalAuthorityRoute
  ∷ legalAuthorityRoute
  ∷ []

data ExplanationLayer : Set where
  mythLayer :
    ExplanationLayer

  narrativeLayer :
    ExplanationLayer

  eigenvectorLayer :
    ExplanationLayer

  intuitiveGuideLayer :
    ExplanationLayer

  typedProofSurfaceLayer :
    ExplanationLayer

  clinicalAuthorityLayer :
    ExplanationLayer

  educationalAuthorityLayer :
    ExplanationLayer

  legalAuthorityLayer :
    ExplanationLayer

layerName : ExplanationLayer → String
layerName mythLayer =
  "myth-layer"
layerName narrativeLayer =
  "narrative-layer"
layerName eigenvectorLayer =
  "eigenvector-layer"
layerName intuitiveGuideLayer =
  "intuitive-guide-layer"
layerName typedProofSurfaceLayer =
  "typed-proof-surface-layer"
layerName clinicalAuthorityLayer =
  "clinical-authority-layer"
layerName educationalAuthorityLayer =
  "educational-authority-layer"
layerName legalAuthorityLayer =
  "legal-authority-layer"

routeKindSourceLayer : RouteKind → ExplanationLayer
routeKindSourceLayer mythNarrativeRoute =
  mythLayer
routeKindSourceLayer narrativeGuideRoute =
  narrativeLayer
routeKindSourceLayer eigenvectorIntuitionRoute =
  eigenvectorLayer
routeKindSourceLayer intuitiveGuideRoute =
  intuitiveGuideLayer
routeKindSourceLayer typedProofSurfaceRoute =
  typedProofSurfaceLayer
routeKindSourceLayer clinicalAuthorityRoute =
  clinicalAuthorityLayer
routeKindSourceLayer educationalAuthorityRoute =
  educationalAuthorityLayer
routeKindSourceLayer legalAuthorityRoute =
  legalAuthorityLayer

routeKindTargetLayer : RouteKind → ExplanationLayer
routeKindTargetLayer mythNarrativeRoute =
  narrativeLayer
routeKindTargetLayer narrativeGuideRoute =
  intuitiveGuideLayer
routeKindTargetLayer eigenvectorIntuitionRoute =
  intuitiveGuideLayer
routeKindTargetLayer intuitiveGuideRoute =
  typedProofSurfaceLayer
routeKindTargetLayer typedProofSurfaceRoute =
  typedProofSurfaceLayer
routeKindTargetLayer clinicalAuthorityRoute =
  clinicalAuthorityLayer
routeKindTargetLayer educationalAuthorityRoute =
  educationalAuthorityLayer
routeKindTargetLayer legalAuthorityRoute =
  legalAuthorityLayer

record ExplanationRow : Set where
  constructor mkExplanationRow
  field
    rowLabel :
      String

    rowRouteKind :
      RouteKind

    rowSourceLayer :
      ExplanationLayer

    rowTargetLayer :
      ExplanationLayer

    rowGuideText :
      String

    rowTypedSurfaceText :
      String

    rowAuthorityText :
      String

    rowReaderComprehensionBoundary :
      Bool

    rowJargonCollapseBlocked :
      Bool

    rowProofOfTruthClaimed :
      Bool

    rowAuthorityPromotionClaimed :
      Bool

open ExplanationRow public

canonicalExplanationRowForRoute :
  String →
  RouteKind →
  String →
  String →
  String →
  ExplanationRow
canonicalExplanationRowForRoute label kind guideText proofText authorityText =
  mkExplanationRow
    label
    kind
    (routeKindSourceLayer kind)
    (routeKindTargetLayer kind)
    guideText
    proofText
    authorityText
    true
    true
    false
    false

canonicalMythNarrativeRow : ExplanationRow
canonicalMythNarrativeRow =
  canonicalExplanationRowForRoute
    "myth-narrative-row"
    mythNarrativeRoute
    "myth and narrative can guide orientation without becoming proof"
    "typed proof is not present on the myth-narrative route"
    "mythic framing does not promote clinical, educational, or legal authority"

canonicalNarrativeGuideRow : ExplanationRow
canonicalNarrativeGuideRow =
  canonicalExplanationRowForRoute
    "narrative-guide-row"
    narrativeGuideRoute
    "narrative guides reader attention toward the intended layer boundary"
    "narrative guidance is not itself a proof surface"
    "narrative guidance does not become authority"

canonicalEigenvectorIntuitionRow : ExplanationRow
canonicalEigenvectorIntuitionRow =
  canonicalExplanationRowForRoute
    "eigenvector-intuition-row"
    eigenvectorIntuitionRoute
    "eigenvector talk may supply intuition for structure"
    "intuition from linear algebra is not a proof of truth"
    "intuition does not promote clinical, educational, or legal authority"

canonicalIntuitiveGuideRow : ExplanationRow
canonicalIntuitiveGuideRow =
  canonicalExplanationRowForRoute
    "intuitive-guide-row"
    intuitiveGuideRoute
    "an intuitive guide can explain where the proof surface begins"
    "the guide is still not the proof surface"
    "the guide does not add authority"

canonicalTypedProofSurfaceRow : ExplanationRow
canonicalTypedProofSurfaceRow =
  canonicalExplanationRowForRoute
    "typed-proof-surface-row"
    typedProofSurfaceRoute
    "typed proof surface names judgments and derivations"
    "typing is structure, not a proof of social or clinical truth"
    "typed proof surface does not promote authority"

canonicalClinicalAuthorityRow : ExplanationRow
canonicalClinicalAuthorityRow =
  canonicalExplanationRowForRoute
    "clinical-authority-row"
    clinicalAuthorityRoute
    "clinical authority requires evidence, governance, and consent beyond exposition"
    "clinical authority is not created by terminology alone"
    "clinical authority is named, not promoted, by this boundary"

canonicalEducationalAuthorityRow : ExplanationRow
canonicalEducationalAuthorityRow =
  canonicalExplanationRowForRoute
    "educational-authority-row"
    educationalAuthorityRoute
    "educational authority belongs to pedagogy and curriculum, not to the guide text"
    "an educational explanation is not a credential transfer"
    "educational authority is named, not promoted, by this boundary"

canonicalLegalAuthorityRow : ExplanationRow
canonicalLegalAuthorityRow =
  canonicalExplanationRowForRoute
    "legal-authority-row"
    legalAuthorityRoute
    "legal authority is a separate institutional surface"
    "legal naming does not turn explanation into legal effect"
    "legal authority is named, not promoted, by this boundary"

canonicalExplanationRows : List ExplanationRow
canonicalExplanationRows =
  canonicalMythNarrativeRow
  ∷ canonicalNarrativeGuideRow
  ∷ canonicalEigenvectorIntuitionRow
  ∷ canonicalIntuitiveGuideRow
  ∷ canonicalTypedProofSurfaceRow
  ∷ canonicalClinicalAuthorityRow
  ∷ canonicalEducationalAuthorityRow
  ∷ canonicalLegalAuthorityRow
  ∷ []

record ReaderComprehensionBoundary : Set where
  constructor mkReaderComprehensionBoundary
  field
    boundaryLabel :
      String

    guideRows :
      List ExplanationRow

    proofRows :
      List ExplanationRow

    authorityRows :
      List ExplanationRow

    readerCanDistinguishGuideFromProof :
      Bool

    readerCanDistinguishProofFromAuthority :
      Bool

    readerCanKeepJargonFromCollapsingLayers :
      Bool

    boundaryHolds :
      Bool

    boundaryStatement :
      String

open ReaderComprehensionBoundary public

canonicalReaderComprehensionBoundary :
  ReaderComprehensionBoundary
canonicalReaderComprehensionBoundary =
  mkReaderComprehensionBoundary
    "reader-comprehension-boundary"
    (canonicalMythNarrativeRow
     ∷ canonicalNarrativeGuideRow
     ∷ canonicalEigenvectorIntuitionRow
     ∷ canonicalIntuitiveGuideRow
     ∷ [])
    (canonicalTypedProofSurfaceRow ∷ [])
    (canonicalClinicalAuthorityRow
     ∷ canonicalEducationalAuthorityRow
     ∷ canonicalLegalAuthorityRow
     ∷ [])
    true
    true
    true
    true
    "reader comprehension separates guide, typed proof, and authority surfaces"

record NoJargonCollapseReceipt (row : ExplanationRow) : Set where
  constructor mkNoJargonCollapseReceipt
  field
    receiptLabel :
      String

    receiptRow :
      ExplanationRow

    receiptRowMatches :
      receiptRow ≡ row

    jargonCollapseBlocked :
      Bool

    jargonCollapseBlockedIsTrue :
      jargonCollapseBlocked ≡ true

    collapseWouldEraseLayerBoundary :
      String

open NoJargonCollapseReceipt public

canonicalNoJargonCollapseReceipt :
  NoJargonCollapseReceipt canonicalTypedProofSurfaceRow
canonicalNoJargonCollapseReceipt =
  mkNoJargonCollapseReceipt
    "typed-proof-surface-no-jargon-collapse"
    canonicalTypedProofSurfaceRow
    refl
    true
    refl
    "collapsing typed proof into jargon would erase the proof surface boundary"

record NoProofOfTruthReceipt (row : ExplanationRow) : Set where
  constructor mkNoProofOfTruthReceipt
  field
    receiptLabel :
      String

    receiptRow :
      ExplanationRow

    receiptRowMatches :
      receiptRow ≡ row

    proofOfTruthClaimed :
      Bool

    proofOfTruthClaimedIsFalse :
      proofOfTruthClaimed ≡ false

    typedSurfaceIsNotTruth :
      String

open NoProofOfTruthReceipt public

canonicalNoProofOfTruthReceipt :
  NoProofOfTruthReceipt canonicalTypedProofSurfaceRow
canonicalNoProofOfTruthReceipt =
  mkNoProofOfTruthReceipt
    "typed-proof-surface-no-proof-of-truth"
    canonicalTypedProofSurfaceRow
    refl
    false
    refl
    "typed proof surface gives form, not truth of social, clinical, or legal claims"

record NoAuthorityPromotionReceipt (row : ExplanationRow) : Set where
  constructor mkNoAuthorityPromotionReceipt
  field
    receiptLabel :
      String

    receiptRow :
      ExplanationRow

    receiptRowMatches :
      receiptRow ≡ row

    authorityPromotionClaimed :
      Bool

    authorityPromotionClaimedIsFalse :
      authorityPromotionClaimed ≡ false

    authoritySurfaceName :
      String

    authorityPromotionDoesNotOccur :
      String

open NoAuthorityPromotionReceipt public

canonicalNoClinicalAuthorityPromotionReceipt :
  NoAuthorityPromotionReceipt canonicalClinicalAuthorityRow
canonicalNoClinicalAuthorityPromotionReceipt =
  mkNoAuthorityPromotionReceipt
    "clinical-authority-no-promotion"
    canonicalClinicalAuthorityRow
    refl
    false
    refl
    "clinical-authority"
    "clinical authority is named but not promoted by this explanation boundary"

canonicalNoEducationalAuthorityPromotionReceipt :
  NoAuthorityPromotionReceipt canonicalEducationalAuthorityRow
canonicalNoEducationalAuthorityPromotionReceipt =
  mkNoAuthorityPromotionReceipt
    "educational-authority-no-promotion"
    canonicalEducationalAuthorityRow
    refl
    false
    refl
    "educational-authority"
    "educational authority is named but not promoted by this explanation boundary"

canonicalNoLegalAuthorityPromotionReceipt :
  NoAuthorityPromotionReceipt canonicalLegalAuthorityRow
canonicalNoLegalAuthorityPromotionReceipt =
  mkNoAuthorityPromotionReceipt
    "legal-authority-no-promotion"
    canonicalLegalAuthorityRow
    refl
    false
    refl
    "legal-authority"
    "legal authority is named but not promoted by this explanation boundary"

record FormalLayerExplanationBoundary : Set where
  constructor mkFormalLayerExplanationBoundary
  field
    boundaryLabel :
      String

    routeKinds :
      List RouteKind

    explanationRows :
      List ExplanationRow

    readerComprehensionBoundary :
      ReaderComprehensionBoundary

    noJargonCollapseReceipt :
      NoJargonCollapseReceipt canonicalTypedProofSurfaceRow

    noProofOfTruthReceipt :
      NoProofOfTruthReceipt canonicalTypedProofSurfaceRow

    noClinicalAuthorityPromotionReceipt :
      NoAuthorityPromotionReceipt canonicalClinicalAuthorityRow

    noEducationalAuthorityPromotionReceipt :
      NoAuthorityPromotionReceipt canonicalEducationalAuthorityRow

    noLegalAuthorityPromotionReceipt :
      NoAuthorityPromotionReceipt canonicalLegalAuthorityRow

    layerSeparationStatement :
      String

    proofSurfaceStatement :
      String

    authoritySurfaceStatement :
      String

    boundaryHolds :
      Bool

open FormalLayerExplanationBoundary public

canonicalFormalLayerExplanationBoundary :
  FormalLayerExplanationBoundary
canonicalFormalLayerExplanationBoundary =
  mkFormalLayerExplanationBoundary
    "formal-layer-explanation-boundary"
    canonicalRouteKinds
    canonicalExplanationRows
    canonicalReaderComprehensionBoundary
    canonicalNoJargonCollapseReceipt
    canonicalNoProofOfTruthReceipt
    canonicalNoClinicalAuthorityPromotionReceipt
    canonicalNoEducationalAuthorityPromotionReceipt
    canonicalNoLegalAuthorityPromotionReceipt
    "layer separation keeps myth, narrative, eigenvector intuition, typed proof, and authority apart"
    "typed proof surface is formal structure rather than social, clinical, educational, or legal truth"
    "authority surfaces are named as separate layers and are not promoted by explanation alone; cultural/operator explanations are interpretive only and neuro-affirming phrasing is not proof of social, clinical, neurological, or biological truth"
    true

canonicalBoundaryHolds :
  boundaryHolds canonicalFormalLayerExplanationBoundary ≡ true
canonicalBoundaryHolds =
  refl

canonicalReaderCanDistinguishGuideFromProof :
  readerCanDistinguishGuideFromProof
    canonicalReaderComprehensionBoundary
  ≡
  true
canonicalReaderCanDistinguishGuideFromProof =
  refl

canonicalReaderCanDistinguishProofFromAuthority :
  readerCanDistinguishProofFromAuthority
    canonicalReaderComprehensionBoundary
  ≡
  true
canonicalReaderCanDistinguishProofFromAuthority =
  refl

canonicalReaderCanKeepJargonFromCollapsingLayers :
  readerCanKeepJargonFromCollapsingLayers
    canonicalReaderComprehensionBoundary
  ≡
  true
canonicalReaderCanKeepJargonFromCollapsingLayers =
  refl

canonicalNoJargonCollapseBlocked :
  jargonCollapseBlocked canonicalNoJargonCollapseReceipt ≡ true
canonicalNoJargonCollapseBlocked =
  refl

canonicalNoProofOfTruthClaimedIsFalse :
  proofOfTruthClaimed canonicalNoProofOfTruthReceipt ≡ false
canonicalNoProofOfTruthClaimedIsFalse =
  refl

canonicalNoClinicalAuthorityPromotionClaimedIsFalse :
  authorityPromotionClaimed canonicalNoClinicalAuthorityPromotionReceipt ≡ false
canonicalNoClinicalAuthorityPromotionClaimedIsFalse =
  refl

canonicalNoEducationalAuthorityPromotionClaimedIsFalse :
  authorityPromotionClaimed canonicalNoEducationalAuthorityPromotionReceipt ≡ false
canonicalNoEducationalAuthorityPromotionClaimedIsFalse =
  refl

canonicalNoLegalAuthorityPromotionClaimedIsFalse :
  authorityPromotionClaimed canonicalNoLegalAuthorityPromotionReceipt ≡ false
canonicalNoLegalAuthorityPromotionClaimedIsFalse =
  refl

------------------------------------------------------------------------
-- Cultural/operator explanation and neuro-affirming limits.

data CulturalOperatorRouteKind : Set where
  culturalGuideRoute :
    CulturalOperatorRouteKind

  operatorGuideRoute :
    CulturalOperatorRouteKind

  neuroAffirmingGuideRoute :
    CulturalOperatorRouteKind

  socialTruthClaimRoute :
    CulturalOperatorRouteKind

  clinicalTruthClaimRoute :
    CulturalOperatorRouteKind

  neurologicalTruthClaimRoute :
    CulturalOperatorRouteKind

  biologicalTruthClaimRoute :
    CulturalOperatorRouteKind

  operatorAuthorityRoute :
    CulturalOperatorRouteKind

  culturalAuthorityRoute :
    CulturalOperatorRouteKind

  neuroAuthorityRoute :
    CulturalOperatorRouteKind

routeKindNameCulturalOperator :
  CulturalOperatorRouteKind → String
routeKindNameCulturalOperator culturalGuideRoute =
  "cultural-guide-route"
routeKindNameCulturalOperator operatorGuideRoute =
  "operator-guide-route"
routeKindNameCulturalOperator neuroAffirmingGuideRoute =
  "neuro-affirming-guide-route"
routeKindNameCulturalOperator socialTruthClaimRoute =
  "social-truth-claim-route"
routeKindNameCulturalOperator clinicalTruthClaimRoute =
  "clinical-truth-claim-route"
routeKindNameCulturalOperator neurologicalTruthClaimRoute =
  "neurological-truth-claim-route"
routeKindNameCulturalOperator biologicalTruthClaimRoute =
  "biological-truth-claim-route"
routeKindNameCulturalOperator operatorAuthorityRoute =
  "operator-authority-route"
routeKindNameCulturalOperator culturalAuthorityRoute =
  "cultural-authority-route"
routeKindNameCulturalOperator neuroAuthorityRoute =
  "neuro-authority-route"

routeKindGuidesInterpretationOnly :
  CulturalOperatorRouteKind → Bool
routeKindGuidesInterpretationOnly culturalGuideRoute =
  true
routeKindGuidesInterpretationOnly operatorGuideRoute =
  true
routeKindGuidesInterpretationOnly neuroAffirmingGuideRoute =
  true
routeKindGuidesInterpretationOnly socialTruthClaimRoute =
  false
routeKindGuidesInterpretationOnly clinicalTruthClaimRoute =
  false
routeKindGuidesInterpretationOnly neurologicalTruthClaimRoute =
  false
routeKindGuidesInterpretationOnly biologicalTruthClaimRoute =
  false
routeKindGuidesInterpretationOnly operatorAuthorityRoute =
  false
routeKindGuidesInterpretationOnly culturalAuthorityRoute =
  false
routeKindGuidesInterpretationOnly neuroAuthorityRoute =
  false

routeKindBlocksTruthClaims :
  CulturalOperatorRouteKind → Bool
routeKindBlocksTruthClaims culturalGuideRoute =
  true
routeKindBlocksTruthClaims operatorGuideRoute =
  true
routeKindBlocksTruthClaims neuroAffirmingGuideRoute =
  true
routeKindBlocksTruthClaims socialTruthClaimRoute =
  true
routeKindBlocksTruthClaims clinicalTruthClaimRoute =
  true
routeKindBlocksTruthClaims neurologicalTruthClaimRoute =
  true
routeKindBlocksTruthClaims biologicalTruthClaimRoute =
  true
routeKindBlocksTruthClaims operatorAuthorityRoute =
  true
routeKindBlocksTruthClaims culturalAuthorityRoute =
  true
routeKindBlocksTruthClaims neuroAuthorityRoute =
  true

routeKindBlocksAuthorityPromotion :
  CulturalOperatorRouteKind → Bool
routeKindBlocksAuthorityPromotion culturalGuideRoute =
  true
routeKindBlocksAuthorityPromotion operatorGuideRoute =
  true
routeKindBlocksAuthorityPromotion neuroAffirmingGuideRoute =
  true
routeKindBlocksAuthorityPromotion socialTruthClaimRoute =
  true
routeKindBlocksAuthorityPromotion clinicalTruthClaimRoute =
  true
routeKindBlocksAuthorityPromotion neurologicalTruthClaimRoute =
  true
routeKindBlocksAuthorityPromotion biologicalTruthClaimRoute =
  true
routeKindBlocksAuthorityPromotion operatorAuthorityRoute =
  true
routeKindBlocksAuthorityPromotion culturalAuthorityRoute =
  true
routeKindBlocksAuthorityPromotion neuroAuthorityRoute =
  true

canonicalCulturalOperatorRouteKinds : List CulturalOperatorRouteKind
canonicalCulturalOperatorRouteKinds =
  culturalGuideRoute
  ∷ operatorGuideRoute
  ∷ neuroAffirmingGuideRoute
  ∷ socialTruthClaimRoute
  ∷ clinicalTruthClaimRoute
  ∷ neurologicalTruthClaimRoute
  ∷ biologicalTruthClaimRoute
  ∷ operatorAuthorityRoute
  ∷ culturalAuthorityRoute
  ∷ neuroAuthorityRoute
  ∷ []

data CulturalOperatorExplanationRowKind : Set where
  culturalNarrativeRowKind :
    CulturalOperatorExplanationRowKind

  operatorInterpretationRowKind :
    CulturalOperatorExplanationRowKind

  neuroAffirmingBoundaryRowKind :
    CulturalOperatorExplanationRowKind

  socialTruthLimitRowKind :
    CulturalOperatorExplanationRowKind

  clinicalTruthLimitRowKind :
    CulturalOperatorExplanationRowKind

  neurologicalTruthLimitRowKind :
    CulturalOperatorExplanationRowKind

  biologicalTruthLimitRowKind :
    CulturalOperatorExplanationRowKind

  authorityBoundaryRowKind :
    CulturalOperatorExplanationRowKind

canonicalCulturalOperatorExplanationRowKinds :
  List CulturalOperatorExplanationRowKind
canonicalCulturalOperatorExplanationRowKinds =
  culturalNarrativeRowKind
  ∷ operatorInterpretationRowKind
  ∷ neuroAffirmingBoundaryRowKind
  ∷ socialTruthLimitRowKind
  ∷ clinicalTruthLimitRowKind
  ∷ neurologicalTruthLimitRowKind
  ∷ biologicalTruthLimitRowKind
  ∷ authorityBoundaryRowKind
  ∷ []

record CulturalOperatorExplanationRow : Set where
  constructor mkCulturalOperatorExplanationRow
  field
    rowIndex :
      Nat

    rowKind :
      CulturalOperatorExplanationRowKind

    rowRouteKind :
      CulturalOperatorRouteKind

    rowLabel :
      String

    rowLayerGuide :
      String

    rowLayerIsInterpretationOnly :
      Bool

    rowLayerIsInterpretationOnlyIsTrue :
      rowLayerIsInterpretationOnly ≡ true

    rowBlocksSocialTruthClaim :
      Bool

    rowBlocksSocialTruthClaimIsTrue :
      rowBlocksSocialTruthClaim ≡ true

    rowBlocksClinicalTruthClaim :
      Bool

    rowBlocksClinicalTruthClaimIsTrue :
      rowBlocksClinicalTruthClaim ≡ true

    rowBlocksNeurologicalTruthClaim :
      Bool

    rowBlocksNeurologicalTruthClaimIsTrue :
      rowBlocksNeurologicalTruthClaim ≡ true

    rowBlocksBiologicalTruthClaim :
      Bool

    rowBlocksBiologicalTruthClaimIsTrue :
      rowBlocksBiologicalTruthClaim ≡ true

    rowBlocksAuthorityPromotion :
      Bool

    rowBlocksAuthorityPromotionIsTrue :
      rowBlocksAuthorityPromotion ≡ true

    rowBoundaryStatement :
      String

open CulturalOperatorExplanationRow public

record CulturalOperatorExplanationCertificate
  (row : CulturalOperatorExplanationRow) :
  Set where
  constructor mkCulturalOperatorExplanationCertificate
  field
    certificateLabel :
      String

    receiptRow :
      CulturalOperatorExplanationRow

    receiptRowMatches :
      receiptRow ≡ row

    certificateRouteKindGuidesInterpretationOnly :
      Bool

    certificateRouteKindGuidesInterpretationOnlyMatches :
      certificateRouteKindGuidesInterpretationOnly ≡
      routeKindGuidesInterpretationOnly (rowRouteKind row)

    routeKindBlocksTruthClaimsIsTrue :
      routeKindBlocksTruthClaims (rowRouteKind row) ≡ true

    routeKindBlocksAuthorityPromotionIsTrue :
      routeKindBlocksAuthorityPromotion (rowRouteKind row) ≡ true

    rowInterpretationOnlyIsTrue :
      rowLayerIsInterpretationOnly row ≡ true

    rowBlocksSocialTruthClaimTrue :
      rowBlocksSocialTruthClaim row ≡ true

    rowBlocksClinicalTruthClaimTrue :
      rowBlocksClinicalTruthClaim row ≡ true

    rowBlocksNeurologicalTruthClaimTrue :
      rowBlocksNeurologicalTruthClaim row ≡ true

    rowBlocksBiologicalTruthClaimTrue :
      rowBlocksBiologicalTruthClaim row ≡ true

    rowBlocksAuthorityPromotionTrue :
      rowBlocksAuthorityPromotion row ≡ true

    certificateStatement :
      String

open CulturalOperatorExplanationCertificate public

culturalNarrativeExplanationRow :
  CulturalOperatorExplanationRow
culturalNarrativeExplanationRow =
  mkCulturalOperatorExplanationRow
    zero
    culturalNarrativeRowKind
    culturalGuideRoute
    "cultural narrative explanation row"
    "Cultural narrative can guide interpretation without becoming truth."
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
    "cultural narrative explanations remain interpretive, not evidentiary"

operatorInterpretationExplanationRow :
  CulturalOperatorExplanationRow
operatorInterpretationExplanationRow =
  mkCulturalOperatorExplanationRow
    (suc zero)
    operatorInterpretationRowKind
    operatorGuideRoute
    "operator interpretation explanation row"
    "Operator explanation guides reading, sequencing, and usage constraints."
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
    "operator explanations remain interpretation-only, not truth authority"

neuroAffirmingBoundaryExplanationRow :
  CulturalOperatorExplanationRow
neuroAffirmingBoundaryExplanationRow =
  mkCulturalOperatorExplanationRow
    (suc (suc zero))
    neuroAffirmingBoundaryRowKind
    neuroAffirmingGuideRoute
    "neuro-affirming boundary explanation row"
    "Neuro-affirming explanation can support interpretation without claiming neurological truth."
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
    "neuro-affirming explanation remains a guide, not a neurological proof"

socialTruthLimitExplanationRow :
  CulturalOperatorExplanationRow
socialTruthLimitExplanationRow =
  mkCulturalOperatorExplanationRow
    (suc (suc (suc zero)))
    socialTruthLimitRowKind
    socialTruthClaimRoute
    "social truth limit explanation row"
    "Social interpretation is not a proof of social truth."
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
    "social truth claims are blocked in the explanation boundary"

clinicalTruthLimitExplanationRow :
  CulturalOperatorExplanationRow
clinicalTruthLimitExplanationRow =
  mkCulturalOperatorExplanationRow
    (suc (suc (suc (suc zero))))
    clinicalTruthLimitRowKind
    clinicalTruthClaimRoute
    "clinical truth limit explanation row"
    "Clinical interpretation is not a diagnosis, treatment, or proof of clinical truth."
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
    "clinical truth claims are blocked in the explanation boundary"

neurologicalTruthLimitExplanationRow :
  CulturalOperatorExplanationRow
neurologicalTruthLimitExplanationRow =
  mkCulturalOperatorExplanationRow
    (suc (suc (suc (suc (suc zero)))))
    neurologicalTruthLimitRowKind
    neurologicalTruthClaimRoute
    "neurological truth limit explanation row"
    "Neuro-affirming phrasing can guide interpretation without proving neurological truth."
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
    "neurological truth claims are blocked in the explanation boundary"

biologicalTruthLimitExplanationRow :
  CulturalOperatorExplanationRow
biologicalTruthLimitExplanationRow =
  mkCulturalOperatorExplanationRow
    (suc (suc (suc (suc (suc (suc zero))))))
    biologicalTruthLimitRowKind
    biologicalTruthClaimRoute
    "biological truth limit explanation row"
    "Biological explanation can orient interpretation without proving biological truth."
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
    "biological truth claims are blocked in the explanation boundary"

authorityBoundaryExplanationRow :
  CulturalOperatorExplanationRow
authorityBoundaryExplanationRow =
  mkCulturalOperatorExplanationRow
    (suc (suc (suc (suc (suc (suc (suc zero)))))))
    authorityBoundaryRowKind
    operatorAuthorityRoute
    "authority boundary explanation row"
    "Explanation about authority stays descriptive and does not promote authority."
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
    "authority promotion is blocked at the explanation boundary"

canonicalCulturalOperatorExplanationRows :
  List CulturalOperatorExplanationRow
canonicalCulturalOperatorExplanationRows =
  culturalNarrativeExplanationRow
  ∷ operatorInterpretationExplanationRow
  ∷ neuroAffirmingBoundaryExplanationRow
  ∷ socialTruthLimitExplanationRow
  ∷ clinicalTruthLimitExplanationRow
  ∷ neurologicalTruthLimitExplanationRow
  ∷ biologicalTruthLimitExplanationRow
  ∷ authorityBoundaryExplanationRow
  ∷ []

record CulturalOperatorExplanationBoundary : Set where
  constructor mkCulturalOperatorExplanationBoundary
  field
    routeKinds :
      List CulturalOperatorRouteKind

    routeKindsAreCanonical :
      routeKinds ≡ canonicalCulturalOperatorRouteKinds

    rowKinds :
      List CulturalOperatorExplanationRowKind

    rowKindsAreCanonical :
      rowKinds ≡ canonicalCulturalOperatorExplanationRowKinds

    rows :
      List CulturalOperatorExplanationRow

    rowsAreCanonical :
      rows ≡ canonicalCulturalOperatorExplanationRows

    culturalNarrativeRowCertificate :
      CulturalOperatorExplanationCertificate
        culturalNarrativeExplanationRow

    operatorInterpretationRowCertificate :
      CulturalOperatorExplanationCertificate
        operatorInterpretationExplanationRow

    neuroAffirmingBoundaryRowCertificate :
      CulturalOperatorExplanationCertificate
        neuroAffirmingBoundaryExplanationRow

    socialTruthLimitRowCertificate :
      CulturalOperatorExplanationCertificate
        socialTruthLimitExplanationRow

    clinicalTruthLimitRowCertificate :
      CulturalOperatorExplanationCertificate
        clinicalTruthLimitExplanationRow

    neurologicalTruthLimitRowCertificate :
      CulturalOperatorExplanationCertificate
        neurologicalTruthLimitExplanationRow

    biologicalTruthLimitRowCertificate :
      CulturalOperatorExplanationCertificate
        biologicalTruthLimitExplanationRow

    authorityBoundaryRowCertificate :
      CulturalOperatorExplanationCertificate
        authorityBoundaryExplanationRow

    interpretationOnly :
      Bool

    interpretationOnlyIsTrue :
      interpretationOnly ≡ true

    socialTruthBlocked :
      Bool

    socialTruthBlockedIsTrue :
      socialTruthBlocked ≡ true

    clinicalTruthBlocked :
      Bool

    clinicalTruthBlockedIsTrue :
      clinicalTruthBlocked ≡ true

    neurologicalTruthBlocked :
      Bool

    neurologicalTruthBlockedIsTrue :
      neurologicalTruthBlocked ≡ true

    biologicalTruthBlocked :
      Bool

    biologicalTruthBlockedIsTrue :
      biologicalTruthBlocked ≡ true

    authorityPromotionBlocked :
      Bool

    authorityPromotionBlockedIsTrue :
      authorityPromotionBlocked ≡ true

    boundaryStatement :
      String

open CulturalOperatorExplanationBoundary public

canonicalCulturalOperatorExplanationBoundary :
  CulturalOperatorExplanationBoundary
canonicalCulturalOperatorExplanationBoundary =
  mkCulturalOperatorExplanationBoundary
    canonicalCulturalOperatorRouteKinds
    refl
    canonicalCulturalOperatorExplanationRowKinds
    refl
    canonicalCulturalOperatorExplanationRows
    refl
    (mkCulturalOperatorExplanationCertificate
      "cultural narrative explanation certificate"
      culturalNarrativeExplanationRow
      refl
      true
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      "cultural narrative explanations remain interpretive, not evidentiary")
    (mkCulturalOperatorExplanationCertificate
      "operator interpretation explanation certificate"
      operatorInterpretationExplanationRow
      refl
      true
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      "operator explanations remain interpretation-only, not truth authority")
    (mkCulturalOperatorExplanationCertificate
      "neuro-affirming boundary explanation certificate"
      neuroAffirmingBoundaryExplanationRow
      refl
      true
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      "neuro-affirming explanations remain guides, not neurological proof")
    (mkCulturalOperatorExplanationCertificate
      "social truth limit explanation certificate"
      socialTruthLimitExplanationRow
      refl
      false
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      "social truth claims are blocked in the explanation boundary")
    (mkCulturalOperatorExplanationCertificate
      "clinical truth limit explanation certificate"
      clinicalTruthLimitExplanationRow
      refl
      false
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      "clinical truth claims are blocked in the explanation boundary")
    (mkCulturalOperatorExplanationCertificate
      "neurological truth limit explanation certificate"
      neurologicalTruthLimitExplanationRow
      refl
      false
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      "neurological truth claims are blocked in the explanation boundary")
    (mkCulturalOperatorExplanationCertificate
      "biological truth limit explanation certificate"
      biologicalTruthLimitExplanationRow
      refl
      false
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      "biological truth claims are blocked in the explanation boundary")
    (mkCulturalOperatorExplanationCertificate
      "authority boundary explanation certificate"
      authorityBoundaryExplanationRow
      refl
      false
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      refl
      "authority promotion is blocked at the explanation boundary")
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
    "cultural/operator explanation remains interpretive, and neuro-affirming language is not proof of social, clinical, neurological, or biological truth"

culturalOperatorExplanationBoundaryHolds :
  interpretationOnly canonicalCulturalOperatorExplanationBoundary ≡ true
culturalOperatorExplanationBoundaryHolds =
  interpretationOnlyIsTrue canonicalCulturalOperatorExplanationBoundary

culturalOperatorExplanationBoundarySocialTruthBlocked :
  socialTruthBlocked canonicalCulturalOperatorExplanationBoundary ≡ true
culturalOperatorExplanationBoundarySocialTruthBlocked =
  socialTruthBlockedIsTrue canonicalCulturalOperatorExplanationBoundary

culturalOperatorExplanationBoundaryClinicalTruthBlocked :
  clinicalTruthBlocked canonicalCulturalOperatorExplanationBoundary ≡ true
culturalOperatorExplanationBoundaryClinicalTruthBlocked =
  clinicalTruthBlockedIsTrue canonicalCulturalOperatorExplanationBoundary

culturalOperatorExplanationBoundaryNeurologicalTruthBlocked :
  neurologicalTruthBlocked canonicalCulturalOperatorExplanationBoundary ≡ true
culturalOperatorExplanationBoundaryNeurologicalTruthBlocked =
  neurologicalTruthBlockedIsTrue canonicalCulturalOperatorExplanationBoundary

culturalOperatorExplanationBoundaryBiologicalTruthBlocked :
  biologicalTruthBlocked canonicalCulturalOperatorExplanationBoundary ≡ true
culturalOperatorExplanationBoundaryBiologicalTruthBlocked =
  biologicalTruthBlockedIsTrue canonicalCulturalOperatorExplanationBoundary

culturalOperatorExplanationBoundaryAuthorityBlocked :
  authorityPromotionBlocked canonicalCulturalOperatorExplanationBoundary ≡ true
culturalOperatorExplanationBoundaryAuthorityBlocked =
  authorityPromotionBlockedIsTrue canonicalCulturalOperatorExplanationBoundary
