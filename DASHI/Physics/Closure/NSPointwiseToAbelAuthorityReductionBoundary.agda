module DASHI.Physics.Closure.NSPointwiseToAbelAuthorityReductionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS A6 pointwise-to-Abel authority reduction boundary.
--
-- This receipt records the latest A6 transfer route as an authority
-- reduction surface, not as a new Clay or terminal theorem.  It is
-- intentionally builtin-only so it can be checked with --no-libraries.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Recorded child-boundary anchors.

a3StationarityBoundaryReference : String
a3StationarityBoundaryReference =
  "DASHI.Physics.Closure.NSAbelTriadicStationarityConstructionBoundary"

diagonalBoundaryReference : String
diagonalBoundaryReference =
  "DASHI.Physics.Closure.NSDiagonalStretchingToAbelMeanBoundary"

offDiagonalBoundaryReference : String
offDiagonalBoundaryReference =
  "DASHI.Physics.Closure.NSOffDiagonalShellAbsorptionBoundary"

localizationPressureBoundaryReference : String
localizationPressureBoundaryReference =
  "DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary"

llnBoundaryReference : String
llnBoundaryReference =
  "DASHI.Physics.Closure.NSAbelShellMixingLLNBoundary"

compositeA6BoundaryReference : String
compositeA6BoundaryReference =
  "DASHI.Physics.Closure.NSPointwiseToAbelCompositeA6Boundary"

a3StationarityImported : Bool
a3StationarityImported =
  true

diagonalBoundaryImported : Bool
diagonalBoundaryImported =
  true

offDiagonalBoundaryImported : Bool
offDiagonalBoundaryImported =
  true

localizationPressureBoundaryImported : Bool
localizationPressureBoundaryImported =
  true

llnBoundaryImported : Bool
llnBoundaryImported =
  true

compositeA6BoundaryImported : Bool
compositeA6BoundaryImported =
  true

record ImportedAuthorityReductionSupport : Set where
  field
    a3StationarityImportedIsTrue :
      a3StationarityImported ≡ true
    diagonalBoundaryImportedIsTrue :
      diagonalBoundaryImported ≡ true
    offDiagonalBoundaryImportedIsTrue :
      offDiagonalBoundaryImported ≡ true
    localizationPressureBoundaryImportedIsTrue :
      localizationPressureBoundaryImported ≡ true
    llnBoundaryImportedIsTrue :
      llnBoundaryImported ≡ true
    compositeA6BoundaryImportedIsTrue :
      compositeA6BoundaryImported ≡ true

canonicalImportedAuthorityReductionSupport :
  ImportedAuthorityReductionSupport
canonicalImportedAuthorityReductionSupport =
  record
    { a3StationarityImportedIsTrue =
        refl
    ; diagonalBoundaryImportedIsTrue =
        refl
    ; offDiagonalBoundaryImportedIsTrue =
        refl
    ; localizationPressureBoundaryImportedIsTrue =
        refl
    ; llnBoundaryImportedIsTrue =
        refl
    ; compositeA6BoundaryImportedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Route rows.

data AuthorityReductionRouteFlag : Set where
  route-A3StationarityHandoff :
    AuthorityReductionRouteFlag
  route-DiagonalSameShellStretchingIdentification :
    AuthorityReductionRouteFlag
  route-OffDiagonalCoifmanMeyerAbsorption :
    AuthorityReductionRouteFlag
  route-LocalizationPressureCommutatorControl :
    AuthorityReductionRouteFlag
  route-HarmonicPressureTailControl :
    AuthorityReductionRouteFlag
  route-AbelShellMixingLLNDownstreamOfA3 :
    AuthorityReductionRouteFlag
  route-CompositeA6ImportedAsPriorSurface :
    AuthorityReductionRouteFlag
  route-AuthorityReductionNonPromotingGuard :
    AuthorityReductionRouteFlag

canonicalAuthorityReductionRouteFlags :
  List AuthorityReductionRouteFlag
canonicalAuthorityReductionRouteFlags =
  route-A3StationarityHandoff
  ∷ route-DiagonalSameShellStretchingIdentification
  ∷ route-OffDiagonalCoifmanMeyerAbsorption
  ∷ route-LocalizationPressureCommutatorControl
  ∷ route-HarmonicPressureTailControl
  ∷ route-AbelShellMixingLLNDownstreamOfA3
  ∷ route-CompositeA6ImportedAsPriorSurface
  ∷ route-AuthorityReductionNonPromotingGuard
  ∷ []

authorityReductionRouteFlagCount : Nat
authorityReductionRouteFlagCount =
  listLength canonicalAuthorityReductionRouteFlags

authorityReductionRouteFlagCountIs8 :
  authorityReductionRouteFlagCount ≡ 8
authorityReductionRouteFlagCountIs8 =
  refl

data TransferPayloadLine : Set where
  payloadSameShellDiagonalXiJR :
    TransferPayloadLine
  payloadDiagonalAbelMeasureMuRDiag :
    TransferPayloadLine
  payloadOffDiagonalDyadicCoifmanMeyer :
    TransferPayloadLine
  payloadEpsilonGradientAbsorption :
    TransferPayloadLine
  payloadLocalizedCutoffCommutator :
    TransferPayloadLine
  payloadLerayPressureReconstruction :
    TransferPayloadLine
  payloadHarmonicAndExteriorPressureTail :
    TransferPayloadLine
  payloadAbelWindowEffectiveSampleLLN :
    TransferPayloadLine
  payloadA3StationarityDefectAsDownstreamInput :
    TransferPayloadLine
  payloadNoClayOrTerminalConsequence :
    TransferPayloadLine

canonicalTransferPayloadLines :
  List TransferPayloadLine
canonicalTransferPayloadLines =
  payloadSameShellDiagonalXiJR
  ∷ payloadDiagonalAbelMeasureMuRDiag
  ∷ payloadOffDiagonalDyadicCoifmanMeyer
  ∷ payloadEpsilonGradientAbsorption
  ∷ payloadLocalizedCutoffCommutator
  ∷ payloadLerayPressureReconstruction
  ∷ payloadHarmonicAndExteriorPressureTail
  ∷ payloadAbelWindowEffectiveSampleLLN
  ∷ payloadA3StationarityDefectAsDownstreamInput
  ∷ payloadNoClayOrTerminalConsequence
  ∷ []

transferPayloadLineCount : Nat
transferPayloadLineCount =
  listLength canonicalTransferPayloadLines

transferPayloadLineCountIs10 :
  transferPayloadLineCount ≡ 10
transferPayloadLineCountIs10 =
  refl

data AuthorityReductionDependencyEdge : Set where
  edge-A3StationarityToAbelLLN :
    AuthorityReductionDependencyEdge
  edge-DiagonalIdentificationToTransfer :
    AuthorityReductionDependencyEdge
  edge-OffDiagonalAbsorptionToTransfer :
    AuthorityReductionDependencyEdge
  edge-LocalizationPressureToTransfer :
    AuthorityReductionDependencyEdge
  edge-HarmonicTailToPressureBudget :
    AuthorityReductionDependencyEdge
  edge-LLNToAbelShellMean :
    AuthorityReductionDependencyEdge
  edge-CompositeA6ToDownstreamReceipt :
    AuthorityReductionDependencyEdge
  edge-TransferReceiptToPromotionGuards :
    AuthorityReductionDependencyEdge

canonicalAuthorityReductionDependencyEdges :
  List AuthorityReductionDependencyEdge
canonicalAuthorityReductionDependencyEdges =
  edge-A3StationarityToAbelLLN
  ∷ edge-DiagonalIdentificationToTransfer
  ∷ edge-OffDiagonalAbsorptionToTransfer
  ∷ edge-LocalizationPressureToTransfer
  ∷ edge-HarmonicTailToPressureBudget
  ∷ edge-LLNToAbelShellMean
  ∷ edge-CompositeA6ToDownstreamReceipt
  ∷ edge-TransferReceiptToPromotionGuards
  ∷ []

authorityReductionDependencyEdgeCount : Nat
authorityReductionDependencyEdgeCount =
  listLength canonicalAuthorityReductionDependencyEdges

authorityReductionDependencyEdgeCountIs8 :
  authorityReductionDependencyEdgeCount ≡ 8
authorityReductionDependencyEdgeCountIs8 =
  refl

diagonalSameShellStretchingIdentificationRecorded : Bool
diagonalSameShellStretchingIdentificationRecorded =
  true

offDiagonalCoifmanMeyerAbsorptionRecorded : Bool
offDiagonalCoifmanMeyerAbsorptionRecorded =
  true

localizationPressureCommutatorControlRecorded : Bool
localizationPressureCommutatorControlRecorded =
  true

harmonicTailControlRecorded : Bool
harmonicTailControlRecorded =
  true

abelShellMixingLLNDownstreamOfA3Recorded : Bool
abelShellMixingLLNDownstreamOfA3Recorded =
  true

authorityReductionRouteRecorded : Bool
authorityReductionRouteRecorded =
  true

a6TransferPromoted : Bool
a6TransferPromoted =
  false

nsClayPromoted : Bool
nsClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

terminalUnificationPromoted : Bool
terminalUnificationPromoted =
  false

sameShellStretchingIdentificationText : String
sameShellStretchingIdentificationText =
  "Diagonal same-shell stretching route: identify localized P_j omega . S(P_j u) P_j omega with the diagonal Abel measure before mixing."

offDiagonalAbsorptionText : String
offDiagonalAbsorptionText =
  "Off-diagonal route: high-low, low-high, high-high, pressure, cutoff, and Abel-tail terms are absorbed by dyadic almost orthogonality and Coifman-Meyer absorption."

localizationPressureTailText : String
localizationPressureTailText =
  "Localization / pressure commutator route: cutoff derivatives, Leray pressure reconstruction, local Calderon-Zygmund core, harmonic pressure tail, exterior annuli, and shell off-window tails are lower-order or epsilon-absorbed budgets."

llnDownstreamOfA3Text : String
llnDownstreamOfA3Text =
  "Abel shell-mixing LLN downstream of A3 stationarity: the A3 stationarity defect is an input error before the finite log-window shell mean is replaced by the Abel mean."

nonPromotionGuardText : String
nonPromotionGuardText =
  "Authority reduction boundary only: a6TransferPromoted, nsClayPromoted, terminalPromotion, and terminalUnificationPromoted remain false."

orcsLpgfSummary : String
orcsLpgfSummary =
  "O NS A6 pointwise-to-Abel authority-reduction boundary; R record diagonal same-shell stretching, off-diagonal Coifman-Meyer absorption, localization / pressure commutator / harmonic pressure tail controls, and Abel shell-mixing LLN downstream of A3 stationarity; C builtin-only Agda receipt with child-boundary anchors; S route flags true while a6TransferPromoted, nsClayPromoted, and terminal promotion are false; L A3 stationarity -> Abel LLN plus diagonal/off-diagonal/localization children -> guarded transfer receipt; P expose the receipt for audit only; G no Clay or terminal authority is created; F route recorded, promotions false."

record NSPointwiseToAbelAuthorityReductionBoundary : Set where
  field
    importedSupport :
      ImportedAuthorityReductionSupport
    routeFlags :
      List AuthorityReductionRouteFlag
    routeFlagCountProof :
      authorityReductionRouteFlagCount ≡ 8
    payloadLines :
      List TransferPayloadLine
    payloadLineCountProof :
      transferPayloadLineCount ≡ 10
    dependencyEdges :
      List AuthorityReductionDependencyEdge
    dependencyEdgeCountProof :
      authorityReductionDependencyEdgeCount ≡ 8
    sameShellStretchingText :
      String
    offDiagonalAbsorptionSummary :
      String
    localizationPressureTailSummary :
      String
    llnDownstreamOfA3Summary :
      String
    nonPromotionGuard :
      String
    summary :
      String
    diagonalSameShellStretchingIdentificationRecordedIsTrue :
      diagonalSameShellStretchingIdentificationRecorded ≡ true
    offDiagonalCoifmanMeyerAbsorptionRecordedIsTrue :
      offDiagonalCoifmanMeyerAbsorptionRecorded ≡ true
    localizationPressureCommutatorControlRecordedIsTrue :
      localizationPressureCommutatorControlRecorded ≡ true
    harmonicTailControlRecordedIsTrue :
      harmonicTailControlRecorded ≡ true
    abelShellMixingLLNDownstreamOfA3RecordedIsTrue :
      abelShellMixingLLNDownstreamOfA3Recorded ≡ true
    authorityReductionRouteRecordedIsTrue :
      authorityReductionRouteRecorded ≡ true
    a6TransferPromotedIsFalse :
      a6TransferPromoted ≡ false
    nsClayPromotedIsFalse :
      nsClayPromoted ≡ false
    terminalPromotionIsFalse :
      terminalPromotion ≡ false
    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

canonicalNSPointwiseToAbelAuthorityReductionBoundary :
  NSPointwiseToAbelAuthorityReductionBoundary
canonicalNSPointwiseToAbelAuthorityReductionBoundary =
  record
    { importedSupport =
        canonicalImportedAuthorityReductionSupport
    ; routeFlags =
        canonicalAuthorityReductionRouteFlags
    ; routeFlagCountProof =
        refl
    ; payloadLines =
        canonicalTransferPayloadLines
    ; payloadLineCountProof =
        refl
    ; dependencyEdges =
        canonicalAuthorityReductionDependencyEdges
    ; dependencyEdgeCountProof =
        refl
    ; sameShellStretchingText =
        sameShellStretchingIdentificationText
    ; offDiagonalAbsorptionSummary =
        offDiagonalAbsorptionText
    ; localizationPressureTailSummary =
        localizationPressureTailText
    ; llnDownstreamOfA3Summary =
        llnDownstreamOfA3Text
    ; nonPromotionGuard =
        nonPromotionGuardText
    ; summary =
        orcsLpgfSummary
    ; diagonalSameShellStretchingIdentificationRecordedIsTrue =
        refl
    ; offDiagonalCoifmanMeyerAbsorptionRecordedIsTrue =
        refl
    ; localizationPressureCommutatorControlRecordedIsTrue =
        refl
    ; harmonicTailControlRecordedIsTrue =
        refl
    ; abelShellMixingLLNDownstreamOfA3RecordedIsTrue =
        refl
    ; authorityReductionRouteRecordedIsTrue =
        refl
    ; a6TransferPromotedIsFalse =
        refl
    ; nsClayPromotedIsFalse =
        refl
    ; terminalPromotionIsFalse =
        refl
    ; terminalUnificationPromotedIsFalse =
        refl
    }
