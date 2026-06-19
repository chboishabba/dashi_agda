module DASHI.Physics.Closure.NSCollapseBoundaryEnergyQGronwallReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Fail-closed receipt for the collapseImpossible boundary-energy route.
--
-- This module records the Q(t) boundary-energy surface, the smooth
-- finite-energy data assumptions, the positive boundary gap g12 before
-- T*, the material derivative and boundary transport terms, the desired
-- d_t Q <= C Q inequality, the Gronwall consequence, and the explicit
-- commutator / transport blockers that remain unproved.
--
-- No promotion is recorded: collapseImpossiblePromoted = false and
-- Clay = false.

data NSCollapseBoundaryEnergyQGronwallStage : Set where
  qBoundaryFunctionalRecorded :
    NSCollapseBoundaryEnergyQGronwallStage
  smoothFiniteEnergyDataRecorded :
    NSCollapseBoundaryEnergyQGronwallStage
  positiveBoundaryGapBeforeTStarRecorded :
    NSCollapseBoundaryEnergyQGronwallStage
  materialDerivativeOfRatioRecorded :
    NSCollapseBoundaryEnergyQGronwallStage
  boundaryTransportTermsRecorded :
    NSCollapseBoundaryEnergyQGronwallStage
  targetDifferentialInequalityRecorded :
    NSCollapseBoundaryEnergyQGronwallStage
  gronwallBoundRecorded :
    NSCollapseBoundaryEnergyQGronwallStage
  finiteRatioConsequenceRecorded :
    NSCollapseBoundaryEnergyQGronwallStage
  commutatorEstimateBlockerRecorded :
    NSCollapseBoundaryEnergyQGronwallStage
  transportEstimateBlockerRecorded :
    NSCollapseBoundaryEnergyQGronwallStage
  collapseImpossibleAndClayFalseRecorded :
    NSCollapseBoundaryEnergyQGronwallStage

canonicalNSCollapseBoundaryEnergyQGronwallStages :
  List NSCollapseBoundaryEnergyQGronwallStage
canonicalNSCollapseBoundaryEnergyQGronwallStages =
  qBoundaryFunctionalRecorded
  ∷ smoothFiniteEnergyDataRecorded
  ∷ positiveBoundaryGapBeforeTStarRecorded
  ∷ materialDerivativeOfRatioRecorded
  ∷ boundaryTransportTermsRecorded
  ∷ targetDifferentialInequalityRecorded
  ∷ gronwallBoundRecorded
  ∷ finiteRatioConsequenceRecorded
  ∷ commutatorEstimateBlockerRecorded
  ∷ transportEstimateBlockerRecorded
  ∷ collapseImpossibleAndClayFalseRecorded
  ∷ []

data NSCollapseBoundaryEnergyQGronwallBlocker : Set where
  commutatorEstimateUnproved :
    NSCollapseBoundaryEnergyQGronwallBlocker
  transportEstimateUnproved :
    NSCollapseBoundaryEnergyQGronwallBlocker

canonicalNSCollapseBoundaryEnergyQGronwallBlockers :
  List NSCollapseBoundaryEnergyQGronwallBlocker
canonicalNSCollapseBoundaryEnergyQGronwallBlockers =
  commutatorEstimateUnproved
  ∷ transportEstimateUnproved
  ∷ []

qBoundaryFunctionalText : String
qBoundaryFunctionalText =
  "Q(t) = ∫_{∂Ω_K} |<omega,e2>|^2 / g12^2 dH2"

smoothFiniteEnergyDataText : String
smoothFiniteEnergyDataText =
  "smooth finite-energy data"

positiveBoundaryGapBeforeTStarText : String
positiveBoundaryGapBeforeTStarText =
  "g12 > 0 on ∂Ω_K before T*"

materialDerivativeOfRatioText : String
materialDerivativeOfRatioText =
  "material derivative of the omega/e2/g12 ratio"

boundaryTransportTermsText : String
boundaryTransportTermsText =
  "boundary transport terms appear in d_t Q"

targetDifferentialInequalityText : String
targetDifferentialInequalityText =
  "d_t Q <= C Q"

gronwallBoundText : String
gronwallBoundText =
  "Q(t) <= Q(0) e^{Ct}"

finiteRatioConsequenceText : String
finiteRatioConsequenceText =
  "finite Q(0) and d_t Q <= C Q imply finite Q(t) by Gronwall"

commutatorBlockerText : String
commutatorBlockerText =
  "blocker: the commutator estimate needed for the material derivative is not proved"

transportBlockerText : String
transportBlockerText =
  "blocker: the boundary transport estimate is not proved"

routeSummaryText : String
routeSummaryText =
  "collapseImpossible boundary-energy route: smooth finite-energy data and positive boundary gap g12 support the Q(t) surface, but the commutator and transport estimates remain open, so the receipt records the target d_t Q <= C Q and the Gronwall consequence without promotion."

receiptBoundaryText : List String
receiptBoundaryText =
  "Q(t) is the boundary-energy route quantity"
  ∷ "smooth finite-energy data and positive g12 on the boundary are recorded"
  ∷ "material derivative and boundary transport terms are tracked, not proved"
  ∷ "target differential inequality: d_t Q <= C Q"
  ∷ "Gronwall consequence: Q(t) <= Q(0) e^{Ct}"
  ∷ "finite-ratio consequence is recorded as the intended downstream gain"
  ∷ "commutator and transport estimates remain explicit blockers"
  ∷ "collapseImpossiblePromoted remains false"
  ∷ "Clay remains false"
  ∷ []

record NSCollapseBoundaryEnergyQGronwallReceipt : Set where
  constructor mkNSCollapseBoundaryEnergyQGronwallReceipt
  field
    stage :
      List NSCollapseBoundaryEnergyQGronwallStage
    stageIsCanonical :
      stage ≡ canonicalNSCollapseBoundaryEnergyQGronwallStages

    blockers :
      List NSCollapseBoundaryEnergyQGronwallBlocker
    blockersIsCanonical :
      blockers ≡ canonicalNSCollapseBoundaryEnergyQGronwallBlockers

    qBoundaryFunctional :
      String
    qBoundaryFunctionalIsCanonical :
      qBoundaryFunctional ≡ qBoundaryFunctionalText

    smoothFiniteEnergyData :
      Bool
    smoothFiniteEnergyDataIsTrue :
      smoothFiniteEnergyData ≡ true

    positiveBoundaryGapBeforeTStar :
      Bool
    positiveBoundaryGapBeforeTStarIsTrue :
      positiveBoundaryGapBeforeTStar ≡ true

    materialDerivativeOfRatio :
      String
    materialDerivativeOfRatioIsCanonical :
      materialDerivativeOfRatio ≡ materialDerivativeOfRatioText

    boundaryTransportTerms :
      String
    boundaryTransportTermsIsCanonical :
      boundaryTransportTerms ≡ boundaryTransportTermsText

    targetDifferentialInequality :
      String
    targetDifferentialInequalityIsCanonical :
      targetDifferentialInequality ≡ targetDifferentialInequalityText

    gronwallBound :
      String
    gronwallBoundIsCanonical :
      gronwallBound ≡ gronwallBoundText

    finiteRatioConsequence :
      String
    finiteRatioConsequenceIsCanonical :
      finiteRatioConsequence ≡ finiteRatioConsequenceText

    commutatorBlocker :
      NSCollapseBoundaryEnergyQGronwallBlocker
    commutatorBlockerIsCanonical :
      commutatorBlocker ≡ commutatorEstimateUnproved

    transportBlocker :
      NSCollapseBoundaryEnergyQGronwallBlocker
    transportBlockerIsCanonical :
      transportBlocker ≡ transportEstimateUnproved

    collapseImpossiblePromoted :
      Bool
    collapseImpossiblePromotedIsFalse :
      collapseImpossiblePromoted ≡ false

    clay :
      Bool
    clayIsFalse :
      clay ≡ false

    routeSummary :
      String
    routeSummaryIsCanonical :
      routeSummary ≡ routeSummaryText

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryText

canonicalNSCollapseBoundaryEnergyQGronwallReceipt :
  NSCollapseBoundaryEnergyQGronwallReceipt
canonicalNSCollapseBoundaryEnergyQGronwallReceipt =
  mkNSCollapseBoundaryEnergyQGronwallReceipt
    canonicalNSCollapseBoundaryEnergyQGronwallStages
    refl
    canonicalNSCollapseBoundaryEnergyQGronwallBlockers
    refl
    qBoundaryFunctionalText
    refl
    true
    refl
    true
    refl
    materialDerivativeOfRatioText
    refl
    boundaryTransportTermsText
    refl
    targetDifferentialInequalityText
    refl
    gronwallBoundText
    refl
    finiteRatioConsequenceText
    refl
    commutatorEstimateUnproved
    refl
    transportEstimateUnproved
    refl
    false
    refl
    false
    refl
    routeSummaryText
    refl
    receiptBoundaryText
    refl

open NSCollapseBoundaryEnergyQGronwallReceipt public

canonicalNSCollapseBoundaryEnergyQGronwallStageListIsCanonical :
  stage canonicalNSCollapseBoundaryEnergyQGronwallReceipt
  ≡ canonicalNSCollapseBoundaryEnergyQGronwallStages
canonicalNSCollapseBoundaryEnergyQGronwallStageListIsCanonical =
  refl

canonicalNSCollapseBoundaryEnergyQGronwallBlockersAreCanonical :
  blockers canonicalNSCollapseBoundaryEnergyQGronwallReceipt
  ≡ canonicalNSCollapseBoundaryEnergyQGronwallBlockers
canonicalNSCollapseBoundaryEnergyQGronwallBlockersAreCanonical =
  refl

canonicalNSCollapseBoundaryEnergyQGronwallQBoundaryFunctionalIsCanonical :
  qBoundaryFunctional canonicalNSCollapseBoundaryEnergyQGronwallReceipt
  ≡ qBoundaryFunctionalText
canonicalNSCollapseBoundaryEnergyQGronwallQBoundaryFunctionalIsCanonical =
  refl

canonicalNSCollapseBoundaryEnergyQGronwallSmoothFiniteEnergyDataIsTrue :
  smoothFiniteEnergyData canonicalNSCollapseBoundaryEnergyQGronwallReceipt
  ≡ true
canonicalNSCollapseBoundaryEnergyQGronwallSmoothFiniteEnergyDataIsTrue =
  refl

canonicalNSCollapseBoundaryEnergyQGronwallPositiveBoundaryGapIsTrue :
  positiveBoundaryGapBeforeTStar canonicalNSCollapseBoundaryEnergyQGronwallReceipt
  ≡ true
canonicalNSCollapseBoundaryEnergyQGronwallPositiveBoundaryGapIsTrue =
  refl

canonicalNSCollapseBoundaryEnergyQGronwallTargetDifferentialInequalityIsCanonical :
  targetDifferentialInequality canonicalNSCollapseBoundaryEnergyQGronwallReceipt
  ≡ targetDifferentialInequalityText
canonicalNSCollapseBoundaryEnergyQGronwallTargetDifferentialInequalityIsCanonical =
  refl

canonicalNSCollapseBoundaryEnergyQGronwallGronwallBoundIsCanonical :
  gronwallBound canonicalNSCollapseBoundaryEnergyQGronwallReceipt
  ≡ gronwallBoundText
canonicalNSCollapseBoundaryEnergyQGronwallGronwallBoundIsCanonical =
  refl

canonicalNSCollapseBoundaryEnergyQGronwallFiniteRatioConsequenceIsCanonical :
  finiteRatioConsequence canonicalNSCollapseBoundaryEnergyQGronwallReceipt
  ≡ finiteRatioConsequenceText
canonicalNSCollapseBoundaryEnergyQGronwallFiniteRatioConsequenceIsCanonical =
  refl

canonicalNSCollapseBoundaryEnergyQGronwallCommutatorBlockerIsCanonical :
  commutatorBlocker canonicalNSCollapseBoundaryEnergyQGronwallReceipt
  ≡ commutatorEstimateUnproved
canonicalNSCollapseBoundaryEnergyQGronwallCommutatorBlockerIsCanonical =
  refl

canonicalNSCollapseBoundaryEnergyQGronwallTransportBlockerIsCanonical :
  transportBlocker canonicalNSCollapseBoundaryEnergyQGronwallReceipt
  ≡ transportEstimateUnproved
canonicalNSCollapseBoundaryEnergyQGronwallTransportBlockerIsCanonical =
  refl

canonicalNSCollapseBoundaryEnergyQGronwallCollapseImpossiblePromotedIsFalse :
  collapseImpossiblePromoted canonicalNSCollapseBoundaryEnergyQGronwallReceipt
  ≡ false
canonicalNSCollapseBoundaryEnergyQGronwallCollapseImpossiblePromotedIsFalse =
  refl

canonicalNSCollapseBoundaryEnergyQGronwallClayIsFalse :
  clay canonicalNSCollapseBoundaryEnergyQGronwallReceipt ≡ false
canonicalNSCollapseBoundaryEnergyQGronwallClayIsFalse =
  refl

canonicalNSCollapseBoundaryEnergyQGronwallRouteSummaryIsCanonical :
  routeSummary canonicalNSCollapseBoundaryEnergyQGronwallReceipt
  ≡ routeSummaryText
canonicalNSCollapseBoundaryEnergyQGronwallRouteSummaryIsCanonical =
  refl

canonicalNSCollapseBoundaryEnergyQGronwallReceiptBoundaryIsCanonical :
  receiptBoundary canonicalNSCollapseBoundaryEnergyQGronwallReceipt
  ≡ receiptBoundaryText
canonicalNSCollapseBoundaryEnergyQGronwallReceiptBoundaryIsCanonical =
  refl
