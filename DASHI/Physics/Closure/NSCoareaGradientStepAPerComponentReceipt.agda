module DASHI.Physics.Closure.NSCoareaGradientStepAPerComponentReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate-only geometry receipt for the corrected coarea gradient bound
-- and the StepA_PerComponent closure route.
--
-- This surface records the corrected exponent as r^1, not r^(7/2), and it
-- records the StepA_PerComponent route as closing from local L3 blow-up plus
-- diameter/layer-thickness hypotheses.  It is geometry/standard-lemma
-- bookkeeping only; no Clay promotion or theorem promotion is claimed.

data NSCoareaGradientStepAPerComponentStatus : Set where
  candidateOnlyFailClosed :
    NSCoareaGradientStepAPerComponentStatus

data NSCoareaGradientStepAPerComponentRow : Set where
  correctedCoareaExponentRecorded :
    NSCoareaGradientStepAPerComponentRow
  stepAPerComponentClosureRecorded :
    NSCoareaGradientStepAPerComponentRow
  geometryStandardLemmaOnly :
    NSCoareaGradientStepAPerComponentRow
  noClayPromotion :
    NSCoareaGradientStepAPerComponentRow

canonicalNSCoareaGradientStepAPerComponentRows :
  List NSCoareaGradientStepAPerComponentRow
canonicalNSCoareaGradientStepAPerComponentRows =
  correctedCoareaExponentRecorded
  ∷ stepAPerComponentClosureRecorded
  ∷ geometryStandardLemmaOnly
  ∷ noClayPromotion
  ∷ []

linkedReceiptLabels : List String
linkedReceiptLabels =
  "CorrectedCoareaGradientBoundReceipt"
  ∷ "NSKatoHessianConfinementReceipt"
  ∷ []

exactObjectLabels : List String
exactObjectLabels =
  "f=lambda2+"
  ∷ "B(x₀,r)"
  ∷ "K"
  ∷ "C_geo"
  ∷ "r"
  ∷ "C_iso"
  ∷ "component Cₙ"
  ∷ "d₀"
  ∷ "τ₀"
  ∷ "local L3 nbhd(Cₙ)"
  ∷ []

coareaExponentText : String
coareaExponentText =
  "coareaGradientBound exponent is r^1, not r^(7/2)"

stepAPerComponentText : String
stepAPerComponentText =
  "StepA_PerComponent closes from local L3 blow-up plus diameter/layer-thickness hypotheses"

conclusionText : String
conclusionText =
  "sup_{∂Cₙ}|∇λ₂|→∞"

geometryNoteText : String
geometryNoteText =
  "Geometry/standard lemma only; not Clay promotion."

boundaryText : String
boundaryText =
  "Candidate-only geometry receipt: the corrected coarea gradient bound is fixed at r^1, the StepA_PerComponent route is recorded as a local L3 blow-up plus diameter/layer-thickness closure, and all promotion flags stay false."

record NSCoareaGradientStepAPerComponentORCSLPGF : Set where
  constructor mkNSCoareaGradientStepAPerComponentORCSLPGF
  field
    O :
      String
    OIsCanonical :
      O ≡
      "Worker 3 owns the corrected coarea gradient bound receipt surface only."

    R :
      String
    RIsCanonical :
      R ≡
      "Record the corrected coarea exponent as r^1 and close StepA_PerComponent from local L3 blow-up plus diameter/layer-thickness hypotheses."

    C :
      String
    CIsCanonical :
      C ≡
      "Create only NSCoareaGradientStepAPerComponentReceipt.agda."

    S :
      String
    SIsCanonical :
      S ≡
      "Related surfaces are CorrectedCoareaGradientBoundReceipt and NSKatoHessianConfinementReceipt; no other files are touched."

    L :
      String
    LIsCanonical :
      L ≡
      "corrected coarea receipt -> main Agda check -> later aggregation"

    P :
      String
    PIsCanonical :
      P ≡
      "f=lambda2+, B(x₀,r), K, C_geo, r, C_iso, component Cₙ, d₀, τ₀, local L3 nbhd(Cₙ), conclusion sup_{∂Cₙ}|∇λ₂|→∞"

    G :
      String
    GIsCanonical :
      G ≡
      "Candidate-only; no theorem promotion; main runs Agda."

    F :
      String
    FIsCanonical :
      F ≡
      "Avoid depending on unavailable math libraries; this is a receipt surface, not a full formal coarea proof."

canonicalNSCoareaGradientStepAPerComponentORCSLPGF :
  NSCoareaGradientStepAPerComponentORCSLPGF
canonicalNSCoareaGradientStepAPerComponentORCSLPGF =
  mkNSCoareaGradientStepAPerComponentORCSLPGF
    "Worker 3 owns the corrected coarea gradient bound receipt surface only."
    refl
    "Record the corrected coarea exponent as r^1 and close StepA_PerComponent from local L3 blow-up plus diameter/layer-thickness hypotheses."
    refl
    "Create only NSCoareaGradientStepAPerComponentReceipt.agda."
    refl
    "Related surfaces are CorrectedCoareaGradientBoundReceipt and NSKatoHessianConfinementReceipt; no other files are touched."
    refl
    "corrected coarea receipt -> main Agda check -> later aggregation"
    refl
    "f=lambda2+, B(x₀,r), K, C_geo, r, C_iso, component Cₙ, d₀, τ₀, local L3 nbhd(Cₙ), conclusion sup_{∂Cₙ}|∇λ₂|→∞"
    refl
    "Candidate-only; no theorem promotion; main runs Agda."
    refl
    "Avoid depending on unavailable math libraries; this is a receipt surface, not a full formal coarea proof."
    refl

record NSCoareaGradientStepAPerComponentReceipt : Set where
  constructor mkNSCoareaGradientStepAPerComponentReceipt
  field
    status :
      NSCoareaGradientStepAPerComponentStatus
    statusIsCanonical :
      status ≡ candidateOnlyFailClosed

    linkedReceipts :
      List String
    linkedReceiptsIsCanonical :
      linkedReceipts ≡ linkedReceiptLabels

    linkedReceiptCount :
      Nat
    linkedReceiptCountIsTwo :
      linkedReceiptCount ≡ 2

    exactObjectLabelsField :
      List String
    exactObjectLabelsFieldIsCanonical :
      exactObjectLabelsField ≡ exactObjectLabels

    canonicalRows :
      List NSCoareaGradientStepAPerComponentRow
    canonicalRowsIsCanonical :
      canonicalRows ≡ canonicalNSCoareaGradientStepAPerComponentRows

    coareaExponent :
      String
    coareaExponentIsCanonical :
      coareaExponent ≡ coareaExponentText

    stepAPerComponentClosure :
      String
    stepAPerComponentClosureIsCanonical :
      stepAPerComponentClosure ≡ stepAPerComponentText

    conclusion :
      String
    conclusionIsCanonical :
      conclusion ≡ conclusionText

    geometryNote :
      String
    geometryNoteIsCanonical :
      geometryNote ≡ geometryNoteText

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ boundaryText

    orcslpgf :
      NSCoareaGradientStepAPerComponentORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSCoareaGradientStepAPerComponentORCSLPGF

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalPromoted :
      Bool
    terminalPromotedIsFalse :
      terminalPromoted ≡ false

canonicalNSCoareaGradientStepAPerComponentReceipt :
  NSCoareaGradientStepAPerComponentReceipt
canonicalNSCoareaGradientStepAPerComponentReceipt =
  mkNSCoareaGradientStepAPerComponentReceipt
    candidateOnlyFailClosed
    refl
    linkedReceiptLabels
    refl
    2
    refl
    exactObjectLabels
    refl
    canonicalNSCoareaGradientStepAPerComponentRows
    refl
    coareaExponentText
    refl
    stepAPerComponentText
    refl
    conclusionText
    refl
    geometryNoteText
    refl
    boundaryText
    refl
    canonicalNSCoareaGradientStepAPerComponentORCSLPGF
    refl
    false
    refl
    false
    refl
    false
    refl

open NSCoareaGradientStepAPerComponentReceipt public
open NSCoareaGradientStepAPerComponentORCSLPGF public
