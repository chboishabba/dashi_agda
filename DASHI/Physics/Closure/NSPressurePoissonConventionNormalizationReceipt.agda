module DASHI.Physics.Closure.NSPressurePoissonConventionNormalizationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Fail-closed receipt for the pressure-Poisson convention-normalization lane.
--
-- The prior bypass surface treated the pressure archive in canonical
-- -Delta p form.  The audit now records that the raw pressure archive
-- aligns more naturally with +Delta p, but only up to a scale mismatch.
-- Therefore any analytic use must pass through a convention-normalization
-- lemma first.  This module records that handoff only; it does not prove
-- the analytic theorem, does not discharge the scale mismatch, and keeps
-- all Clay promotion fields explicitly false.

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSPressurePoissonConventionNormalizationStatus : Set where
  pressurePoissonConventionNormalizationReceiptRecorded :
    NSPressurePoissonConventionNormalizationStatus

data NSPressurePoissonConventionNormalizationStage : Set where
  priorCanonicalMinusDeltaPBypassRecorded :
    NSPressurePoissonConventionNormalizationStage
  rawPressureArchivePlusDeltaPAlignmentAudited :
    NSPressurePoissonConventionNormalizationStage
  scaleMismatchRecorded :
    NSPressurePoissonConventionNormalizationStage
  conventionNormalizationLemmaRequired :
    NSPressurePoissonConventionNormalizationStage
  analyticUseBlockedBeforeNormalization :
    NSPressurePoissonConventionNormalizationStage
  bypassRouteFailClosed :
    NSPressurePoissonConventionNormalizationStage
  clayPromotionFalse :
    NSPressurePoissonConventionNormalizationStage

canonicalNSPressurePoissonConventionNormalizationStages :
  List NSPressurePoissonConventionNormalizationStage
canonicalNSPressurePoissonConventionNormalizationStages =
  priorCanonicalMinusDeltaPBypassRecorded
  ∷ rawPressureArchivePlusDeltaPAlignmentAudited
  ∷ scaleMismatchRecorded
  ∷ conventionNormalizationLemmaRequired
  ∷ analyticUseBlockedBeforeNormalization
  ∷ bypassRouteFailClosed
  ∷ clayPromotionFalse
  ∷ []

data NSPressurePoissonConventionNormalizationBlocker : Set where
  canonicalMinusDeltaPBypassIsRetired :
    NSPressurePoissonConventionNormalizationBlocker
  rawArchivePlusDeltaPNeedsScaleNormalization :
    NSPressurePoissonConventionNormalizationBlocker
  scaleMismatchStillOpen :
    NSPressurePoissonConventionNormalizationBlocker
  normalizationLemmaNotYetDischarged :
    NSPressurePoissonConventionNormalizationBlocker
  analyticUseStillBlocked :
    NSPressurePoissonConventionNormalizationBlocker
  noClayPromotion :
    NSPressurePoissonConventionNormalizationBlocker

canonicalNSPressurePoissonConventionNormalizationBlockers :
  List NSPressurePoissonConventionNormalizationBlocker
canonicalNSPressurePoissonConventionNormalizationBlockers =
  canonicalMinusDeltaPBypassIsRetired
  ∷ rawArchivePlusDeltaPNeedsScaleNormalization
  ∷ scaleMismatchStillOpen
  ∷ normalizationLemmaNotYetDischarged
  ∷ analyticUseStillBlocked
  ∷ noClayPromotion
  ∷ []

data NSPressurePoissonConventionNormalizationPromotion : Set where

nsPressurePoissonConventionNormalizationPromotionImpossibleHere :
  NSPressurePoissonConventionNormalizationPromotion →
  ⊥
nsPressurePoissonConventionNormalizationPromotionImpossibleHere ()

oTextValue : String
oTextValue =
  "O: prior pressure bypass was recorded in canonical -Delta p form."

rTextValue : String
rTextValue =
  "R: the raw pressure archive aligns better with +Delta p, but only after a convention-normalization lemma because the archive carries a scale mismatch."

cTextValue : String
cTextValue =
  "C: the bypass must route through convention normalization before any analytic use of the pressure-Poisson data."

sTextValue : String
sTextValue =
  "S: the convention-normalization step is recorded; the analytic comparison surface remains fail-closed."

lTextValue : String
lTextValue =
  "L: canonical -Delta p bypass -> raw +Delta p archive audit -> scale mismatch -> normalization lemma -> analytic use."

pTextValue : String
pTextValue =
  "P: do not use the pressure archive analytically until the normalization lemma is separately discharged."

gTextValue : String
gTextValue =
  "G: Clay Navier-Stokes promotion remains false."

fTextValue : String
fTextValue =
  "F: promotion flags remain empty and the analytic gap stays open."

receiptBoundaryText : List String
receiptBoundaryText =
  "O: prior pressure bypass was recorded in canonical -Delta p form"
  ∷ "R: raw pressure archive aligns better with +Delta p, but with a scale mismatch"
  ∷ "C: pressure-Poisson bypass must pass through a convention-normalization lemma before analytic use"
  ∷ "S: normalization handoff recorded; analytic use is still closed"
  ∷ "L: bypass archive -> audit -> scale mismatch -> normalization lemma -> analytic use"
  ∷ "P: no analytic use until normalization is discharged"
  ∷ "G: Clay promotion remains false"
  ∷ "F: promotion flags remain empty"
  ∷ []

canonicalBoundaryText : String
canonicalBoundaryText =
  "Pressure-Poisson convention-normalization receipt: the earlier bypass used canonical -Delta p, the raw archive now aligns better with +Delta p but with a scale mismatch, and any analytic use must pass through the convention-normalization lemma before the route can be considered further."

record NSPressurePoissonConventionNormalizationORCSLPGF : Set where
  constructor nsPressurePoissonConventionNormalizationORCSLPGF
  field
    O : String
    OIsCanonical :
      O ≡ "O: prior pressure bypass was recorded in canonical -Delta p form."
    R : String
    RIsCanonical :
      R ≡ "R: the raw pressure archive aligns better with +Delta p, but only after a convention-normalization lemma because the archive carries a scale mismatch."
    C : String
    CIsCanonical :
      C ≡ "C: the bypass must route through convention normalization before any analytic use of the pressure-Poisson data."
    S : String
    SIsCanonical :
      S ≡ "S: the convention-normalization step is recorded; the analytic comparison surface remains fail-closed."
    L : String
    LIsCanonical :
      L ≡ "L: canonical -Delta p bypass -> raw +Delta p archive audit -> scale mismatch -> normalization lemma -> analytic use."
    P : String
    PIsCanonical :
      P ≡ "P: do not use the pressure archive analytically until the normalization lemma is separately discharged."
    G : String
    GIsCanonical :
      G ≡ "G: Clay Navier-Stokes promotion remains false."
    F : String
    FIsCanonical :
      F ≡ "F: promotion flags remain empty and the analytic gap stays open."

open NSPressurePoissonConventionNormalizationORCSLPGF public

canonicalNSPressurePoissonConventionNormalizationORCSLPGF :
  NSPressurePoissonConventionNormalizationORCSLPGF
canonicalNSPressurePoissonConventionNormalizationORCSLPGF =
  nsPressurePoissonConventionNormalizationORCSLPGF
    "O: prior pressure bypass was recorded in canonical -Delta p form."
    refl
    "R: the raw pressure archive aligns better with +Delta p, but only after a convention-normalization lemma because the archive carries a scale mismatch."
    refl
    "C: the bypass must route through convention normalization before any analytic use of the pressure-Poisson data."
    refl
    "S: the convention-normalization step is recorded; the analytic comparison surface remains fail-closed."
    refl
    "L: canonical -Delta p bypass -> raw +Delta p archive audit -> scale mismatch -> normalization lemma -> analytic use."
    refl
    "P: do not use the pressure archive analytically until the normalization lemma is separately discharged."
    refl
    "G: Clay Navier-Stokes promotion remains false."
    refl
    "F: promotion flags remain empty and the analytic gap stays open."
    refl

record NSPressurePoissonConventionNormalizationReceipt : Setω where
  constructor mkNSPressurePoissonConventionNormalizationReceipt
  field
    status :
      NSPressurePoissonConventionNormalizationStatus
    statusIsCanonical :
      status ≡ pressurePoissonConventionNormalizationReceiptRecorded

    stageTrail :
      List NSPressurePoissonConventionNormalizationStage
    stageTrailIsCanonical :
      stageTrail ≡ canonicalNSPressurePoissonConventionNormalizationStages
    stageCount :
      Nat
    stageCountIsCanonical :
      stageCount ≡ listLength canonicalNSPressurePoissonConventionNormalizationStages

    blockerTrail :
      List NSPressurePoissonConventionNormalizationBlocker
    blockerTrailIsCanonical :
      blockerTrail ≡ canonicalNSPressurePoissonConventionNormalizationBlockers
    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSPressurePoissonConventionNormalizationBlockers

    orcslpgf :
      NSPressurePoissonConventionNormalizationORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSPressurePoissonConventionNormalizationORCSLPGF

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryText
    receiptBoundaryParagraph :
      String
    receiptBoundaryParagraphIsCanonical :
      receiptBoundaryParagraph ≡ canonicalBoundaryText

    priorBypassCanonicalMinusDeltaP :
      Bool
    priorBypassCanonicalMinusDeltaPIsTrue :
      priorBypassCanonicalMinusDeltaP ≡ true

    rawArchiveAlignsBetterWithPlusDeltaP :
      Bool
    rawArchiveAlignsBetterWithPlusDeltaPIsTrue :
      rawArchiveAlignsBetterWithPlusDeltaP ≡ true

    scaleMismatchRecordedHere :
      Bool
    scaleMismatchRecordedHereIsTrue :
      scaleMismatchRecordedHere ≡ true

    conventionNormalizationLemmaRecorded :
      Bool
    conventionNormalizationLemmaRecordedIsTrue :
      conventionNormalizationLemmaRecorded ≡ true

    analyticUseRemainsBlocked :
      Bool
    analyticUseRemainsBlockedIsTrue :
      analyticUseRemainsBlocked ≡ true

    clayNavierStokesPromoted :
      Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    fullClayNSSolved :
      Bool
    fullClayNSSolvedIsFalse :
      fullClayNSSolved ≡ false

    terminalPromotion :
      Bool
    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    promotionFlags :
      List NSPressurePoissonConventionNormalizationPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open NSPressurePoissonConventionNormalizationReceipt public

canonicalNSPressurePoissonConventionNormalizationReceipt :
  NSPressurePoissonConventionNormalizationReceipt
canonicalNSPressurePoissonConventionNormalizationReceipt =
  mkNSPressurePoissonConventionNormalizationReceipt
    pressurePoissonConventionNormalizationReceiptRecorded
    refl
    canonicalNSPressurePoissonConventionNormalizationStages
    refl
    (listLength canonicalNSPressurePoissonConventionNormalizationStages)
    refl
    canonicalNSPressurePoissonConventionNormalizationBlockers
    refl
    (listLength canonicalNSPressurePoissonConventionNormalizationBlockers)
    refl
    canonicalNSPressurePoissonConventionNormalizationORCSLPGF
    refl
    receiptBoundaryText
    refl
    canonicalBoundaryText
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
    []
    refl

canonicalStatusIsCanonical :
  status canonicalNSPressurePoissonConventionNormalizationReceipt ≡
  pressurePoissonConventionNormalizationReceiptRecorded
canonicalStatusIsCanonical = refl

canonicalStageTrailIsCanonical :
  stageTrail canonicalNSPressurePoissonConventionNormalizationReceipt ≡
  canonicalNSPressurePoissonConventionNormalizationStages
canonicalStageTrailIsCanonical = refl

canonicalStageCountIsCanonical :
  stageCount canonicalNSPressurePoissonConventionNormalizationReceipt ≡
  listLength canonicalNSPressurePoissonConventionNormalizationStages
canonicalStageCountIsCanonical = refl

canonicalBlockerTrailIsCanonical :
  blockerTrail canonicalNSPressurePoissonConventionNormalizationReceipt ≡
  canonicalNSPressurePoissonConventionNormalizationBlockers
canonicalBlockerTrailIsCanonical = refl

canonicalBlockerCountIsCanonical :
  blockerCount canonicalNSPressurePoissonConventionNormalizationReceipt ≡
  listLength canonicalNSPressurePoissonConventionNormalizationBlockers
canonicalBlockerCountIsCanonical = refl

canonicalORCSLPGFIsCanonical :
  orcslpgf canonicalNSPressurePoissonConventionNormalizationReceipt ≡
  canonicalNSPressurePoissonConventionNormalizationORCSLPGF
canonicalORCSLPGFIsCanonical = refl

canonicalBoundaryTextIsCanonical :
  receiptBoundaryParagraph canonicalNSPressurePoissonConventionNormalizationReceipt ≡
  canonicalBoundaryText
canonicalBoundaryTextIsCanonical = refl

canonicalPriorBypassCanonicalMinusDeltaPIsTrue :
  priorBypassCanonicalMinusDeltaP
    canonicalNSPressurePoissonConventionNormalizationReceipt ≡ true
canonicalPriorBypassCanonicalMinusDeltaPIsTrue = refl

canonicalRawArchiveAlignsBetterWithPlusDeltaPIsTrue :
  rawArchiveAlignsBetterWithPlusDeltaP
    canonicalNSPressurePoissonConventionNormalizationReceipt ≡ true
canonicalRawArchiveAlignsBetterWithPlusDeltaPIsTrue = refl

canonicalScaleMismatchRecordedHereIsTrue :
  scaleMismatchRecordedHere
    canonicalNSPressurePoissonConventionNormalizationReceipt ≡ true
canonicalScaleMismatchRecordedHereIsTrue = refl

canonicalConventionNormalizationLemmaRecordedIsTrue :
  conventionNormalizationLemmaRecorded
    canonicalNSPressurePoissonConventionNormalizationReceipt ≡ true
canonicalConventionNormalizationLemmaRecordedIsTrue = refl

canonicalAnalyticUseStillBlockedIsTrue :
  analyticUseRemainsBlocked
    canonicalNSPressurePoissonConventionNormalizationReceipt ≡ true
canonicalAnalyticUseStillBlockedIsTrue = refl

canonicalClayNavierStokesPromotedIsFalse :
  clayNavierStokesPromoted
    canonicalNSPressurePoissonConventionNormalizationReceipt ≡ false
canonicalClayNavierStokesPromotedIsFalse = refl

canonicalFullClayNSSolvedIsFalse :
  fullClayNSSolved
    canonicalNSPressurePoissonConventionNormalizationReceipt ≡ false
canonicalFullClayNSSolvedIsFalse = refl

canonicalTerminalPromotionIsFalse :
  terminalPromotion
    canonicalNSPressurePoissonConventionNormalizationReceipt ≡ false
canonicalTerminalPromotionIsFalse = refl

canonicalPromotionFlagsAreEmpty :
  promotionFlags canonicalNSPressurePoissonConventionNormalizationReceipt ≡ []
canonicalPromotionFlagsAreEmpty = refl
