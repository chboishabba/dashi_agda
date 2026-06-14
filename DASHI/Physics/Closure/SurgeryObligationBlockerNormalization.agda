module DASHI.Physics.Closure.SurgeryObligationBlockerNormalization where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.SurgeryCanonicalNeighborhoodObstruction as Surgery
import DASHI.Physics.Closure.SurgeryCanonicalNeighborhoodObligationLadder as Ladder
import DASHI.Physics.Closure.BTNeckSurgeryObligationComposite as BTNeck

------------------------------------------------------------------------
-- Surgery obligation blocker normalization.
--
-- This module is a bookkeeping surface only.  It normalizes the three
-- obligations used by the finite BT neck rows and records that each remains
-- undischarged here.  It does not promote finite BT evidence into a smooth
-- epsilon-neck, surgery-continuation theorem, or Ricci-flow surgery result.

length : {A : Set} → List A → Nat
length [] =
  zero
length (_ ∷ xs) =
  suc (length xs)

data SurgeryBlockerStatus : Set where
  finiteAnalogueOnlySmoothTargetBlocked :
    SurgeryBlockerStatus

record SurgeryObligationBlockerRow : Set where
  field
    label :
      String

    sourceObligation :
      Surgery.SurgeryObligation

    dischargedHere :
      Bool

    dischargedHereIsFalse :
      dischargedHere ≡ false

    blockerStatus :
      SurgeryBlockerStatus

    ladderStatus :
      Ladder.LadderPromotionStatus

    ladderStatusIsFiniteAnalogueBlocked :
      ladderStatus ≡ Ladder.finiteAnalogueConstructedSmoothTargetBlocked

    rowStatement :
      String

open SurgeryObligationBlockerRow public

rowForObligation :
  String →
  Surgery.SurgeryObligation →
  SurgeryObligationBlockerRow
rowForObligation rowLabel obligation =
  record
    { label =
        rowLabel
    ; sourceObligation =
        obligation
    ; dischargedHere =
        false
    ; dischargedHereIsFalse =
        refl
    ; blockerStatus =
        finiteAnalogueOnlySmoothTargetBlocked
    ; ladderStatus =
        Ladder.finiteAnalogueConstructedSmoothTargetBlocked
    ; ladderStatusIsFiniteAnalogueBlocked =
        refl
    ; rowStatement =
        "Finite BT neck evidence is recorded, but this obligation is not discharged as smooth surgery evidence."
    }

smoothEpsilonNeckModelBlockerRow :
  SurgeryObligationBlockerRow
smoothEpsilonNeckModelBlockerRow =
  rowForObligation
    "requireSmoothEpsilonNeckModel"
    Surgery.requireSmoothEpsilonNeckModel

surgeryContinuationLawBlockerRow :
  SurgeryObligationBlockerRow
surgeryContinuationLawBlockerRow =
  rowForObligation
    "requireSurgeryContinuationLaw"
    Surgery.requireSurgeryContinuationLaw

retainDiscreteShellOnlyStatusBlockerRow :
  SurgeryObligationBlockerRow
retainDiscreteShellOnlyStatusBlockerRow =
  rowForObligation
    "retainDiscreteShellOnlyStatus"
    Surgery.retainDiscreteShellOnlyStatus

canonicalSurgeryObligationBlockerRows :
  List SurgeryObligationBlockerRow
canonicalSurgeryObligationBlockerRows =
  smoothEpsilonNeckModelBlockerRow
  ∷ surgeryContinuationLawBlockerRow
  ∷ retainDiscreteShellOnlyStatusBlockerRow
  ∷ []

canonicalSurgeryObligationBlockerRowCount :
  Nat
canonicalSurgeryObligationBlockerRowCount =
  length canonicalSurgeryObligationBlockerRows

canonicalSurgeryObligationBlockerRowCountIs3 :
  canonicalSurgeryObligationBlockerRowCount ≡ 3
canonicalSurgeryObligationBlockerRowCountIs3 =
  refl

canonicalSurgeryObligations :
  List Surgery.SurgeryObligation
canonicalSurgeryObligations =
  Surgery.requireSmoothEpsilonNeckModel
  ∷ Surgery.requireSurgeryContinuationLaw
  ∷ Surgery.retainDiscreteShellOnlyStatus
  ∷ []

canonicalSurgeryObligationsMatchBTNeckComposite :
  canonicalSurgeryObligations ≡ BTNeck.canonicalBTNeckSurgeryObligations
canonicalSurgeryObligationsMatchBTNeckComposite =
  refl

canonicalSurgeryBlockerStatus :
  Ladder.LadderPromotionStatus
canonicalSurgeryBlockerStatus =
  Ladder.finiteAnalogueConstructedSmoothTargetBlocked

canonicalSurgeryBlockerStatusMatchesBTNeckComposite :
  canonicalSurgeryBlockerStatus ≡ BTNeck.canonicalBTNeckSurgeryStatus
canonicalSurgeryBlockerStatusMatchesBTNeckComposite =
  refl

record BTNeckSurgeryObligationBlockerLink : Set where
  field
    sourceRow :
      BTNeck.BTNeckSurgeryObligationCompositeRow

    normalizedRows :
      List SurgeryObligationBlockerRow

    normalizedRowsAreCanonical :
      normalizedRows ≡ canonicalSurgeryObligationBlockerRows

    sourceObligations :
      List Surgery.SurgeryObligation

    sourceObligationsAreCanonical :
      sourceObligations ≡ canonicalSurgeryObligations

    sourceObligationsMatchComposite :
      sourceObligations ≡ BTNeck.associatedSmoothObligations sourceRow

    sourceStatus :
      Ladder.LadderPromotionStatus

    sourceStatusIsBlocked :
      sourceStatus ≡ Ladder.finiteAnalogueConstructedSmoothTargetBlocked

    sourceStatusMatchesComposite :
      sourceStatus ≡ BTNeck.associatedSmoothObligationStatus sourceRow

    linkStatement :
      String

open BTNeckSurgeryObligationBlockerLink public

linkForBTNeckRow :
  BTNeck.BTNeckSurgeryObligationCompositeRow →
  BTNeckSurgeryObligationBlockerLink
linkForBTNeckRow source =
  record
    { sourceRow =
        source
    ; normalizedRows =
        canonicalSurgeryObligationBlockerRows
    ; normalizedRowsAreCanonical =
        refl
    ; sourceObligations =
        BTNeck.associatedSmoothObligations source
    ; sourceObligationsAreCanonical =
        BTNeck.associatedSmoothObligationsAreCanonical source
    ; sourceObligationsMatchComposite =
        refl
    ; sourceStatus =
        BTNeck.associatedSmoothObligationStatus source
    ; sourceStatusIsBlocked =
        BTNeck.associatedSmoothObligationStatusIsCanonical source
    ; sourceStatusMatchesComposite =
        refl
    ; linkStatement =
        "The p-adic BT neck row links to the same three normalized surgery obligations and the same finite-analogue blocked status."
    }

p2BTNeckSurgeryObligationBlockerLink :
  BTNeckSurgeryObligationBlockerLink
p2BTNeckSurgeryObligationBlockerLink =
  linkForBTNeckRow BTNeck.p2BTNeckSurgeryObligationCompositeRow

p3BTNeckSurgeryObligationBlockerLink :
  BTNeckSurgeryObligationBlockerLink
p3BTNeckSurgeryObligationBlockerLink =
  linkForBTNeckRow BTNeck.p3BTNeckSurgeryObligationCompositeRow

p7BTNeckSurgeryObligationBlockerLink :
  BTNeckSurgeryObligationBlockerLink
p7BTNeckSurgeryObligationBlockerLink =
  linkForBTNeckRow BTNeck.p7BTNeckSurgeryObligationCompositeRow

p2LinkObligationsAreCanonical :
  sourceObligations p2BTNeckSurgeryObligationBlockerLink
  ≡
  canonicalSurgeryObligations
p2LinkObligationsAreCanonical =
  refl

p3LinkObligationsAreCanonical :
  sourceObligations p3BTNeckSurgeryObligationBlockerLink
  ≡
  canonicalSurgeryObligations
p3LinkObligationsAreCanonical =
  refl

p7LinkObligationsAreCanonical :
  sourceObligations p7BTNeckSurgeryObligationBlockerLink
  ≡
  canonicalSurgeryObligations
p7LinkObligationsAreCanonical =
  refl

p2LinkStatusIsFiniteAnalogueBlocked :
  sourceStatus p2BTNeckSurgeryObligationBlockerLink
  ≡
  Ladder.finiteAnalogueConstructedSmoothTargetBlocked
p2LinkStatusIsFiniteAnalogueBlocked =
  refl

p3LinkStatusIsFiniteAnalogueBlocked :
  sourceStatus p3BTNeckSurgeryObligationBlockerLink
  ≡
  Ladder.finiteAnalogueConstructedSmoothTargetBlocked
p3LinkStatusIsFiniteAnalogueBlocked =
  refl

p7LinkStatusIsFiniteAnalogueBlocked :
  sourceStatus p7BTNeckSurgeryObligationBlockerLink
  ≡
  Ladder.finiteAnalogueConstructedSmoothTargetBlocked
p7LinkStatusIsFiniteAnalogueBlocked =
  refl

smoothEpsilonNeckModelBlockerUndischarged :
  dischargedHere smoothEpsilonNeckModelBlockerRow ≡ false
smoothEpsilonNeckModelBlockerUndischarged =
  refl

surgeryContinuationLawBlockerUndischarged :
  dischargedHere surgeryContinuationLawBlockerRow ≡ false
surgeryContinuationLawBlockerUndischarged =
  refl

retainDiscreteShellOnlyStatusUndischarged :
  dischargedHere retainDiscreteShellOnlyStatusBlockerRow ≡ false
retainDiscreteShellOnlyStatusUndischarged =
  refl
