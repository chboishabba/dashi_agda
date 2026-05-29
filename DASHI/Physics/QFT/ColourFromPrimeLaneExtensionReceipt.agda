module DASHI.Physics.QFT.ColourFromPrimeLaneExtensionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt as Conditional
import DASHI.Physics.QFT.FinitePrimeLaneDHRSMCompatibilityLedger as Ledger

------------------------------------------------------------------------
-- Colour-origin diagnostic from the three finite prime lanes.
--
-- The receipt records the honest finite observation: the three selected
-- prime lanes admit S3 permutation symmetry, and S3 can be treated as a
-- discrete subgroup/candidate inside SU(3).  It deliberately does not promote
-- that finite permutation symmetry to the full continuous SU(3) colour group
-- and does not change the existing false exact G_DHR ~= G_SM boundary.

data ThreeLanePermutationSymmetry : Set where
  S3 :
    ThreeLanePermutationSymmetry

data SU3ExtensionNeed : Set where
  needContinuousLieGroupStructure :
    SU3ExtensionNeed

  needEightInfinitesimalColourGenerators :
    SU3ExtensionNeed

  needUnitaryDeterminantOneThreeDimensionalAction :
    SU3ExtensionNeed

  needRepresentationCategoryExtension :
    SU3ExtensionNeed

  needDRTannakaCompactGaugeGroupConstruction :
    SU3ExtensionNeed

canonicalSU3ExtensionNeeds :
  List SU3ExtensionNeed
canonicalSU3ExtensionNeeds =
  needContinuousLieGroupStructure
  ∷ needEightInfinitesimalColourGenerators
  ∷ needUnitaryDeterminantOneThreeDimensionalAction
  ∷ needRepresentationCategoryExtension
  ∷ needDRTannakaCompactGaugeGroupConstruction
  ∷ []

data ColourFromPrimeLaneExtensionStatus : Set where
  finiteS3CandidateOnlyFullSU3False :
    ColourFromPrimeLaneExtensionStatus

record ColourFromPrimeLaneExtensionReceipt : Setω where
  field
    status :
      ColourFromPrimeLaneExtensionStatus

    p2Lane :
      Ledger.FinitePrimeLaneSMRow

    p2LaneIsCanonical :
      p2Lane ≡ Ledger.p2U1YFinitePrimeLaneSMRow

    p3Lane :
      Ledger.FinitePrimeLaneSMRow

    p3LaneIsCanonical :
      p3Lane ≡ Ledger.p3SU2LFinitePrimeLaneSMRow

    p5Lane :
      Ledger.FinitePrimeLaneSMRow

    p5LaneIsCanonical :
      p5Lane ≡ Ledger.p5SU3cFinitePrimeLaneSMRow

    threePrimeLaneRows :
      List Ledger.FinitePrimeLaneSMRow

    threePrimeLaneRowsAreCanonical :
      threePrimeLaneRows ≡ Ledger.canonicalFinitePrimeLaneSMRows

    threeLanePermutationSymmetry :
      ThreeLanePermutationSymmetry

    threeLanePermutationSymmetryIsS3 :
      threeLanePermutationSymmetry ≡ S3

    s3InSu3 :
      Bool

    s3InSu3IsTrue :
      s3InSu3 ≡ true

    s3InSu3Diagnostic :
      String

    s3InSu3DiagnosticIsCanonical :
      s3InSu3Diagnostic
      ≡
      "S3 is recorded only as a discrete subgroup/candidate inside SU(3)"

    fullSU3FromPermutation :
      Bool

    fullSU3FromPermutationIsFalse :
      fullSU3FromPermutation ≡ false

    fullSU3FromPermutationReason :
      String

    fullSU3FromPermutationReasonIsCanonical :
      fullSU3FromPermutationReason
      ≡
      "S3 permutation symmetry is finite and discrete; S3 is not the full continuous SU(3) colour group"

    exactGDHREqualsGSMRemains :
      Bool

    exactGDHREqualsGSMRemainsIsFalse :
      exactGDHREqualsGSMRemains ≡ false

    existingConditionalReceipt :
      Conditional.ConditionalGDHRSMPromotionReceipt

    existingUnconditionalGDHREqualsGSMPromotedIsFalse :
      Conditional.ConditionalGDHRSMPromotionReceipt.unconditionalGDHREqualsGSMPromoted
        existingConditionalReceipt
      ≡
      false

    existingFullTheoremInRepoClaimedIsFalse :
      Conditional.ConditionalGDHRSMPromotionReceipt.fullTheoremInRepoClaimed
        existingConditionalReceipt
      ≡
      false

    su3ExtensionNeeds :
      List SU3ExtensionNeed

    su3ExtensionNeedsAreCanonical :
      su3ExtensionNeeds ≡ canonicalSU3ExtensionNeeds

    extensionBoundary :
      List String

open ColourFromPrimeLaneExtensionReceipt public

canonicalColourFromPrimeLaneExtensionReceipt :
  ColourFromPrimeLaneExtensionReceipt
canonicalColourFromPrimeLaneExtensionReceipt =
  record
    { status =
        finiteS3CandidateOnlyFullSU3False
    ; p2Lane =
        Ledger.p2U1YFinitePrimeLaneSMRow
    ; p2LaneIsCanonical =
        refl
    ; p3Lane =
        Ledger.p3SU2LFinitePrimeLaneSMRow
    ; p3LaneIsCanonical =
        refl
    ; p5Lane =
        Ledger.p5SU3cFinitePrimeLaneSMRow
    ; p5LaneIsCanonical =
        refl
    ; threePrimeLaneRows =
        Ledger.canonicalFinitePrimeLaneSMRows
    ; threePrimeLaneRowsAreCanonical =
        refl
    ; threeLanePermutationSymmetry =
        S3
    ; threeLanePermutationSymmetryIsS3 =
        refl
    ; s3InSu3 =
        true
    ; s3InSu3IsTrue =
        refl
    ; s3InSu3Diagnostic =
        "S3 is recorded only as a discrete subgroup/candidate inside SU(3)"
    ; s3InSu3DiagnosticIsCanonical =
        refl
    ; fullSU3FromPermutation =
        false
    ; fullSU3FromPermutationIsFalse =
        refl
    ; fullSU3FromPermutationReason =
        "S3 permutation symmetry is finite and discrete; S3 is not the full continuous SU(3) colour group"
    ; fullSU3FromPermutationReasonIsCanonical =
        refl
    ; exactGDHREqualsGSMRemains =
        false
    ; exactGDHREqualsGSMRemainsIsFalse =
        refl
    ; existingConditionalReceipt =
        Conditional.canonicalConditionalGDHRSMPromotionReceipt
    ; existingUnconditionalGDHREqualsGSMPromotedIsFalse =
        refl
    ; existingFullTheoremInRepoClaimedIsFalse =
        Conditional.canonicalConditionalGDHRSMPromotionNoFullTheorem
    ; su3ExtensionNeeds =
        canonicalSU3ExtensionNeeds
    ; su3ExtensionNeedsAreCanonical =
        refl
    ; extensionBoundary =
        "The finite p2/p3/p5 lane set has three-lane permutation symmetry S3"
        ∷ "S3 is admissible here only as a discrete SU(3) subgroup/candidate diagnostic"
        ∷ "A continuous SU(3) result would need a Lie group/topology, eight infinitesimal colour generators, a unitary determinant-one three-dimensional action, representation-category extension, and a DR/Tannaka compact gauge group construction"
        ∷ "This receipt does not promote S3 to full SU(3), does not prove S3 ~= SU(3), and keeps exact G_DHR ~= G_SM false"
        ∷ []
    }

colourFromPrimeLaneThreeLanePermutationSymmetryIsS3 :
  threeLanePermutationSymmetry canonicalColourFromPrimeLaneExtensionReceipt
  ≡
  S3
colourFromPrimeLaneThreeLanePermutationSymmetryIsS3 =
  refl

colourFromPrimeLaneS3InSU3IsTrue :
  s3InSu3 canonicalColourFromPrimeLaneExtensionReceipt
  ≡
  true
colourFromPrimeLaneS3InSU3IsTrue =
  refl

colourFromPrimeLaneFullSU3FromPermutationIsFalse :
  fullSU3FromPermutation canonicalColourFromPrimeLaneExtensionReceipt
  ≡
  false
colourFromPrimeLaneFullSU3FromPermutationIsFalse =
  refl

colourFromPrimeLaneExactGDHREqualsGSMRemainsFalse :
  exactGDHREqualsGSMRemains canonicalColourFromPrimeLaneExtensionReceipt
  ≡
  false
colourFromPrimeLaneExactGDHREqualsGSMRemainsFalse =
  refl
