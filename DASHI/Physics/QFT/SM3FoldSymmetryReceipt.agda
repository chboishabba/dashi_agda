module DASHI.Physics.QFT.SM3FoldSymmetryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Three-fold Standard Model symmetry reconstruction receipt.
--
-- This receipt is a compact status map for the current finite/conditional
-- SM reconstruction surface.  It records the three visible branches:
--
--   * SU2_L is conditional on the supplied spin-sector Rep(SU2) input.
--   * U1_Y is a candidate read from the order-three subset of the Z/6
--     finite CM-character factor.
--   * SU3_c remains open at the depth-2 / triality extension frontier.
--
-- It deliberately does not promote G_DHR = G_SM.

data SM3FoldSymmetryBranch : Set where
  su2LSpinSectorBranch :
    SM3FoldSymmetryBranch

  u1yZ3InsideZ6Branch :
    SM3FoldSymmetryBranch

  su3cDepth2TrialityFrontierBranch :
    SM3FoldSymmetryBranch

canonicalSM3FoldSymmetryBranches :
  List SM3FoldSymmetryBranch
canonicalSM3FoldSymmetryBranches =
  su2LSpinSectorBranch
  ∷ u1yZ3InsideZ6Branch
  ∷ su3cDepth2TrialityFrontierBranch
  ∷ []

data Z6HyperchargeCandidateSubsetElement : Set where
  z6-0 :
    Z6HyperchargeCandidateSubsetElement

  z6-2 :
    Z6HyperchargeCandidateSubsetElement

  z6-4 :
    Z6HyperchargeCandidateSubsetElement

canonicalZ3SubsetOfZ6ForU1YCandidate :
  List Z6HyperchargeCandidateSubsetElement
canonicalZ3SubsetOfZ6ForU1YCandidate =
  z6-0
  ∷ z6-2
  ∷ z6-4
  ∷ []

z3SubsetOfZ6Cardinality : Nat
z3SubsetOfZ6Cardinality =
  3

su2LConditionalLabel : String
su2LConditionalLabel =
  "SU2_L is conditional on the supplied spin-sector Rep(SU2) witness"

u1yCandidateLabel : String
u1yCandidateLabel =
  "U1_Y is recorded as a candidate from the Z/3 subset {0,2,4} inside the finite Z/6 factor"

su3cOpenLabel : String
su3cOpenLabel =
  "SU3_c remains open at the depth-2 / triality extension frontier"

gDHREqualsGSMNotPromotedLabel : String
gDHREqualsGSMNotPromotedLabel =
  "G_DHR = G_SM is not promoted by this three-fold status receipt"

record SM3FoldSymmetryReceipt : Setω where
  field
    branches :
      List SM3FoldSymmetryBranch

    branchesAreCanonical :
      branches ≡ canonicalSM3FoldSymmetryBranches

    smReconstructionCandidateMap :
      Bool

    smReconstructionCandidateMapIsTrue :
      smReconstructionCandidateMap ≡ true

    su2LConditional :
      Bool

    su2LConditionalIsTrue :
      su2LConditional ≡ true

    su2LCondition :
      String

    su2LConditionIsCanonical :
      su2LCondition ≡ su2LConditionalLabel

    u1yCandidate :
      Bool

    u1yCandidateIsTrue :
      u1yCandidate ≡ true

    u1yCandidateSubset :
      List Z6HyperchargeCandidateSubsetElement

    u1yCandidateSubsetIsZ3InsideZ6 :
      u1yCandidateSubset ≡ canonicalZ3SubsetOfZ6ForU1YCandidate

    u1yCandidateSubsetCardinality :
      Nat

    u1yCandidateSubsetCardinalityIsThree :
      u1yCandidateSubsetCardinality ≡ z3SubsetOfZ6Cardinality

    u1yCandidateBoundary :
      String

    u1yCandidateBoundaryIsCanonical :
      u1yCandidateBoundary ≡ u1yCandidateLabel

    su3cOpen :
      Bool

    su3cOpenIsTrue :
      su3cOpen ≡ true

    su3cOpenBoundary :
      String

    su3cOpenBoundaryIsCanonical :
      su3cOpenBoundary ≡ su3cOpenLabel

    depth2TrialityExtensionConsumedAsFrontier :
      Bool

    depth2TrialityExtensionConsumedAsFrontierIsTrue :
      depth2TrialityExtensionConsumedAsFrontier ≡ true

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    gDHREqualsGSMBoundary :
      String

    gDHREqualsGSMBoundaryIsCanonical :
      gDHREqualsGSMBoundary ≡ gDHREqualsGSMNotPromotedLabel

    receiptBoundary :
      List String

open SM3FoldSymmetryReceipt public

canonicalSM3FoldSymmetryReceipt :
  SM3FoldSymmetryReceipt
canonicalSM3FoldSymmetryReceipt =
  record
    { branches =
        canonicalSM3FoldSymmetryBranches
    ; branchesAreCanonical =
        refl
    ; smReconstructionCandidateMap =
        true
    ; smReconstructionCandidateMapIsTrue =
        refl
    ; su2LConditional =
        true
    ; su2LConditionalIsTrue =
        refl
    ; su2LCondition =
        su2LConditionalLabel
    ; su2LConditionIsCanonical =
        refl
    ; u1yCandidate =
        true
    ; u1yCandidateIsTrue =
        refl
    ; u1yCandidateSubset =
        canonicalZ3SubsetOfZ6ForU1YCandidate
    ; u1yCandidateSubsetIsZ3InsideZ6 =
        refl
    ; u1yCandidateSubsetCardinality =
        z3SubsetOfZ6Cardinality
    ; u1yCandidateSubsetCardinalityIsThree =
        refl
    ; u1yCandidateBoundary =
        u1yCandidateLabel
    ; u1yCandidateBoundaryIsCanonical =
        refl
    ; su3cOpen =
        true
    ; su3cOpenIsTrue =
        refl
    ; su3cOpenBoundary =
        su3cOpenLabel
    ; su3cOpenBoundaryIsCanonical =
        refl
    ; depth2TrialityExtensionConsumedAsFrontier =
        true
    ; depth2TrialityExtensionConsumedAsFrontierIsTrue =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; gDHREqualsGSMBoundary =
        gDHREqualsGSMNotPromotedLabel
    ; gDHREqualsGSMBoundaryIsCanonical =
        refl
    ; receiptBoundary =
        "SM reconstruction candidate map is recorded but not promoted"
        ∷ "SU2_L is conditional from the spin-sector Rep(SU2) branch"
        ∷ "U1_Y is a candidate from the Z/3 subset of the finite Z/6 branch"
        ∷ "SU3_c is open at the depth-2 / triality extension branch"
        ∷ "G_DHR = G_SM remains false"
        ∷ []
    }

sm3FoldSymmetryReceiptKeepsGDHRGSMFalse :
  gDHREqualsGSMPromoted canonicalSM3FoldSymmetryReceipt ≡ false
sm3FoldSymmetryReceiptKeepsGDHRGSMFalse =
  gDHREqualsGSMPromotedIsFalse canonicalSM3FoldSymmetryReceipt

sm3FoldSymmetryReceiptHasCandidateMap :
  smReconstructionCandidateMap canonicalSM3FoldSymmetryReceipt ≡ true
sm3FoldSymmetryReceiptHasCandidateMap =
  smReconstructionCandidateMapIsTrue canonicalSM3FoldSymmetryReceipt
