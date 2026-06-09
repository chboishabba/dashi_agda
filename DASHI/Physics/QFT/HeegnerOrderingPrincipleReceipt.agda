module DASHI.Physics.QFT.HeegnerOrderingPrincipleReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Heegner-ordering principle receipt.
--
-- This receipt records a structural hypothesis only: order the thirteen
-- class-number-1 imaginary quadratic discriminants by absolute
-- discriminant, use the first six as a candidate Standard-Model matter-lane
-- surface, split those six into first-three quark candidates and next-three
-- lepton candidates, and leave the remaining seven as beyond-Standard-Model
-- candidates.
--
-- The receipt deliberately does not construct the Standard Model, a DHR
-- reconstruction equal to the Standard Model gauge group, a terminal
-- unification claim, or a proof of fourth-generation absence.  The existence
-- of ordered positions beyond six is recorded as the reason an additional
-- exclusion mechanism is still required.

data HeegnerOrderingStatus : Set where
  structuralCandidateOnly :
    HeegnerOrderingStatus

data MatterLaneKind : Set where
  quarkLaneCandidate :
    MatterLaneKind

  leptonLaneCandidate :
    MatterLaneKind

  beyondStandardModelCandidate :
    MatterLaneKind

data FourthGenerationAbsenceStatus : Set where
  requiresAdditionalMechanism :
    FourthGenerationAbsenceStatus

data HeegnerOrderingBlocker : Set where
  fourthGenerationAbsenceMechanismMissing :
    HeegnerOrderingBlocker

  exactQuarkSectorNotConstructed :
    HeegnerOrderingBlocker

  exactLeptonSectorNotConstructed :
    HeegnerOrderingBlocker

  exactStandardModelNotConstructed :
    HeegnerOrderingBlocker

  exactGDHRStandardModelMatchNotConstructed :
    HeegnerOrderingBlocker

  terminalUnificationNotConstructed :
    HeegnerOrderingBlocker

canonicalHeegnerAbsoluteDiscriminants :
  List Nat
canonicalHeegnerAbsoluteDiscriminants =
  3
  ∷ 4
  ∷ 7
  ∷ 8
  ∷ 11
  ∷ 12
  ∷ 16
  ∷ 19
  ∷ 27
  ∷ 28
  ∷ 43
  ∷ 67
  ∷ 163
  ∷ []

canonicalFirstThreeQuarkDiscriminants :
  List Nat
canonicalFirstThreeQuarkDiscriminants =
  3
  ∷ 4
  ∷ 7
  ∷ []

canonicalNextThreeLeptonDiscriminants :
  List Nat
canonicalNextThreeLeptonDiscriminants =
  8
  ∷ 11
  ∷ 12
  ∷ []

canonicalFirstSixMatterLaneDiscriminants :
  List Nat
canonicalFirstSixMatterLaneDiscriminants =
  3
  ∷ 4
  ∷ 7
  ∷ 8
  ∷ 11
  ∷ 12
  ∷ []

canonicalBeyondStandardModelDiscriminants :
  List Nat
canonicalBeyondStandardModelDiscriminants =
  16
  ∷ 19
  ∷ 27
  ∷ 28
  ∷ 43
  ∷ 67
  ∷ 163
  ∷ []

canonicalHeegnerOrderingBlockers :
  List HeegnerOrderingBlocker
canonicalHeegnerOrderingBlockers =
  fourthGenerationAbsenceMechanismMissing
  ∷ exactQuarkSectorNotConstructed
  ∷ exactLeptonSectorNotConstructed
  ∷ exactStandardModelNotConstructed
  ∷ exactGDHRStandardModelMatchNotConstructed
  ∷ terminalUnificationNotConstructed
  ∷ []

heegnerOrderingBoundaryLabel :
  String
heegnerOrderingBoundaryLabel =
  "Structural Heegner-ordering hypothesis only: first six class-number-1 discriminants form a candidate matter-lane surface; no exact SM/DHR/terminal promotion"

fourthGenerationAbsenceBoundaryLabel :
  String
fourthGenerationAbsenceBoundaryLabel =
  "Positions beyond six still exist in the Heegner sequence, so absence of a fourth generation requires an additional mechanism"

record HeegnerMatterLaneBlock : Set where
  field
    laneKind :
      MatterLaneKind

    discriminants :
      List Nat

    discriminantsAreCanonical :
      (laneKind ≡ quarkLaneCandidate
       → discriminants ≡ canonicalFirstThreeQuarkDiscriminants)

    leptonDiscriminantsAreCanonical :
      (laneKind ≡ leptonLaneCandidate
       → discriminants ≡ canonicalNextThreeLeptonDiscriminants)

    beyondSMDiscriminantsAreCanonical :
      (laneKind ≡ beyondStandardModelCandidate
       → discriminants ≡ canonicalBeyondStandardModelDiscriminants)

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

open HeegnerMatterLaneBlock public

canonicalQuarkLaneCandidateBlock :
  HeegnerMatterLaneBlock
canonicalQuarkLaneCandidateBlock =
  record
    { laneKind =
        quarkLaneCandidate
    ; discriminants =
        canonicalFirstThreeQuarkDiscriminants
    ; discriminantsAreCanonical =
        λ _ → refl
    ; leptonDiscriminantsAreCanonical =
        λ ()
    ; beyondSMDiscriminantsAreCanonical =
        λ ()
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    }

canonicalLeptonLaneCandidateBlock :
  HeegnerMatterLaneBlock
canonicalLeptonLaneCandidateBlock =
  record
    { laneKind =
        leptonLaneCandidate
    ; discriminants =
        canonicalNextThreeLeptonDiscriminants
    ; discriminantsAreCanonical =
        λ ()
    ; leptonDiscriminantsAreCanonical =
        λ _ → refl
    ; beyondSMDiscriminantsAreCanonical =
        λ ()
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    }

canonicalBeyondSMCandidateBlock :
  HeegnerMatterLaneBlock
canonicalBeyondSMCandidateBlock =
  record
    { laneKind =
        beyondStandardModelCandidate
    ; discriminants =
        canonicalBeyondStandardModelDiscriminants
    ; discriminantsAreCanonical =
        λ ()
    ; leptonDiscriminantsAreCanonical =
        λ ()
    ; beyondSMDiscriminantsAreCanonical =
        λ _ → refl
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    }

record HeegnerOrderingPrincipleReceipt : Setω where
  field
    status :
      HeegnerOrderingStatus

    statusIsStructuralCandidateOnly :
      status ≡ structuralCandidateOnly

    orderedAbsoluteDiscriminants :
      List Nat

    orderedAbsoluteDiscriminantsAreCanonical :
      orderedAbsoluteDiscriminants
      ≡
      canonicalHeegnerAbsoluteDiscriminants

    heegnerDiscriminantCount :
      Nat

    heegnerDiscriminantCountIsThirteen :
      heegnerDiscriminantCount ≡ 13

    firstSixMatterLaneCandidates :
      List Nat

    firstSixMatterLaneCandidatesAreCanonical :
      firstSixMatterLaneCandidates
      ≡
      canonicalFirstSixMatterLaneDiscriminants

    firstThreeQuarkLaneCandidates :
      HeegnerMatterLaneBlock

    firstThreeQuarkLaneCandidatesAreCanonical :
      firstThreeQuarkLaneCandidates
      ≡
      canonicalQuarkLaneCandidateBlock

    nextThreeLeptonLaneCandidates :
      HeegnerMatterLaneBlock

    nextThreeLeptonLaneCandidatesAreCanonical :
      nextThreeLeptonLaneCandidates
      ≡
      canonicalLeptonLaneCandidateBlock

    remainingSevenBeyondSMCandidates :
      HeegnerMatterLaneBlock

    remainingSevenBeyondSMCandidatesAreCanonical :
      remainingSevenBeyondSMCandidates
      ≡
      canonicalBeyondSMCandidateBlock

    beyondSMCandidateCount :
      Nat

    beyondSMCandidateCountIsSeven :
      beyondSMCandidateCount ≡ 7

    firstSixMatterLaneCandidateSurface :
      Bool

    firstSixMatterLaneCandidateSurfaceIsTrue :
      firstSixMatterLaneCandidateSurface ≡ true

    positionNotUnitGroupIsDistinguisher :
      Bool

    positionNotUnitGroupIsDistinguisherIsCandidateTrue :
      positionNotUnitGroupIsDistinguisher ≡ true

    fourthGenerationAbsence :
      FourthGenerationAbsenceStatus

    fourthGenerationAbsenceRequiresMechanism :
      fourthGenerationAbsence ≡ requiresAdditionalMechanism

    positionsBeyondSixStillExist :
      Bool

    positionsBeyondSixStillExistIsTrue :
      positionsBeyondSixStillExist ≡ true

    fourthGenerationAbsenceDerived :
      Bool

    fourthGenerationAbsenceDerivedIsFalse :
      fourthGenerationAbsenceDerived ≡ false

    fourthGenerationAbsenceRequiresAdditionalMechanism :
      Bool

    fourthGenerationAbsenceRequiresAdditionalMechanismIsTrue :
      fourthGenerationAbsenceRequiresAdditionalMechanism ≡ true

    exactQuarkSectorConstructed :
      Bool

    exactQuarkSectorConstructedIsFalse :
      exactQuarkSectorConstructed ≡ false

    exactLeptonSectorConstructed :
      Bool

    exactLeptonSectorConstructedIsFalse :
      exactLeptonSectorConstructed ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    blockers :
      List HeegnerOrderingBlocker

    blockersAreCanonical :
      blockers ≡ canonicalHeegnerOrderingBlockers

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ heegnerOrderingBoundaryLabel

    fourthGenerationBoundary :
      String

    fourthGenerationBoundaryIsCanonical :
      fourthGenerationBoundary ≡ fourthGenerationAbsenceBoundaryLabel

    auditTrail :
      List String

open HeegnerOrderingPrincipleReceipt public

canonicalHeegnerOrderingPrincipleReceipt :
  HeegnerOrderingPrincipleReceipt
canonicalHeegnerOrderingPrincipleReceipt =
  record
    { status =
        structuralCandidateOnly
    ; statusIsStructuralCandidateOnly =
        refl
    ; orderedAbsoluteDiscriminants =
        canonicalHeegnerAbsoluteDiscriminants
    ; orderedAbsoluteDiscriminantsAreCanonical =
        refl
    ; heegnerDiscriminantCount =
        13
    ; heegnerDiscriminantCountIsThirteen =
        refl
    ; firstSixMatterLaneCandidates =
        canonicalFirstSixMatterLaneDiscriminants
    ; firstSixMatterLaneCandidatesAreCanonical =
        refl
    ; firstThreeQuarkLaneCandidates =
        canonicalQuarkLaneCandidateBlock
    ; firstThreeQuarkLaneCandidatesAreCanonical =
        refl
    ; nextThreeLeptonLaneCandidates =
        canonicalLeptonLaneCandidateBlock
    ; nextThreeLeptonLaneCandidatesAreCanonical =
        refl
    ; remainingSevenBeyondSMCandidates =
        canonicalBeyondSMCandidateBlock
    ; remainingSevenBeyondSMCandidatesAreCanonical =
        refl
    ; beyondSMCandidateCount =
        7
    ; beyondSMCandidateCountIsSeven =
        refl
    ; firstSixMatterLaneCandidateSurface =
        true
    ; firstSixMatterLaneCandidateSurfaceIsTrue =
        refl
    ; positionNotUnitGroupIsDistinguisher =
        true
    ; positionNotUnitGroupIsDistinguisherIsCandidateTrue =
        refl
    ; fourthGenerationAbsence =
        requiresAdditionalMechanism
    ; fourthGenerationAbsenceRequiresMechanism =
        refl
    ; positionsBeyondSixStillExist =
        true
    ; positionsBeyondSixStillExistIsTrue =
        refl
    ; fourthGenerationAbsenceDerived =
        false
    ; fourthGenerationAbsenceDerivedIsFalse =
        refl
    ; fourthGenerationAbsenceRequiresAdditionalMechanism =
        true
    ; fourthGenerationAbsenceRequiresAdditionalMechanismIsTrue =
        refl
    ; exactQuarkSectorConstructed =
        false
    ; exactQuarkSectorConstructedIsFalse =
        refl
    ; exactLeptonSectorConstructed =
        false
    ; exactLeptonSectorConstructedIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; blockers =
        canonicalHeegnerOrderingBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        heegnerOrderingBoundaryLabel
    ; receiptBoundaryIsCanonical =
        refl
    ; fourthGenerationBoundary =
        fourthGenerationAbsenceBoundaryLabel
    ; fourthGenerationBoundaryIsCanonical =
        refl
    ; auditTrail =
        "Ordered class-number-1 absolute discriminants recorded: 3,4,7,8,11,12,16,19,27,28,43,67,163"
        ∷ "First three positions recorded as quark-lane candidates: 3,4,7"
        ∷ "Next three positions recorded as lepton-lane candidates: 8,11,12"
        ∷ "Remaining seven positions recorded as beyond-Standard-Model candidates: 16,19,27,28,43,67,163"
        ∷ "The first-six matter-lane surface is a structural candidate only"
        ∷ "Positions beyond six still exist, so fourth-generation absence requires an additional mechanism"
        ∷ "Exact quark sector, exact lepton sector, exact Standard Model, exact G_DHR=G_SM, and terminal promotion all remain false"
        ∷ []
    }

heegnerOrderingRecordsThirteenDiscriminants :
  heegnerDiscriminantCount canonicalHeegnerOrderingPrincipleReceipt
  ≡
  13
heegnerOrderingRecordsThirteenDiscriminants =
  refl

heegnerOrderingFirstSixMatterCandidatesCanonical :
  firstSixMatterLaneCandidates canonicalHeegnerOrderingPrincipleReceipt
  ≡
  canonicalFirstSixMatterLaneDiscriminants
heegnerOrderingFirstSixMatterCandidatesCanonical =
  refl

heegnerOrderingFirstThreeQuarksCanonical :
  firstThreeQuarkLaneCandidates canonicalHeegnerOrderingPrincipleReceipt
  ≡
  canonicalQuarkLaneCandidateBlock
heegnerOrderingFirstThreeQuarksCanonical =
  refl

heegnerOrderingNextThreeLeptonsCanonical :
  nextThreeLeptonLaneCandidates canonicalHeegnerOrderingPrincipleReceipt
  ≡
  canonicalLeptonLaneCandidateBlock
heegnerOrderingNextThreeLeptonsCanonical =
  refl

heegnerOrderingRemainingSevenBeyondSMCanonical :
  remainingSevenBeyondSMCandidates canonicalHeegnerOrderingPrincipleReceipt
  ≡
  canonicalBeyondSMCandidateBlock
heegnerOrderingRemainingSevenBeyondSMCanonical =
  refl

heegnerOrderingKeepsFourthGenerationAbsenceUnproved :
  fourthGenerationAbsenceDerived canonicalHeegnerOrderingPrincipleReceipt
  ≡
  false
heegnerOrderingKeepsFourthGenerationAbsenceUnproved =
  refl

heegnerOrderingRecordsFourthGenerationMechanismNeeded :
  fourthGenerationAbsenceRequiresAdditionalMechanism
    canonicalHeegnerOrderingPrincipleReceipt
  ≡
  true
heegnerOrderingRecordsFourthGenerationMechanismNeeded =
  refl

heegnerOrderingKeepsExactQuarkSectorFalse :
  exactQuarkSectorConstructed canonicalHeegnerOrderingPrincipleReceipt
  ≡
  false
heegnerOrderingKeepsExactQuarkSectorFalse =
  refl

heegnerOrderingKeepsExactLeptonSectorFalse :
  exactLeptonSectorConstructed canonicalHeegnerOrderingPrincipleReceipt
  ≡
  false
heegnerOrderingKeepsExactLeptonSectorFalse =
  refl

heegnerOrderingKeepsExactSMFalse :
  exactStandardModelPromotion canonicalHeegnerOrderingPrincipleReceipt
  ≡
  false
heegnerOrderingKeepsExactSMFalse =
  refl

heegnerOrderingKeepsGDHRSMFalse :
  gDHREqualsGSMPromoted canonicalHeegnerOrderingPrincipleReceipt
  ≡
  false
heegnerOrderingKeepsGDHRSMFalse =
  refl

heegnerOrderingKeepsTerminalClaimFalse :
  terminalClaimPromoted canonicalHeegnerOrderingPrincipleReceipt
  ≡
  false
heegnerOrderingKeepsTerminalClaimFalse =
  refl
