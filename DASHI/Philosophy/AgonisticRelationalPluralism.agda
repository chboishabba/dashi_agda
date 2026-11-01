module DASHI.Philosophy.AgonisticRelationalPluralism where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Plural attachment is not automatic equality of legal, historical,
-- political, or moral claims.

data ClaimDimension : Set where
  attachment :
    ClaimDimension

  historicalContinuity :
    ClaimDimension

  peoplehood :
    ClaimDimension

  politicalStatus :
    ClaimDimension

  power :
    ClaimDimension

  injury :
    ClaimDimension

  responsibility :
    ClaimDimension

  ecologicalObligation :
    ClaimDimension

canonicalClaimDimensions :
  List ClaimDimension
canonicalClaimDimensions =
  attachment
  ∷ historicalContinuity
  ∷ peoplehood
  ∷ politicalStatus
  ∷ power
  ∷ injury
  ∷ responsibility
  ∷ ecologicalObligation
  ∷ []

record DifferentiatedLandRelation
       (People Land Relation Evidence : Set) : Set₁ where
  field
    people :
      People

    land :
      Land

    relation :
      Relation

    evidence :
      Evidence

    dimensionsTracked :
      List ClaimDimension

    attachmentIsReal :
      Set

    claimIsNotReducedToFeeling :
      Set

open DifferentiatedLandRelation public

record RootingAndShifting
       (A B Root Shift : Set) : Set₁ where
  field
    partyA :
      A

    partyB :
      B

    rootedPosition :
      Root

    shiftedUnderstanding :
      Shift

    rootingPreventsAssimilation :
      Set

    shiftingPreventsEnclosure :
      Set

open RootingAndShifting public

record AgonisticPluralismBoundary : Set where
  constructor mkAgonisticPluralismBoundary
  field
    multipleAttachmentsCanBeReal :
      Bool

    allRealAttachmentsAreEquivalent :
      Bool

    asymmetricalPowerMustRemainVisible :
      Bool

    dialogueGuaranteesReconciliation :
      Bool

    adjudicationCanStillBeRequired :
      Bool

    landPrecedesPropertyRegime :
      Bool

    landAloneDeterminesPoliticalJustice :
      Bool

open AgonisticPluralismBoundary public

canonicalAgonisticPluralismBoundary :
  AgonisticPluralismBoundary
canonicalAgonisticPluralismBoundary =
  mkAgonisticPluralismBoundary
    true
    false
    true
    false
    true
    true
    false

canonicalNoFalseEquivalence :
  allRealAttachmentsAreEquivalent canonicalAgonisticPluralismBoundary
  ≡
  false
canonicalNoFalseEquivalence =
  refl

canonicalLandDoesNotUniquelyAdjudicate :
  landAloneDeterminesPoliticalJustice canonicalAgonisticPluralismBoundary
  ≡
  false
canonicalLandDoesNotUniquelyAdjudicate =
  refl
