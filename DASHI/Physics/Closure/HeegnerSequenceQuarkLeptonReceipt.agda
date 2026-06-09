module DASHI.Physics.Closure.HeegnerSequenceQuarkLeptonReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Heegner sequence quark/lepton positional candidate receipt.
--
-- This receipt records only a structural positional hypothesis.  The first
-- six Heegner discriminants by absolute value are 3, 4, 7, 8, 11, and 12.
-- The candidate reading assigns the first three positions to quark lanes,
-- the next three positions to lepton candidates, and any later positions to
-- beyond-Standard-Model candidates.  No Standard Model matter derivation,
-- quark/lepton separation theorem, fourth-generation exclusion, or physical
-- lepton mapping is constructed here.

data HeegnerSequenceStatus : Set where
  positionalQuarkLeptonCandidateRecorded :
    HeegnerSequenceStatus

data HeegnerSequenceRole : Set where
  quarkLaneCandidate :
    HeegnerSequenceRole

  leptonLaneCandidate :
    HeegnerSequenceRole

  beyondSMCandidate :
    HeegnerSequenceRole

data HeegnerSequenceBlocker : Set where
  positionalRuleNotDerived :
    HeegnerSequenceBlocker

  noFourthGenerationAbsenceMechanism :
    HeegnerSequenceBlocker

  leptonMappingNotPhysicalPromotion :
    HeegnerSequenceBlocker

  noDerivedStandardModelMatter :
    HeegnerSequenceBlocker

canonicalHeegnerSequenceBlockers :
  List HeegnerSequenceBlocker
canonicalHeegnerSequenceBlockers =
  positionalRuleNotDerived
  ∷ noFourthGenerationAbsenceMechanism
  ∷ leptonMappingNotPhysicalPromotion
  ∷ noDerivedStandardModelMatter
  ∷ []

data HeegnerSequencePromotion : Set where

heegnerSequencePromotionImpossibleHere :
  HeegnerSequencePromotion →
  ⊥
heegnerSequencePromotionImpossibleHere ()

record HeegnerSequenceEntry : Set where
  field
    position :
      Nat

    absoluteDiscriminant :
      Nat

    role :
      HeegnerSequenceRole

    label :
      String

open HeegnerSequenceEntry public

heegnerD3Entry : HeegnerSequenceEntry
heegnerD3Entry =
  record
    { position = 1
    ; absoluteDiscriminant = 3
    ; role = quarkLaneCandidate
    ; label = "position 1, |D|=3, quark-lane candidate"
    }

heegnerD4Entry : HeegnerSequenceEntry
heegnerD4Entry =
  record
    { position = 2
    ; absoluteDiscriminant = 4
    ; role = quarkLaneCandidate
    ; label = "position 2, |D|=4, quark-lane candidate"
    }

heegnerD7Entry : HeegnerSequenceEntry
heegnerD7Entry =
  record
    { position = 3
    ; absoluteDiscriminant = 7
    ; role = quarkLaneCandidate
    ; label = "position 3, |D|=7, quark-lane candidate"
    }

heegnerD8Entry : HeegnerSequenceEntry
heegnerD8Entry =
  record
    { position = 4
    ; absoluteDiscriminant = 8
    ; role = leptonLaneCandidate
    ; label = "position 4, |D|=8, lepton-lane candidate"
    }

heegnerD11Entry : HeegnerSequenceEntry
heegnerD11Entry =
  record
    { position = 5
    ; absoluteDiscriminant = 11
    ; role = leptonLaneCandidate
    ; label = "position 5, |D|=11, lepton-lane candidate"
    }

heegnerD12Entry : HeegnerSequenceEntry
heegnerD12Entry =
  record
    { position = 6
    ; absoluteDiscriminant = 12
    ; role = leptonLaneCandidate
    ; label = "position 6, |D|=12, lepton-lane candidate"
    }

canonicalFirstSixHeegnerSequence :
  List HeegnerSequenceEntry
canonicalFirstSixHeegnerSequence =
  heegnerD3Entry
  ∷ heegnerD4Entry
  ∷ heegnerD7Entry
  ∷ heegnerD8Entry
  ∷ heegnerD11Entry
  ∷ heegnerD12Entry
  ∷ []

firstSixHeegnerAbsDLabel : String
firstSixHeegnerAbsDLabel =
  "first six Heegner discriminants by |D|: 3, 4, 7, 8, 11, 12"

positionalRuleLabel : String
positionalRuleLabel =
  "candidate positional rule: positions 1-3 quark lanes, positions 4-6 lepton candidates, positions >6 beyond-SM candidates"

beyondSMCandidateLabel : String
beyondSMCandidateLabel =
  "remaining Heegner positions beyond the first six are beyond-SM candidates only"

record HeegnerSequenceQuarkLeptonReceipt : Setω where
  field
    status :
      HeegnerSequenceStatus

    firstSixSequence :
      List HeegnerSequenceEntry

    firstSixSequenceIsCanonical :
      firstSixSequence ≡ canonicalFirstSixHeegnerSequence

    firstSixAbsDStatement :
      String

    firstSixAbsDStatementIsCanonical :
      firstSixAbsDStatement ≡ firstSixHeegnerAbsDLabel

    positionalRule :
      String

    positionalRuleIsCanonical :
      positionalRule ≡ positionalRuleLabel

    firstQuarkCandidate :
      HeegnerSequenceEntry

    firstQuarkCandidateIsD3 :
      firstQuarkCandidate ≡ heegnerD3Entry

    secondQuarkCandidate :
      HeegnerSequenceEntry

    secondQuarkCandidateIsD4 :
      secondQuarkCandidate ≡ heegnerD4Entry

    thirdQuarkCandidate :
      HeegnerSequenceEntry

    thirdQuarkCandidateIsD7 :
      thirdQuarkCandidate ≡ heegnerD7Entry

    firstLeptonCandidate :
      HeegnerSequenceEntry

    firstLeptonCandidateIsD8 :
      firstLeptonCandidate ≡ heegnerD8Entry

    secondLeptonCandidate :
      HeegnerSequenceEntry

    secondLeptonCandidateIsD11 :
      secondLeptonCandidate ≡ heegnerD11Entry

    thirdLeptonCandidate :
      HeegnerSequenceEntry

    thirdLeptonCandidateIsD12 :
      thirdLeptonCandidate ≡ heegnerD12Entry

    beyondSMCandidateStatement :
      String

    beyondSMCandidateStatementIsCanonical :
      beyondSMCandidateStatement ≡ beyondSMCandidateLabel

    structuralCandidateOnly :
      Bool

    structuralCandidateOnlyIsTrue :
      structuralCandidateOnly ≡ true

    positionalRuleDerived :
      Bool

    positionalRuleDerivedIsFalse :
      positionalRuleDerived ≡ false

    fourthGenerationAbsenceMechanism :
      Bool

    fourthGenerationAbsenceMechanismIsFalse :
      fourthGenerationAbsenceMechanism ≡ false

    leptonMappingPhysicalPromotion :
      Bool

    leptonMappingPhysicalPromotionIsFalse :
      leptonMappingPhysicalPromotion ≡ false

    derivedStandardModelMatter :
      Bool

    derivedStandardModelMatterIsFalse :
      derivedStandardModelMatter ≡ false

    physicalSMQuarkLeptonPromotion :
      Bool

    physicalSMQuarkLeptonPromotionIsFalse :
      physicalSMQuarkLeptonPromotion ≡ false

    blockers :
      List HeegnerSequenceBlocker

    blockersAreCanonical :
      blockers ≡ canonicalHeegnerSequenceBlockers

    promotionFlags :
      List HeegnerSequencePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open HeegnerSequenceQuarkLeptonReceipt public

canonicalHeegnerSequenceQuarkLeptonReceipt :
  HeegnerSequenceQuarkLeptonReceipt
canonicalHeegnerSequenceQuarkLeptonReceipt =
  record
    { status =
        positionalQuarkLeptonCandidateRecorded
    ; firstSixSequence =
        canonicalFirstSixHeegnerSequence
    ; firstSixSequenceIsCanonical =
        refl
    ; firstSixAbsDStatement =
        firstSixHeegnerAbsDLabel
    ; firstSixAbsDStatementIsCanonical =
        refl
    ; positionalRule =
        positionalRuleLabel
    ; positionalRuleIsCanonical =
        refl
    ; firstQuarkCandidate =
        heegnerD3Entry
    ; firstQuarkCandidateIsD3 =
        refl
    ; secondQuarkCandidate =
        heegnerD4Entry
    ; secondQuarkCandidateIsD4 =
        refl
    ; thirdQuarkCandidate =
        heegnerD7Entry
    ; thirdQuarkCandidateIsD7 =
        refl
    ; firstLeptonCandidate =
        heegnerD8Entry
    ; firstLeptonCandidateIsD8 =
        refl
    ; secondLeptonCandidate =
        heegnerD11Entry
    ; secondLeptonCandidateIsD11 =
        refl
    ; thirdLeptonCandidate =
        heegnerD12Entry
    ; thirdLeptonCandidateIsD12 =
        refl
    ; beyondSMCandidateStatement =
        beyondSMCandidateLabel
    ; beyondSMCandidateStatementIsCanonical =
        refl
    ; structuralCandidateOnly =
        true
    ; structuralCandidateOnlyIsTrue =
        refl
    ; positionalRuleDerived =
        false
    ; positionalRuleDerivedIsFalse =
        refl
    ; fourthGenerationAbsenceMechanism =
        false
    ; fourthGenerationAbsenceMechanismIsFalse =
        refl
    ; leptonMappingPhysicalPromotion =
        false
    ; leptonMappingPhysicalPromotionIsFalse =
        refl
    ; derivedStandardModelMatter =
        false
    ; derivedStandardModelMatterIsFalse =
        refl
    ; physicalSMQuarkLeptonPromotion =
        false
    ; physicalSMQuarkLeptonPromotionIsFalse =
        refl
    ; blockers =
        canonicalHeegnerSequenceBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The first six Heegner discriminants by absolute value are recorded as 3,4,7,8,11,12"
        ∷ "Positions 1-3 are quark-lane candidates and positions 4-6 are lepton-lane candidates by hypothesis only"
        ∷ "Remaining Heegner positions are beyond-SM candidates only under the same positional convention"
        ∷ "The positional rule is not derived, no fourth-generation absence mechanism is supplied, and lepton mapping is not physically promoted"
        ∷ "No derived Standard Model matter or quark/lepton promotion is asserted"
        ∷ []
    }

heegnerSequenceIsStructuralCandidateOnly :
  structuralCandidateOnly canonicalHeegnerSequenceQuarkLeptonReceipt
  ≡
  true
heegnerSequenceIsStructuralCandidateOnly =
  refl

heegnerSequencePositionalRuleNotDerived :
  positionalRuleDerived canonicalHeegnerSequenceQuarkLeptonReceipt
  ≡
  false
heegnerSequencePositionalRuleNotDerived =
  refl

heegnerSequenceNoFourthGenerationAbsenceMechanism :
  fourthGenerationAbsenceMechanism canonicalHeegnerSequenceQuarkLeptonReceipt
  ≡
  false
heegnerSequenceNoFourthGenerationAbsenceMechanism =
  refl

heegnerSequenceNoPhysicalLeptonPromotion :
  leptonMappingPhysicalPromotion canonicalHeegnerSequenceQuarkLeptonReceipt
  ≡
  false
heegnerSequenceNoPhysicalLeptonPromotion =
  refl

heegnerSequenceNoDerivedStandardModelMatter :
  derivedStandardModelMatter canonicalHeegnerSequenceQuarkLeptonReceipt
  ≡
  false
heegnerSequenceNoDerivedStandardModelMatter =
  refl
