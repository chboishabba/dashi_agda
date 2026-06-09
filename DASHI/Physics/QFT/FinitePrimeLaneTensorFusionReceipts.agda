module DASHI.Physics.QFT.FinitePrimeLaneTensorFusionReceipts where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.FinitePrimeLaneDHRSMCompatibilityLedger as Ledger

------------------------------------------------------------------------
-- Finite p2/p3/p5 tensor-fusion receipts.
--
-- This module is deliberately finite-prime-lane only.  It records the three
-- pairwise external-product fusion rules that can be enumerated from the
-- existing p2, p3, and p5 finite rows.  The decomposition is a finite
-- singleton external-product decomposition for each pair.  Nothing here
-- constructs arbitrary DHR tensor closure, a full representation ring,
-- Doplicher-Roberts reconstruction, or G_DHR ~= G_SM.

data FiniteTensorSector : Set where
  tensorSector-p2 :
    FiniteTensorSector

  tensorSector-p3 :
    FiniteTensorSector

  tensorSector-p5 :
    FiniteTensorSector

finiteTensorSectorDimension :
  FiniteTensorSector →
  Nat
finiteTensorSectorDimension tensorSector-p2 =
  1
finiteTensorSectorDimension tensorSector-p3 =
  2
finiteTensorSectorDimension tensorSector-p5 =
  3

finiteTensorSectorRow :
  FiniteTensorSector →
  Ledger.FinitePrimeLaneSMRow
finiteTensorSectorRow tensorSector-p2 =
  Ledger.p2U1YFinitePrimeLaneSMRow
finiteTensorSectorRow tensorSector-p3 =
  Ledger.p3SU2LFinitePrimeLaneSMRow
finiteTensorSectorRow tensorSector-p5 =
  Ledger.p5SU3cFinitePrimeLaneSMRow

data FiniteTensorFusionPair : Set where
  p2p3TensorFusionPair :
    FiniteTensorFusionPair

  p2p5TensorFusionPair :
    FiniteTensorFusionPair

  p3p5TensorFusionPair :
    FiniteTensorFusionPair

finiteTensorFusionLeft :
  FiniteTensorFusionPair →
  FiniteTensorSector
finiteTensorFusionLeft p2p3TensorFusionPair =
  tensorSector-p2
finiteTensorFusionLeft p2p5TensorFusionPair =
  tensorSector-p2
finiteTensorFusionLeft p3p5TensorFusionPair =
  tensorSector-p3

finiteTensorFusionRight :
  FiniteTensorFusionPair →
  FiniteTensorSector
finiteTensorFusionRight p2p3TensorFusionPair =
  tensorSector-p3
finiteTensorFusionRight p2p5TensorFusionPair =
  tensorSector-p5
finiteTensorFusionRight p3p5TensorFusionPair =
  tensorSector-p5

finiteTensorFusionDimension :
  FiniteTensorFusionPair →
  Nat
finiteTensorFusionDimension pair =
  finiteTensorSectorDimension (finiteTensorFusionLeft pair)
  *
  finiteTensorSectorDimension (finiteTensorFusionRight pair)

data FiniteTensorFusionProductSector :
  FiniteTensorFusionPair →
  Set where
  p2p3ExternalProductSector :
    FiniteTensorFusionProductSector p2p3TensorFusionPair

  p2p5ExternalProductSector :
    FiniteTensorFusionProductSector p2p5TensorFusionPair

  p3p5ExternalProductSector :
    FiniteTensorFusionProductSector p3p5TensorFusionPair

canonicalFiniteTensorFusionDecomposition :
  (pair : FiniteTensorFusionPair) →
  List (FiniteTensorFusionProductSector pair)
canonicalFiniteTensorFusionDecomposition p2p3TensorFusionPair =
  p2p3ExternalProductSector
  ∷ []
canonicalFiniteTensorFusionDecomposition p2p5TensorFusionPair =
  p2p5ExternalProductSector
  ∷ []
canonicalFiniteTensorFusionDecomposition p3p5TensorFusionPair =
  p3p5ExternalProductSector
  ∷ []

finiteTensorFusionRuleLabel :
  FiniteTensorFusionPair →
  String
finiteTensorFusionRuleLabel p2p3TensorFusionPair =
  "rho_p2 tensor rho_p3 decomposes as the finite external-product sector rho_p2 boxtimes rho_p3"
finiteTensorFusionRuleLabel p2p5TensorFusionPair =
  "rho_p2 tensor rho_p5 decomposes as the finite external-product sector rho_p2 boxtimes rho_p5"
finiteTensorFusionRuleLabel p3p5TensorFusionPair =
  "rho_p3 tensor rho_p5 decomposes as the finite external-product sector rho_p3 boxtimes rho_p5"

p2LaneUnitsZ4Label : String
p2LaneUnitsZ4Label =
  "p2 lane units Z/4"

p5CorrectedHeegnerLaneUnitsZ2Label : String
p5CorrectedHeegnerLaneUnitsZ2Label =
  "corrected p5 Heegner lane units Z/2 from Z[(1+sqrt(-7))/2]"

p2p5ProductCharacterCountLabel : String
p2p5ProductCharacterCountLabel =
  "p2 tensor p5 product character count 8"

p3LaneUnitsZ6Label : String
p3LaneUnitsZ6Label =
  "p3 lane units Z/6"

p3p5ProductCharacterCountLabel : String
p3p5ProductCharacterCountLabel =
  "p3 tensor p5 product character count 12"

p2p3EndomorphismProductLabel : String
p2p3EndomorphismProductLabel =
  "End(E_p2 x E_p3) CM unit-character product Z/4 x Z/6"

p2p3ProductCharacterCountCanonicalLabel : String
p2p3ProductCharacterCountCanonicalLabel =
  "p2 tensor p3 product character count 24"

record P2P3CharacterCountEnrichment : Set where
  field
    p2CMUnitCharacters :
      String

    p2CMUnitCharactersAreZ4 :
      p2CMUnitCharacters ≡ "Z/4"

    p2p3P2CharacterCount :
      Nat

    p2p3P2CharacterCountIsFour :
      p2p3P2CharacterCount ≡ 4

    p3CMUnitCharacters :
      String

    p3CMUnitCharactersAreZ6 :
      p3CMUnitCharacters ≡ "Z/6"

    p2p3P3CharacterCount :
      Nat

    p2p3P3CharacterCountIsSix :
      p2p3P3CharacterCount ≡ 6

    endomorphismProduct :
      String

    endomorphismProductIsCanonical :
      endomorphismProduct ≡ p2p3EndomorphismProductLabel

    p2p3ProductCharacterCount :
      Nat

    p2p3ProductCharacterCountIsProduct :
      p2p3ProductCharacterCount
      ≡
      p2p3P2CharacterCount * p2p3P3CharacterCount

    p2p3ProductCharacterCountIsTwentyFour :
      p2p3ProductCharacterCount ≡ 24

    p2p3ProductCharacterCountLabel :
      String

    p2p3ProductCharacterCountLabelIsCanonical :
      p2p3ProductCharacterCountLabel
      ≡
      p2p3ProductCharacterCountCanonicalLabel

    p2p3FiniteCharacterCountComputed :
      Bool

    p2p3FiniteCharacterCountComputedIsTrue :
      p2p3FiniteCharacterCountComputed ≡ true

    p2p3ArbitraryTensorClosurePromoted :
      Bool

    p2p3ArbitraryTensorClosurePromotedIsFalse :
      p2p3ArbitraryTensorClosurePromoted ≡ false

    p2p3FullRepresentationRingComputed :
      Bool

    p2p3FullRepresentationRingComputedIsFalse :
      p2p3FullRepresentationRingComputed ≡ false

    p2p3EnrichmentBoundary :
      List String

open P2P3CharacterCountEnrichment public

p2p3CharacterCountEnrichment :
  P2P3CharacterCountEnrichment
p2p3CharacterCountEnrichment =
  record
    { p2CMUnitCharacters =
        "Z/4"
    ; p2CMUnitCharactersAreZ4 =
        refl
    ; p2p3P2CharacterCount =
        4
    ; p2p3P2CharacterCountIsFour =
        refl
    ; p3CMUnitCharacters =
        "Z/6"
    ; p3CMUnitCharactersAreZ6 =
        refl
    ; p2p3P3CharacterCount =
        6
    ; p2p3P3CharacterCountIsSix =
        refl
    ; endomorphismProduct =
        p2p3EndomorphismProductLabel
    ; endomorphismProductIsCanonical =
        refl
    ; p2p3ProductCharacterCount =
        24
    ; p2p3ProductCharacterCountIsProduct =
        refl
    ; p2p3ProductCharacterCountIsTwentyFour =
        refl
    ; p2p3ProductCharacterCountLabel =
        p2p3ProductCharacterCountCanonicalLabel
    ; p2p3ProductCharacterCountLabelIsCanonical =
        refl
    ; p2p3FiniteCharacterCountComputed =
        true
    ; p2p3FiniteCharacterCountComputedIsTrue =
        refl
    ; p2p3ArbitraryTensorClosurePromoted =
        false
    ; p2p3ArbitraryTensorClosurePromotedIsFalse =
        refl
    ; p2p3FullRepresentationRingComputed =
        false
    ; p2p3FullRepresentationRingComputedIsFalse =
        refl
    ; p2p3EnrichmentBoundary =
        "p2 tensor p3 character count is finite: End(E_p2 x E_p3) CM unit-character product Z/4 x Z/6"
        ∷ "The product character count is 4 * 6 = 24"
        ∷ "This enrichment keeps full representation-ring and arbitrary DHR closure promotion false"
        ∷ []
    }

record P2P5CharacterCountEnrichment : Set where
  field
    p2LaneUnits :
      String

    p2LaneUnitsAreZ4 :
      p2LaneUnits ≡ p2LaneUnitsZ4Label

    p2CharacterCount :
      Nat

    p2CharacterCountIsFour :
      p2CharacterCount ≡ 4

    p5LaneUnits :
      String

    p5LaneUnitsAreCorrectedHeegnerZ2 :
      p5LaneUnits ≡ p5CorrectedHeegnerLaneUnitsZ2Label

    p5CharacterCount :
      Nat

    p5CharacterCountIsTwo :
      p5CharacterCount ≡ 2

    productCharacterCount :
      Nat

    productCharacterCountIsProduct :
      productCharacterCount ≡ p2CharacterCount * p5CharacterCount

    productCharacterCountIsEight :
      productCharacterCount ≡ 8

    productCharacterCountLabel :
      String

    productCharacterCountLabelIsCanonical :
      productCharacterCountLabel ≡ p2p5ProductCharacterCountLabel

    finiteCharacterCountComputed :
      Bool

    finiteCharacterCountComputedIsTrue :
      finiteCharacterCountComputed ≡ true

    arbitraryTensorClosurePromoted :
      Bool

    arbitraryTensorClosurePromotedIsFalse :
      arbitraryTensorClosurePromoted ≡ false

    fullRepresentationRingComputed :
      Bool

    fullRepresentationRingComputedIsFalse :
      fullRepresentationRingComputed ≡ false

    enrichmentBoundary :
      List String

open P2P5CharacterCountEnrichment public

p2p5CharacterCountEnrichment :
  P2P5CharacterCountEnrichment
p2p5CharacterCountEnrichment =
  record
    { p2LaneUnits =
        p2LaneUnitsZ4Label
    ; p2LaneUnitsAreZ4 =
        refl
    ; p2CharacterCount =
        4
    ; p2CharacterCountIsFour =
        refl
    ; p5LaneUnits =
        p5CorrectedHeegnerLaneUnitsZ2Label
    ; p5LaneUnitsAreCorrectedHeegnerZ2 =
        refl
    ; p5CharacterCount =
        2
    ; p5CharacterCountIsTwo =
        refl
    ; productCharacterCount =
        8
    ; productCharacterCountIsProduct =
        refl
    ; productCharacterCountIsEight =
        refl
    ; productCharacterCountLabel =
        p2p5ProductCharacterCountLabel
    ; productCharacterCountLabelIsCanonical =
        refl
    ; finiteCharacterCountComputed =
        true
    ; finiteCharacterCountComputedIsTrue =
        refl
    ; arbitraryTensorClosurePromoted =
        false
    ; arbitraryTensorClosurePromotedIsFalse =
        refl
    ; fullRepresentationRingComputed =
        false
    ; fullRepresentationRingComputedIsFalse =
        refl
    ; enrichmentBoundary =
        "p2 tensor p5 character count is finite: Z/4 units times corrected Heegner Z/2 units"
        ∷ "The corrected p5 lane uses Z[(1+sqrt(-7))/2], giving Z/2 units for this receipt"
        ∷ "The product character count is 4 * 2 = 8"
        ∷ "This enrichment does not promote arbitrary tensor closure or a full representation ring"
        ∷ []
    }

record P3P5CharacterCountEnrichment : Set where
  field
    p3LaneUnits :
      String

    p3LaneUnitsAreZ6 :
      p3LaneUnits ≡ p3LaneUnitsZ6Label

    p3CharacterCount :
      Nat

    p3CharacterCountIsSix :
      p3CharacterCount ≡ 6

    p5HeegnerLaneUnits :
      String

    p5HeegnerLaneUnitsAreCorrectedZ2 :
      p5HeegnerLaneUnits ≡ p5CorrectedHeegnerLaneUnitsZ2Label

    p5HeegnerLaneCharacterCount :
      Nat

    p5HeegnerLaneCharacterCountIsTwo :
      p5HeegnerLaneCharacterCount ≡ 2

    p3p5ProductCharacterCount :
      Nat

    p3p5ProductCharacterCountIsProduct :
      p3p5ProductCharacterCount
      ≡
      p3CharacterCount * p5HeegnerLaneCharacterCount

    p3p5ProductCharacterCountIsTwelve :
      p3p5ProductCharacterCount ≡ 12

    p3p5ProductCharacterCountText :
      String

    p3p5ProductCharacterCountTextIsCanonical :
      p3p5ProductCharacterCountText ≡ p3p5ProductCharacterCountLabel

    p3p5FiniteAbelianCMCharacterBookkeeping :
      Bool

    p3p5FiniteAbelianCMCharacterBookkeepingIsTrue :
      p3p5FiniteAbelianCMCharacterBookkeeping ≡ true

    p3p5NonabelianSMReconstructionPromoted :
      Bool

    p3p5NonabelianSMReconstructionPromotedIsFalse :
      p3p5NonabelianSMReconstructionPromoted ≡ false

    p3p5ArbitraryDHRClosurePromoted :
      Bool

    p3p5ArbitraryDHRClosurePromotedIsFalse :
      p3p5ArbitraryDHRClosurePromoted ≡ false

    p3p5EnrichmentBoundary :
      List String

open P3P5CharacterCountEnrichment public

p3p5CharacterCountEnrichment :
  P3P5CharacterCountEnrichment
p3p5CharacterCountEnrichment =
  record
    { p3LaneUnits =
        p3LaneUnitsZ6Label
    ; p3LaneUnitsAreZ6 =
        refl
    ; p3CharacterCount =
        6
    ; p3CharacterCountIsSix =
        refl
    ; p5HeegnerLaneUnits =
        p5CorrectedHeegnerLaneUnitsZ2Label
    ; p5HeegnerLaneUnitsAreCorrectedZ2 =
        refl
    ; p5HeegnerLaneCharacterCount =
        2
    ; p5HeegnerLaneCharacterCountIsTwo =
        refl
    ; p3p5ProductCharacterCount =
        12
    ; p3p5ProductCharacterCountIsProduct =
        refl
    ; p3p5ProductCharacterCountIsTwelve =
        refl
    ; p3p5ProductCharacterCountText =
        p3p5ProductCharacterCountLabel
    ; p3p5ProductCharacterCountTextIsCanonical =
        refl
    ; p3p5FiniteAbelianCMCharacterBookkeeping =
        true
    ; p3p5FiniteAbelianCMCharacterBookkeepingIsTrue =
        refl
    ; p3p5NonabelianSMReconstructionPromoted =
        false
    ; p3p5NonabelianSMReconstructionPromotedIsFalse =
        refl
    ; p3p5ArbitraryDHRClosurePromoted =
        false
    ; p3p5ArbitraryDHRClosurePromotedIsFalse =
        refl
    ; p3p5EnrichmentBoundary =
        "p3 tensor p5 character count is finite abelian CM-character bookkeeping: Z/6 units times corrected Heegner Z/2 units"
        ∷ "The corrected p5 Heegner lane contributes Z/2 units for this receipt"
        ∷ "The product character count is 6 * 2 = 12"
        ∷ "This enrichment is not nonabelian Standard Model reconstruction and keeps arbitrary DHR closure false"
        ∷ []
    }

record FiniteTensorFusionRuleReceipt
  (pair : FiniteTensorFusionPair) :
  Set where
  field
    leftSector :
      FiniteTensorSector

    leftSectorIsCanonical :
      leftSector ≡ finiteTensorFusionLeft pair

    rightSector :
      FiniteTensorSector

    rightSectorIsCanonical :
      rightSector ≡ finiteTensorFusionRight pair

    leftRow :
      Ledger.FinitePrimeLaneSMRow

    leftRowIsCanonical :
      leftRow ≡ finiteTensorSectorRow leftSector

    rightRow :
      Ledger.FinitePrimeLaneSMRow

    rightRowIsCanonical :
      rightRow ≡ finiteTensorSectorRow rightSector

    fusionDimension :
      Nat

    fusionDimensionIsProduct :
      fusionDimension
      ≡
      finiteTensorSectorDimension leftSector
      *
      finiteTensorSectorDimension rightSector

    decomposition :
      List (FiniteTensorFusionProductSector pair)

    decompositionIsCanonical :
      decomposition ≡ canonicalFiniteTensorFusionDecomposition pair

    ruleLabel :
      String

    ruleLabelIsCanonical :
      ruleLabel ≡ finiteTensorFusionRuleLabel pair

    finiteDecompositionEnumerated :
      Bool

    finiteDecompositionEnumeratedIsTrue :
      finiteDecompositionEnumerated ≡ true

    finiteRuleComputableByCaseSplit :
      Bool

    finiteRuleComputableByCaseSplitIsTrue :
      finiteRuleComputableByCaseSplit ≡ true

    fullRepresentationRingComputed :
      Bool

    fullRepresentationRingComputedIsFalse :
      fullRepresentationRingComputed ≡ false

    arbitraryDHRClosurePromoted :
      Bool

    arbitraryDHRClosurePromotedIsFalse :
      arbitraryDHRClosurePromoted ≡ false

    ruleBoundary :
      List String

open FiniteTensorFusionRuleReceipt public

finiteTensorFusionRuleReceipt :
  (pair : FiniteTensorFusionPair) →
  FiniteTensorFusionRuleReceipt pair
finiteTensorFusionRuleReceipt pair =
  record
    { leftSector =
        finiteTensorFusionLeft pair
    ; leftSectorIsCanonical =
        refl
    ; rightSector =
        finiteTensorFusionRight pair
    ; rightSectorIsCanonical =
        refl
    ; leftRow =
        finiteTensorSectorRow (finiteTensorFusionLeft pair)
    ; leftRowIsCanonical =
        refl
    ; rightRow =
        finiteTensorSectorRow (finiteTensorFusionRight pair)
    ; rightRowIsCanonical =
        refl
    ; fusionDimension =
        finiteTensorFusionDimension pair
    ; fusionDimensionIsProduct =
        refl
    ; decomposition =
        canonicalFiniteTensorFusionDecomposition pair
    ; decompositionIsCanonical =
        refl
    ; ruleLabel =
        finiteTensorFusionRuleLabel pair
    ; ruleLabelIsCanonical =
        refl
    ; finiteDecompositionEnumerated =
        true
    ; finiteDecompositionEnumeratedIsTrue =
        refl
    ; finiteRuleComputableByCaseSplit =
        true
    ; finiteRuleComputableByCaseSplitIsTrue =
        refl
    ; fullRepresentationRingComputed =
        false
    ; fullRepresentationRingComputedIsFalse =
        refl
    ; arbitraryDHRClosurePromoted =
        false
    ; arbitraryDHRClosurePromotedIsFalse =
        refl
    ; ruleBoundary =
        "The finite tensor rule is a singleton external-product decomposition over the explicit prime-lane pair"
        ∷ "Computability is finite case-split computability over p2p3, p2p5, and p3p5 only"
        ∷ "No arbitrary DHR tensor closure, full representation-ring computation, DR reconstruction, or Standard Model match is promoted"
        ∷ []
    }

p2p3FiniteTensorFusionRuleReceipt :
  FiniteTensorFusionRuleReceipt p2p3TensorFusionPair
p2p3FiniteTensorFusionRuleReceipt =
  finiteTensorFusionRuleReceipt p2p3TensorFusionPair

p2p5FiniteTensorFusionRuleReceipt :
  FiniteTensorFusionRuleReceipt p2p5TensorFusionPair
p2p5FiniteTensorFusionRuleReceipt =
  finiteTensorFusionRuleReceipt p2p5TensorFusionPair

p3p5FiniteTensorFusionRuleReceipt :
  FiniteTensorFusionRuleReceipt p3p5TensorFusionPair
p3p5FiniteTensorFusionRuleReceipt =
  finiteTensorFusionRuleReceipt p3p5TensorFusionPair

record FinitePrimeLaneTensorFusionReceipt : Set where
  field
    p2p3Rule :
      FiniteTensorFusionRuleReceipt p2p3TensorFusionPair

    p2p3RuleIsCanonical :
      Bool

    p2p3RuleIsCanonicalIsTrue :
      p2p3RuleIsCanonical ≡ true

    p2p3CharacterCount :
      P2P3CharacterCountEnrichment

    p2p3CharacterCountIsCanonical :
      p2p3CharacterCount ≡ p2p3CharacterCountEnrichment

    p2p3ProductCharacterCountIsTwentyFour :
      p2p3ProductCharacterCount p2p3CharacterCount ≡ 24

    p2p5Rule :
      FiniteTensorFusionRuleReceipt p2p5TensorFusionPair

    p2p5RuleIsCanonical :
      Bool

    p2p5RuleIsCanonicalIsTrue :
      p2p5RuleIsCanonical ≡ true

    p2p5CharacterCount :
      P2P5CharacterCountEnrichment

    p2p5CharacterCountIsCanonical :
      p2p5CharacterCount ≡ p2p5CharacterCountEnrichment

    p2p5ProductCharacterCountIsEight :
      productCharacterCount p2p5CharacterCount ≡ 8

    p3p5Rule :
      FiniteTensorFusionRuleReceipt p3p5TensorFusionPair

    p3p5RuleIsCanonical :
      Bool

    p3p5RuleIsCanonicalIsTrue :
      p3p5RuleIsCanonical ≡ true

    p3p5CharacterCount :
      P3P5CharacterCountEnrichment

    p3p5CharacterCountIsCanonical :
      p3p5CharacterCount ≡ p3p5CharacterCountEnrichment

    p3p5ProductCharacterCountIsTwelve :
      P3P5CharacterCountEnrichment.p3p5ProductCharacterCount
        p3p5CharacterCount
      ≡
      12

    p3p5CharacterCountIsFiniteAbelianCMBookkeeping :
      p3p5FiniteAbelianCMCharacterBookkeeping p3p5CharacterCount
      ≡
      true

    p3p5CharacterCountDoesNotPromoteNonabelianSMReconstruction :
      p3p5NonabelianSMReconstructionPromoted p3p5CharacterCount
      ≡
      false

    p3p5CharacterCountKeepsArbitraryDHRClosureFalse :
      p3p5ArbitraryDHRClosurePromoted p3p5CharacterCount
      ≡
      false

    finitePairRules :
      List FiniteTensorFusionPair

    finitePairRulesAreCanonical :
      finitePairRules
      ≡
      p2p3TensorFusionPair
      ∷ p2p5TensorFusionPair
      ∷ p3p5TensorFusionPair
      ∷ []

    allFinitePairRulesComputed :
      Bool

    allFinitePairRulesComputedIsTrue :
      allFinitePairRulesComputed ≡ true

    fullTensorCategoryConstructed :
      Bool

    fullTensorCategoryConstructedIsFalse :
      fullTensorCategoryConstructed ≡ false

    arbitrarySectorTensorClosurePromoted :
      Bool

    arbitrarySectorTensorClosurePromotedIsFalse :
      arbitrarySectorTensorClosurePromoted ≡ false

    receiptBoundary :
      List String

open FinitePrimeLaneTensorFusionReceipt public

canonicalFinitePrimeLaneTensorFusionReceipt :
  FinitePrimeLaneTensorFusionReceipt
canonicalFinitePrimeLaneTensorFusionReceipt =
  record
    { p2p3Rule =
        p2p3FiniteTensorFusionRuleReceipt
    ; p2p3RuleIsCanonical =
        true
    ; p2p3RuleIsCanonicalIsTrue =
        refl
    ; p2p3CharacterCount =
        p2p3CharacterCountEnrichment
    ; p2p3CharacterCountIsCanonical =
        refl
    ; p2p3ProductCharacterCountIsTwentyFour =
        refl
    ; p2p5Rule =
        p2p5FiniteTensorFusionRuleReceipt
    ; p2p5RuleIsCanonical =
        true
    ; p2p5RuleIsCanonicalIsTrue =
        refl
    ; p2p5CharacterCount =
        p2p5CharacterCountEnrichment
    ; p2p5CharacterCountIsCanonical =
        refl
    ; p2p5ProductCharacterCountIsEight =
        refl
    ; p3p5Rule =
        p3p5FiniteTensorFusionRuleReceipt
    ; p3p5RuleIsCanonical =
        true
    ; p3p5RuleIsCanonicalIsTrue =
        refl
    ; p3p5CharacterCount =
        p3p5CharacterCountEnrichment
    ; p3p5CharacterCountIsCanonical =
        refl
    ; p3p5ProductCharacterCountIsTwelve =
        refl
    ; p3p5CharacterCountIsFiniteAbelianCMBookkeeping =
        refl
    ; p3p5CharacterCountDoesNotPromoteNonabelianSMReconstruction =
        refl
    ; p3p5CharacterCountKeepsArbitraryDHRClosureFalse =
        refl
    ; finitePairRules =
        p2p3TensorFusionPair
        ∷ p2p5TensorFusionPair
        ∷ p3p5TensorFusionPair
        ∷ []
    ; finitePairRulesAreCanonical =
        refl
    ; allFinitePairRulesComputed =
        true
    ; allFinitePairRulesComputedIsTrue =
        refl
    ; fullTensorCategoryConstructed =
        false
    ; fullTensorCategoryConstructedIsFalse =
        refl
    ; arbitrarySectorTensorClosurePromoted =
        false
    ; arbitrarySectorTensorClosurePromotedIsFalse =
        refl
    ; receiptBoundary =
        "Finite p2p3, p2p5, and p3p5 tensor-fusion rules are enumerated as singleton external-product decompositions"
        ∷ "The p2p3 rule records character-count enrichment: End(E_p2 x E_p3) CM unit-character product Z/4 x Z/6 gives 24 characters"
        ∷ "The p2p5 rule records character-count enrichment: p2 Z/4 units times corrected p5 Heegner Z/2 units gives 8 characters"
        ∷ "The p3p5 rule records character-count enrichment: p3 Z/6 units times corrected p5 Heegner Z/2 units gives 12 characters"
        ∷ "The p3p5 enrichment is finite abelian CM-character bookkeeping, not nonabelian Standard Model reconstruction"
        ∷ "The rules are computable by finite case split over the three explicit prime-lane pairs"
        ∷ "This receipt does not construct arbitrary-sector tensor closure, a full tensor C-star category, a representation ring, or G_DHR ~= G_SM"
        ∷ []
    }

finitePrimeLaneTensorFusionRulesComputed :
  allFinitePairRulesComputed canonicalFinitePrimeLaneTensorFusionReceipt
  ≡
  true
finitePrimeLaneTensorFusionRulesComputed =
  refl

finitePrimeLaneTensorFusionDoesNotPromoteArbitraryClosure :
  arbitrarySectorTensorClosurePromoted canonicalFinitePrimeLaneTensorFusionReceipt
  ≡
  false
finitePrimeLaneTensorFusionDoesNotPromoteArbitraryClosure =
  refl

p3p5FinitePrimeLaneProductCharacterCountIsTwelve :
  P3P5CharacterCountEnrichment.p3p5ProductCharacterCount
    p3p5CharacterCountEnrichment
  ≡
  12
p3p5FinitePrimeLaneProductCharacterCountIsTwelve =
  refl

p3p5FinitePrimeLaneCharacterCountIsFiniteAbelianCMBookkeeping :
  p3p5FiniteAbelianCMCharacterBookkeeping p3p5CharacterCountEnrichment
  ≡
  true
p3p5FinitePrimeLaneCharacterCountIsFiniteAbelianCMBookkeeping =
  refl

p3p5FinitePrimeLaneCharacterCountDoesNotPromoteNonabelianSM :
  p3p5NonabelianSMReconstructionPromoted p3p5CharacterCountEnrichment
  ≡
  false
p3p5FinitePrimeLaneCharacterCountDoesNotPromoteNonabelianSM =
  refl

p3p5FinitePrimeLaneCharacterCountKeepsArbitraryDHRClosureFalse :
  p3p5ArbitraryDHRClosurePromoted p3p5CharacterCountEnrichment
  ≡
  false
p3p5FinitePrimeLaneCharacterCountKeepsArbitraryDHRClosureFalse =
  refl
