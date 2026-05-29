module DASHI.Physics.QFT.ArbitrarySectorExtensionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Arbitrary-sector extension receipt.
--
-- This receipt identifies the remaining non-abelian gap after the finite
-- CM-character reconstruction surface is recorded.  The finite readback
-- Z/4 x Z/6 x Z/2 has character surface 48, but that abelian surface is not
-- the non-abelian Standard Model gauge group.  Exact G_DHR ~= G_SM still
-- requires arbitrary-sector closure, non-abelian braiding/intertwiner
-- structure, continuum passage, and DR authority consumption.

data FiniteCMCharacterFactor : Set where
  cmCharacterZ4 :
    FiniteCMCharacterFactor

  cmCharacterZ6 :
    FiniteCMCharacterFactor

  cmCharacterZ2 :
    FiniteCMCharacterFactor

canonicalFiniteCMCharacterFactors :
  List FiniteCMCharacterFactor
canonicalFiniteCMCharacterFactors =
  cmCharacterZ4
  ∷ cmCharacterZ6
  ∷ cmCharacterZ2
  ∷ []

data ArbitrarySectorExtensionBlocker : Set where
  finiteCMCharacterSurfaceOnlyAbelian :
    ArbitrarySectorExtensionBlocker

  missingArbitrarySectorClosure :
    ArbitrarySectorExtensionBlocker

  missingNonabelianBraidingIntertwinerStructure :
    ArbitrarySectorExtensionBlocker

  missingContinuumDHRNetAuthorityConsumption :
    ArbitrarySectorExtensionBlocker

  missingExactStandardModelGaugeGroupIdentification :
    ArbitrarySectorExtensionBlocker

canonicalArbitrarySectorExtensionBlockers :
  List ArbitrarySectorExtensionBlocker
canonicalArbitrarySectorExtensionBlockers =
  finiteCMCharacterSurfaceOnlyAbelian
  ∷ missingArbitrarySectorClosure
  ∷ missingNonabelianBraidingIntertwinerStructure
  ∷ missingContinuumDHRNetAuthorityConsumption
  ∷ missingExactStandardModelGaugeGroupIdentification
  ∷ []

finiteCMCharacterGroupLabel : String
finiteCMCharacterGroupLabel =
  "finite abelian CM-character reconstruction group: Z/4 x Z/6 x Z/2"

finiteCMCharacterSurfaceLabel : String
finiteCMCharacterSurfaceLabel =
  "finite abelian CM-character surface cardinality: 4 * 6 * 2 = 48"

nonabelianGapLabel : String
nonabelianGapLabel =
  "Z/4 x Z/6 x Z/2 character surface 48 is abelian bookkeeping, not the non-abelian Standard Model gauge group"

extensionTargetLabel : String
extensionTargetLabel =
  "exact G_DHR ~= G_SM requires arbitrary-sector closure, non-abelian braiding/intertwiner structure, continuum DHR net authority, and DR reconstruction authority"

record ArbitrarySectorExtensionReceipt : Setω where
  field
    finiteCMCharacterFactors :
      List FiniteCMCharacterFactor

    finiteCMCharacterFactorsAreCanonical :
      finiteCMCharacterFactors ≡ canonicalFiniteCMCharacterFactors

    z4FactorOrder :
      Nat

    z4FactorOrderIsFour :
      z4FactorOrder ≡ 4

    z6FactorOrder :
      Nat

    z6FactorOrderIsSix :
      z6FactorOrder ≡ 6

    z2FactorOrder :
      Nat

    z2FactorOrderIsTwo :
      z2FactorOrder ≡ 2

    finiteCharacterSurfaceCardinality :
      Nat

    finiteCharacterSurfaceCardinalityIsFortyEight :
      finiteCharacterSurfaceCardinality ≡ 48

    finiteCharacterSurfaceCardinalityIsProduct :
      finiteCharacterSurfaceCardinality ≡ z4FactorOrder * z6FactorOrder * z2FactorOrder

    finiteCMCharacterGroup :
      String

    finiteCMCharacterGroupIsCanonical :
      finiteCMCharacterGroup ≡ finiteCMCharacterGroupLabel

    finiteCMCharacterSurface :
      String

    finiteCMCharacterSurfaceIsCanonical :
      finiteCMCharacterSurface ≡ finiteCMCharacterSurfaceLabel

    finiteGapIdentified :
      Bool

    finiteGapIdentifiedIsTrue :
      finiteGapIdentified ≡ true

    finiteCMCharacterSurfaceIsAbelian :
      Bool

    finiteCMCharacterSurfaceIsAbelianIsTrue :
      finiteCMCharacterSurfaceIsAbelian ≡ true

    finiteCMCharacterSurfaceIsNonabelianSMGauge :
      Bool

    finiteCMCharacterSurfaceIsNonabelianSMGaugeIsFalse :
      finiteCMCharacterSurfaceIsNonabelianSMGauge ≡ false

    nonabelianGap :
      String

    nonabelianGapIsCanonical :
      nonabelianGap ≡ nonabelianGapLabel

    arbitrarySectorExtensionConstructed :
      Bool

    arbitrarySectorExtensionConstructedIsFalse :
      arbitrarySectorExtensionConstructed ≡ false

    arbitrarySectorClosureAvailableForExtension :
      Bool

    arbitrarySectorClosureAvailableForExtensionIsFalse :
      arbitrarySectorClosureAvailableForExtension ≡ false

    nonabelianBraidingIntertwinersConstructed :
      Bool

    nonabelianBraidingIntertwinersConstructedIsFalse :
      nonabelianBraidingIntertwinersConstructed ≡ false

    continuumDHRNetAuthorityConsumed :
      Bool

    continuumDHRNetAuthorityConsumedIsFalse :
      continuumDHRNetAuthorityConsumed ≡ false

    doplicherRobertsAuthorityConsumed :
      Bool

    doplicherRobertsAuthorityConsumedIsFalse :
      doplicherRobertsAuthorityConsumed ≡ false

    fullGSMGaugePromotion :
      Bool

    fullGSMGaugePromotionIsFalse :
      fullGSMGaugePromotion ≡ false

    extensionTarget :
      String

    extensionTargetIsCanonical :
      extensionTarget ≡ extensionTargetLabel

    blockers :
      List ArbitrarySectorExtensionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalArbitrarySectorExtensionBlockers

    receiptBoundary :
      List String

open ArbitrarySectorExtensionReceipt public

canonicalArbitrarySectorExtensionReceipt :
  ArbitrarySectorExtensionReceipt
canonicalArbitrarySectorExtensionReceipt =
  record
    { finiteCMCharacterFactors =
        canonicalFiniteCMCharacterFactors
    ; finiteCMCharacterFactorsAreCanonical =
        refl
    ; z4FactorOrder =
        4
    ; z4FactorOrderIsFour =
        refl
    ; z6FactorOrder =
        6
    ; z6FactorOrderIsSix =
        refl
    ; z2FactorOrder =
        2
    ; z2FactorOrderIsTwo =
        refl
    ; finiteCharacterSurfaceCardinality =
        48
    ; finiteCharacterSurfaceCardinalityIsFortyEight =
        refl
    ; finiteCharacterSurfaceCardinalityIsProduct =
        refl
    ; finiteCMCharacterGroup =
        finiteCMCharacterGroupLabel
    ; finiteCMCharacterGroupIsCanonical =
        refl
    ; finiteCMCharacterSurface =
        finiteCMCharacterSurfaceLabel
    ; finiteCMCharacterSurfaceIsCanonical =
        refl
    ; finiteGapIdentified =
        true
    ; finiteGapIdentifiedIsTrue =
        refl
    ; finiteCMCharacterSurfaceIsAbelian =
        true
    ; finiteCMCharacterSurfaceIsAbelianIsTrue =
        refl
    ; finiteCMCharacterSurfaceIsNonabelianSMGauge =
        false
    ; finiteCMCharacterSurfaceIsNonabelianSMGaugeIsFalse =
        refl
    ; nonabelianGap =
        nonabelianGapLabel
    ; nonabelianGapIsCanonical =
        refl
    ; arbitrarySectorExtensionConstructed =
        false
    ; arbitrarySectorExtensionConstructedIsFalse =
        refl
    ; arbitrarySectorClosureAvailableForExtension =
        false
    ; arbitrarySectorClosureAvailableForExtensionIsFalse =
        refl
    ; nonabelianBraidingIntertwinersConstructed =
        false
    ; nonabelianBraidingIntertwinersConstructedIsFalse =
        refl
    ; continuumDHRNetAuthorityConsumed =
        false
    ; continuumDHRNetAuthorityConsumedIsFalse =
        refl
    ; doplicherRobertsAuthorityConsumed =
        false
    ; doplicherRobertsAuthorityConsumedIsFalse =
        refl
    ; fullGSMGaugePromotion =
        false
    ; fullGSMGaugePromotionIsFalse =
        refl
    ; extensionTarget =
        extensionTargetLabel
    ; extensionTargetIsCanonical =
        refl
    ; blockers =
        canonicalArbitrarySectorExtensionBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "Finite abelian CM-character reconstruction is identified as Z/4 x Z/6 x Z/2 with surface cardinality 48"
        ∷ "finiteGapIdentified is true only for the gap statement: this abelian character surface is not the non-abelian Standard Model gauge group"
        ∷ "Arbitrary-sector extension, non-abelian braiding/intertwiner structure, continuum DHR net authority, and DR authority consumption remain false"
        ∷ "The receipt does not consume arbitrary-sector closure and does not promote G_DHR ~= G_SM"
        ∷ []
    }

arbitrarySectorExtensionFiniteGapIdentified :
  finiteGapIdentified canonicalArbitrarySectorExtensionReceipt
  ≡
  true
arbitrarySectorExtensionFiniteGapIdentified =
  refl

arbitrarySectorExtensionKeepsExtensionFalse :
  arbitrarySectorExtensionConstructed canonicalArbitrarySectorExtensionReceipt
  ≡
  false
arbitrarySectorExtensionKeepsExtensionFalse =
  refl

arbitrarySectorExtensionKeepsFullGSMFalse :
  fullGSMGaugePromotion canonicalArbitrarySectorExtensionReceipt
  ≡
  false
arbitrarySectorExtensionKeepsFullGSMFalse =
  refl

arbitrarySectorExtensionKeepsArbitraryClosureFalse :
  arbitrarySectorClosureAvailableForExtension
    canonicalArbitrarySectorExtensionReceipt
  ≡
  false
arbitrarySectorExtensionKeepsArbitraryClosureFalse =
  refl
