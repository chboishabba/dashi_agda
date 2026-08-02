module DASHI.Foundations.UBP.MOGGolayCharacterisationBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources
import DASHI.Foundations.UBP.ExternalRepositoryProvenance as Provenance

------------------------------------------------------------------------
-- MOG / Hexacode / Golay characterisation boundary.
--
-- A zero-failure check over the 4096 Golay words proves only the forward
-- inclusion into the selected Hexacode shadow preimage.  A complete reverse
-- characterisation must also carry the column/tetrad parity and global parity
-- conditions for the chosen MOG convention.
------------------------------------------------------------------------

record MOGGolayPredicates : Set₁ where
  field
    Binary24Word : Set
    GolayMembership : Binary24Word → Set
    HexacodeShadow : Binary24Word → Set
    ColumnParityEven : Binary24Word → Set
    GlobalParityEven : Binary24Word → Set

open MOGGolayPredicates public

record MOGGolayCharacterisation
    (surface : MOGGolayPredicates) : Set₁ where
  field
    golayImpliesShadow :
      (word : Binary24Word surface) →
      GolayMembership surface word →
      HexacodeShadow surface word
    golayImpliesColumnParity :
      (word : Binary24Word surface) →
      GolayMembership surface word →
      ColumnParityEven surface word
    golayImpliesGlobalParity :
      (word : Binary24Word surface) →
      GolayMembership surface word →
      GlobalParityEven surface word
    shadowParitySuffices :
      (word : Binary24Word surface) →
      HexacodeShadow surface word →
      ColumnParityEven surface word →
      GlobalParityEven surface word →
      GolayMembership surface word
    selectedMOGConvention : String
    sourceAuthor : String
    sourceTitle : String
    sourceDOI : String

open MOGGolayCharacterisation public

shadowPreimageCount : Nat
shadowPreimageCount = 262144

golayWordCount : Nat
golayWordCount = 4096

missingFibreFactor : Nat
missingFibreFactor = 64

shadowCountFactorisation :
  missingFibreFactor * golayWordCount ≡ shadowPreimageCount
shadowCountFactorisation = refl

record MOGCharacterisationStatus : Set where
  constructor mogCharacterisationStatus
  field
    repositoryURL : String
    repositoryAuthor : String
    implementationPath : String
    forwardContainmentExhaustivelyChecked : Bool
    forwardContainmentExhaustivelyCheckedIsTrue :
      forwardContainmentExhaustivelyChecked ≡ true
    reverseCharacterisationMachineCheckedHere : Bool
    reverseCharacterisationMachineCheckedHereIsFalse :
      reverseCharacterisationMachineCheckedHere ≡ false
    columnParityObligationExplicit : Bool
    columnParityObligationExplicitIsTrue :
      columnParityObligationExplicit ≡ true
    globalParityObligationExplicit : Bool
    globalParityObligationExplicitIsTrue :
      globalParityObligationExplicit ≡ true
    shadowAloneDefinesGolay : Bool
    shadowAloneDefinesGolayIsFalse : shadowAloneDefinesGolay ≡ false
    cardinalityGapChecked : Bool
    cardinalityGapCheckedIsTrue : cardinalityGapChecked ≡ true
    reading : String

open MOGCharacterisationStatus public

canonicalMOGCharacterisationStatus : MOGCharacterisationStatus
canonicalMOGCharacterisationStatus =
  mogCharacterisationStatus
    Provenance.ubpRepositoryURL
    Provenance.ubpAuthorName
    "core_studio_v4.0/core/tgic_v3.py"
    true refl
    false refl
    true refl
    true refl
    false refl
    true refl
    "Hexacode shadow, column parity, and global parity are separate predicates; sufficiency requires an explicit Curtis/MOG theorem receipt"

mogCharacterisationReceipt : GenericReceipt.GenericReceipt
mogCharacterisationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "MOG Golay characterisation boundary"
    "DASHI.Foundations.UBP.MOGGolayCharacterisationBoundary"
    "canonicalMOGCharacterisationStatus"
    "the forward shadow inclusion, column-parity obligation, global-parity obligation, reverse-characterisation interface, and 64-to-1 cardinality seam are explicit"
    "the selected MOG convention and necessary-and-sufficient theorem require a named external proof import"
    "agda -i . DASHI/Foundations/UBP/MOGGolayCharacterisationBoundary.agda"

mogCharacterisationReceiptNonPromoting :
  GenericReceipt.promotesClaim mogCharacterisationReceipt ≡ false
mogCharacterisationReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse mogCharacterisationReceipt
