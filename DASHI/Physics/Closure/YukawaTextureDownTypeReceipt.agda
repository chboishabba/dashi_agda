module DASHI.Physics.Closure.YukawaTextureDownTypeReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Down-type Yukawa texture receipt.
--
-- This records the requested Froggatt-Nielsen-style down-sector texture.
-- It is a diagnostic/structure receipt only: no physical Yukawa eigenbasis,
-- CKM promotion, terminal physics claim, or Clay claim is constructed here.

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

data DownTypeYukawaTextureStatus : Set where
  downTypeTextureRecordedWithDistinctDepthSeparations :
    DownTypeYukawaTextureStatus

data DownTypeYukawaTextureFlag : Set where
  FNWithAlphaDAndAlphaD23 :
    DownTypeYukawaTextureFlag

data DownTypeDepthSymbol : Set where
  alphaD :
    DownTypeDepthSymbol

  alpha1 :
    DownTypeDepthSymbol

  alphaD23 :
    DownTypeDepthSymbol

  alpha2 :
    DownTypeDepthSymbol

alphaDNotAlpha1 :
  alphaD ≢ alpha1
alphaDNotAlpha1 ()

alphaD23NotAlpha2 :
  alphaD23 ≢ alpha2
alphaD23NotAlpha2 ()

data DownTypeYukawaTextureBlocker : Set where
  missingCertifiedDownTypeMassAuthority :
    DownTypeYukawaTextureBlocker

  missingPhysicalYukawaDiagonalisation :
    DownTypeYukawaTextureBlocker

  missingCKMExtractionAuthority :
    DownTypeYukawaTextureBlocker

canonicalDownTypeYukawaTextureBlockers :
  List DownTypeYukawaTextureBlocker
canonicalDownTypeYukawaTextureBlockers =
  missingCertifiedDownTypeMassAuthority
  ∷ missingPhysicalYukawaDiagonalisation
  ∷ missingCKMExtractionAuthority
  ∷ []

data DownTypeYukawaTexturePromotion : Set where

downTypeYukawaTexturePromotionImpossibleHere :
  DownTypeYukawaTexturePromotion →
  ⊥
downTypeYukawaTexturePromotionImpossibleHere ()

downTypeTextureMatrixLabel : String
downTypeTextureMatrixLabel =
  "[[alphaD^2, alphaD, alphaD*alphaD23],[alphaD,1,alphaD23],[alphaD*alphaD23,alphaD23,1]]"

downTypeAlphaDLabel : String
downTypeAlphaDLabel =
  "alphaD=lambda=0.2242"

downTypeAlphaD23Label : String
downTypeAlphaD23Label =
  "alphaD23=sqrt(m_s/m_b)=0.1496"

record YukawaTextureDownTypeReceipt : Set where
  field
    status :
      DownTypeYukawaTextureStatus

    downTypeYukawaTexture :
      DownTypeYukawaTextureFlag

    downTypeYukawaTextureIsFNWithAlphaDAndAlphaD23 :
      downTypeYukawaTexture ≡ FNWithAlphaDAndAlphaD23

    textureLabel :
      String

    textureLabelIsCanonical :
      textureLabel ≡ downTypeTextureMatrixLabel

    alphaDValue :
      Float

    alphaDFormula :
      String

    alphaDFormulaIsCanonical :
      alphaDFormula ≡ downTypeAlphaDLabel

    alphaD23Value :
      Float

    alphaD23Formula :
      String

    alphaD23FormulaIsCanonical :
      alphaD23Formula ≡ downTypeAlphaD23Label

    alphaDIsNotAlpha1 :
      alphaD ≢ alpha1

    alphaD23IsNotAlpha2 :
      alphaD23 ≢ alpha2

    downSectorHasDistinctDepthSeparations :
      Bool

    downSectorHasDistinctDepthSeparationsIsTrue :
      downSectorHasDistinctDepthSeparations ≡ true

    downTypeHierarchyDistinctFromUpType :
      Bool

    downTypeHierarchyDistinctFromUpTypeIsTrue :
      downTypeHierarchyDistinctFromUpType ≡ true

    physicalDownTypeYukawaPromoted :
      Bool

    physicalDownTypeYukawaPromotedIsFalse :
      physicalDownTypeYukawaPromoted ≡ false

    physicalYukawaEigenbasisPromoted :
      Bool

    physicalYukawaEigenbasisPromotedIsFalse :
      physicalYukawaEigenbasisPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    blockers :
      List DownTypeYukawaTextureBlocker

    blockersAreCanonical :
      blockers ≡ canonicalDownTypeYukawaTextureBlockers

    promotionFlags :
      List DownTypeYukawaTexturePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YukawaTextureDownTypeReceipt public

canonicalYukawaTextureDownTypeReceipt :
  YukawaTextureDownTypeReceipt
canonicalYukawaTextureDownTypeReceipt =
  record
    { status =
        downTypeTextureRecordedWithDistinctDepthSeparations
    ; downTypeYukawaTexture =
        FNWithAlphaDAndAlphaD23
    ; downTypeYukawaTextureIsFNWithAlphaDAndAlphaD23 =
        refl
    ; textureLabel =
        downTypeTextureMatrixLabel
    ; textureLabelIsCanonical =
        refl
    ; alphaDValue =
        0.2242
    ; alphaDFormula =
        downTypeAlphaDLabel
    ; alphaDFormulaIsCanonical =
        refl
    ; alphaD23Value =
        0.1496
    ; alphaD23Formula =
        downTypeAlphaD23Label
    ; alphaD23FormulaIsCanonical =
        refl
    ; alphaDIsNotAlpha1 =
        alphaDNotAlpha1
    ; alphaD23IsNotAlpha2 =
        alphaD23NotAlpha2
    ; downSectorHasDistinctDepthSeparations =
        true
    ; downSectorHasDistinctDepthSeparationsIsTrue =
        refl
    ; downTypeHierarchyDistinctFromUpType =
        true
    ; downTypeHierarchyDistinctFromUpTypeIsTrue =
        refl
    ; physicalDownTypeYukawaPromoted =
        false
    ; physicalDownTypeYukawaPromotedIsFalse =
        refl
    ; physicalYukawaEigenbasisPromoted =
        false
    ; physicalYukawaEigenbasisPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; blockers =
        canonicalDownTypeYukawaTextureBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The down-type texture is recorded with alphaD=lambda=0.2242 and alphaD23=sqrt(m_s/m_b)=0.1496"
        ∷ "The alphaD and alphaD23 symbols are kept distinct from alpha1 and alpha2, giving down-sector depth separations distinct from the up-type hierarchy"
        ∷ "This receipt records structure only and promotes no physical down-type Yukawa, Yukawa eigenbasis, CKM, terminal, or Clay claim"
        ∷ []
    }

downTypeTextureFlagIsFN :
  downTypeYukawaTexture canonicalYukawaTextureDownTypeReceipt
  ≡
  FNWithAlphaDAndAlphaD23
downTypeTextureFlagIsFN =
  refl

downTypeHierarchyIsDistinctFromUpType :
  downTypeHierarchyDistinctFromUpType canonicalYukawaTextureDownTypeReceipt
  ≡
  true
downTypeHierarchyIsDistinctFromUpType =
  refl

downTypeTexturePromotesNoCKM :
  physicalCKMPromoted canonicalYukawaTextureDownTypeReceipt ≡ false
downTypeTexturePromotesNoCKM =
  refl

downTypeTexturePromotionFlagsEmpty :
  promotionFlags canonicalYukawaTextureDownTypeReceipt ≡ []
downTypeTexturePromotionFlagsEmpty =
  refl
