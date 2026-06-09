module DASHI.Physics.Closure.YukawaTextureUpTypeReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Up-type Yukawa two-alpha texture receipt.
--
-- This receipt records the Froggatt-Nielsen-style two-alpha texture implied
-- by alpha1/alpha2.  It is a texture diagnostic only: it records inhabited
-- off-diagonal entries, but does not promote a physical eigenbasis, CKM
-- authority, terminal claim, or Clay claim.

data YukawaTextureUpTypeStatus : Set where
  upTypeTwoAlphaTextureRecorded :
    YukawaTextureUpTypeStatus

data UpTypeYukawaTexture : Set where
  FNWithTwoAlphas :
    UpTypeYukawaTexture

data YukawaTextureUpTypePromotion : Set where

yukawaTextureUpTypePromotionImpossibleHere :
  YukawaTextureUpTypePromotion →
  ⊥
yukawaTextureUpTypePromotionImpossibleHere ()

upTypeHierarchyLabel : String
upTypeHierarchyLabel =
  "m_u:m_c:m_t = alpha1^2:1:1/alpha2^2"

twoAlphaTextureMatrixLabel : String
twoAlphaTextureMatrixLabel =
  "[[alpha1^2, alpha1, alpha1*alpha2],[alpha1,1,alpha2],[alpha1*alpha2,alpha2,1]]"

upTypeDiagonalNoteLabel : String
upTypeDiagonalNoteLabel =
  "diag(0.0017,1,136) up to normalisation"

record YukawaTextureUpTypeReceipt : Set where
  field
    status :
      YukawaTextureUpTypeStatus

    alpha1Symbol :
      String

    alpha2Symbol :
      String

    hierarchy :
      String

    hierarchyIsCanonical :
      hierarchy ≡ upTypeHierarchyLabel

    textureMatrixLabel :
      String

    textureMatrixLabelIsCanonical :
      textureMatrixLabel ≡ twoAlphaTextureMatrixLabel

    y12 :
      Float

    y23 :
      Float

    y13 :
      Float

    diagonalNormalisationNote :
      String

    diagonalNormalisationNoteIsCanonical :
      diagonalNormalisationNote ≡ upTypeDiagonalNoteLabel

    upTypeYukawaTexture :
      UpTypeYukawaTexture

    upTypeYukawaTextureIsFNWithTwoAlphas :
      upTypeYukawaTexture ≡ FNWithTwoAlphas

    offDiagonalEntriesInhabited :
      Bool

    offDiagonalEntriesInhabitedIsTrue :
      offDiagonalEntriesInhabited ≡ true

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

    promotionFlags :
      List YukawaTextureUpTypePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YukawaTextureUpTypeReceipt public

canonicalYukawaTextureUpTypeReceipt :
  YukawaTextureUpTypeReceipt
canonicalYukawaTextureUpTypeReceipt =
  record
    { status =
        upTypeTwoAlphaTextureRecorded
    ; alpha1Symbol =
        "alpha1"
    ; alpha2Symbol =
        "alpha2"
    ; hierarchy =
        upTypeHierarchyLabel
    ; hierarchyIsCanonical =
        refl
    ; textureMatrixLabel =
        twoAlphaTextureMatrixLabel
    ; textureMatrixLabelIsCanonical =
        refl
    ; y12 =
        0.0412
    ; y23 =
        0.0858
    ; y13 =
        0.00354
    ; diagonalNormalisationNote =
        upTypeDiagonalNoteLabel
    ; diagonalNormalisationNoteIsCanonical =
        refl
    ; upTypeYukawaTexture =
        FNWithTwoAlphas
    ; upTypeYukawaTextureIsFNWithTwoAlphas =
        refl
    ; offDiagonalEntriesInhabited =
        true
    ; offDiagonalEntriesInhabitedIsTrue =
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
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The up-type two-alpha Froggatt-Nielsen texture is recorded from alpha1/alpha2"
        ∷ "Numerical off-diagonal entries y12=0.0412, y23=0.0858, y13=0.00354 are inhabited diagnostics"
        ∷ "The diagonal note is diag(0.0017,1,136) up to normalisation"
        ∷ "No physical eigenbasis, CKM, terminal, or Clay promotion is asserted"
        ∷ []
    }

upTypeYukawaTextureFlagIsFNWithTwoAlphas :
  upTypeYukawaTexture canonicalYukawaTextureUpTypeReceipt
  ≡
  FNWithTwoAlphas
upTypeYukawaTextureFlagIsFNWithTwoAlphas =
  refl

upTypeYukawaTextureOffDiagonalEntriesInhabited :
  offDiagonalEntriesInhabited canonicalYukawaTextureUpTypeReceipt
  ≡
  true
upTypeYukawaTextureOffDiagonalEntriesInhabited =
  refl

upTypeYukawaTextureDoesNotPromoteCKM :
  physicalCKMPromoted canonicalYukawaTextureUpTypeReceipt
  ≡
  false
upTypeYukawaTextureDoesNotPromoteCKM =
  refl
