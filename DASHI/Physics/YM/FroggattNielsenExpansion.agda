module DASHI.Physics.YM.FroggattNielsenExpansion where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter

record FNChargeAssignment : Set where
  field
    qQ1 qQ2 qQ3 : ℤ
    qU1 qU2 qU3 : ℤ
    qD1 qD2 qD3 : ℤ
    qH : ℤ

open FNChargeAssignment public

record FNSuppressionTexture : Set where
  field
    ckm11 ckm12 ckm13 : ℤ
    ckm21 ckm22 ckm23 : ℤ
    ckm31 ckm32 ckm33 : ℤ
    up11 up12 up13 : ℤ
    up21 up22 up23 : ℤ
    up31 up32 up33 : ℤ
    down11 down12 down13 : ℤ
    down21 down22 down23 : ℤ
    down31 down32 down33 : ℤ

open FNSuppressionTexture public

canonicalFNChargeAssignment : FNChargeAssignment
canonicalFNChargeAssignment = record
  { qQ1 = + 3
  ; qQ2 = + 2
  ; qQ3 = + 0
  ; qU1 = + 3
  ; qU2 = + 2
  ; qU3 = + 0
  ; qD1 = + 3
  ; qD2 = + 2
  ; qD3 = + 0
  ; qH = + 0
  }

canonicalFNSuppressionTexture : FNSuppressionTexture
canonicalFNSuppressionTexture = record
  { ckm11 = + 0
  ; ckm12 = + 1
  ; ckm13 = + 3
  ; ckm21 = + 1
  ; ckm22 = + 0
  ; ckm23 = + 2
  ; ckm31 = + 3
  ; ckm32 = + 2
  ; ckm33 = + 0
  ; up11 = + 6
  ; up12 = + 5
  ; up13 = + 3
  ; up21 = + 5
  ; up22 = + 4
  ; up23 = + 2
  ; up31 = + 3
  ; up32 = + 2
  ; up33 = + 0
  ; down11 = + 6
  ; down12 = + 5
  ; down13 = + 3
  ; down21 = + 5
  ; down22 = + 4
  ; down23 = + 2
  ; down31 = + 3
  ; down32 = + 2
  ; down33 = + 0
  }

record FroggattNielsenWitness : Setω where
  field
    chargeAssignment :
      FNChargeAssignment

    chargeAssignmentIsCanonical :
      chargeAssignment ≡ canonicalFNChargeAssignment

    chargeAssignmentBoundary :
      List String

    suppressionTexture :
      FNSuppressionTexture

    suppressionTextureIsCanonical :
      suppressionTexture ≡ canonicalFNSuppressionTexture

    suppressionTextureBoundary :
      List String

    epsilonLabel :
      String

    downTexture :
      Matter.MixingMatrix

    upTexture :
      Matter.MixingMatrix

    canonicalTexture :
      Matter.MixingMatrix

    downTextureIsCanonical :
      downTexture ≡ canonicalTexture

    upTextureIsCanonical :
      upTexture ≡ canonicalTexture

    witnessBoundary :
      List String

open FroggattNielsenWitness public

canonicalFroggattNielsenWitness : FroggattNielsenWitness
canonicalFroggattNielsenWitness =
  record
    { chargeAssignment = canonicalFNChargeAssignment
    ; chargeAssignmentIsCanonical = refl
    ; chargeAssignmentBoundary =
        "The charge assignment is fixed concretely as q_Q = (3,2,0), q_U = (3,2,0), q_D = (3,2,0), q_H = 0"
        ∷ "This is a packaging witness over the existing FN/CKM lane, not a claim of exact physical normalization"
        ∷ []
    ; suppressionTexture = canonicalFNSuppressionTexture
    ; suppressionTextureIsCanonical = refl
    ; suppressionTextureBoundary =
        "The CKM suppression texture is the explicit exponent table [[0,1,3],[1,0,2],[3,2,0]]"
        ∷ "The up- and down-Yukawa suppression textures are explicitly packaged as [[6,5,3],[5,4,2],[3,2,0]]"
        ∷ []
    ; epsilonLabel = "epsilon ~= 0.225 from the Wolfenstein lane"
    ; downTexture = Matter.canonicalWolfensteinMixingMatrix
    ; upTexture = Matter.canonicalWolfensteinMixingMatrix
    ; canonicalTexture = Matter.canonicalWolfensteinMixingMatrix
    ; downTextureIsCanonical = refl
    ; upTextureIsCanonical = refl
    ; witnessBoundary =
        "Froggatt-Nielsen expansion packages the finite texture lane"
        ∷ "The canonical texture is reused from the existing concrete mixing matrix"
        ∷ "The module now packages an explicit FN charge assignment and explicit suppression textures"
        ∷ "This module does not invent a new matrix carrier"
        ∷ []
    }

froggattNielsenBoundary : List String
froggattNielsenBoundary =
  "Froggatt-Nielsen expansion is packaged as concrete texture data"
  ∷ []
