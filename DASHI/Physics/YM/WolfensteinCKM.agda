module DASHI.Physics.YM.WolfensteinCKM where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.YM.FroggattNielsenExpansion as FN

record WolfensteinCKMWitness : Setω where
  field
    froggattNielsenWitness :
      FN.FroggattNielsenWitness

    ckmMatrix :
      Matter.MixingMatrix

    ckmMatrixIsCanonical :
      ckmMatrix ≡ Matter.canonicalWolfensteinMixingMatrix

    vvdaggerProduct :
      Matter.MixingMatrix

    vvdaggerProductIsCanonical :
      vvdaggerProduct ≡ Matter.canonicalWolfensteinVVdaggerProductMatrix

    residualMatrix :
      Matter.MixingMatrix

    residualMatrixIsCanonical :
      residualMatrix ≡ Matter.canonicalWolfensteinVVdaggerMinusIdentityResidual

    witnessBoundary :
      List String

open WolfensteinCKMWitness public

canonicalWolfensteinCKMWitness : WolfensteinCKMWitness
canonicalWolfensteinCKMWitness =
  record
    { froggattNielsenWitness = FN.canonicalFroggattNielsenWitness
    ; ckmMatrix = Matter.canonicalWolfensteinMixingMatrix
    ; ckmMatrixIsCanonical = refl
    ; vvdaggerProduct = Matter.canonicalWolfensteinVVdaggerProductMatrix
    ; vvdaggerProductIsCanonical = refl
    ; residualMatrix = Matter.canonicalWolfensteinVVdaggerMinusIdentityResidual
    ; residualMatrixIsCanonical = refl
    ; witnessBoundary =
        "Wolfenstein CKM packages the existing canonical mixing matrix"
        ∷ "The FN witness is threaded through as the texture-frontier input"
        ∷ "The VV† product and residual are concrete matrix records"
        ∷ []
    }

wolfensteinCKMBoundary : List String
wolfensteinCKMBoundary =
  "Wolfenstein CKM is packaged concretely from the repository's matrix data"
  ∷ []
