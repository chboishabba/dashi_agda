module Ontology.DNA.ChemistrySheetHamiltonianDistinguishing where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Vec using ([]; _∷_)

import Ontology.DNA.ChemistrySheetHamiltonian as H

------------------------------------------------------------------------
-- Cross-band Hamiltonian is not constant on sheet states.

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

w₁ : H.SheetCoordinates (suc zero)
w₁ = H.sheetCoordinates (H.pos ∷ []) (H.pos ∷ [])

w₂ : H.SheetCoordinates (suc zero)
w₂ = H.sheetCoordinates (H.pos ∷ []) (H.neg ∷ [])

sameUSheet : H.SheetCoordinates.uSheet w₁ ≡ H.SheetCoordinates.uSheet w₂
sameUSheet = refl

differentVSheet : H.SheetCoordinates.vSheet w₁ ≢ H.SheetCoordinates.vSheet w₂
differentVSheet ()

crossBandEnergy-w₁-zero : H.crossBandEnergy w₁ ≡ zero
crossBandEnergy-w₁-zero = refl

crossBandEnergy-w₂-one : H.crossBandEnergy w₂ ≡ suc zero
crossBandEnergy-w₂-one = refl

crossBandEnergy-distinguishes-same-u-band :
  H.crossBandEnergy w₁ ≢ H.crossBandEnergy w₂
crossBandEnergy-distinguishes-same-u-band ()

record SheetHamiltonianDistinguishingWitness : Set where
  field
    left right : H.SheetCoordinates (suc zero)
    sameBandCoordinate :
      H.SheetCoordinates.uSheet left ≡ H.SheetCoordinates.uSheet right
    stateCoordinateSeparates :
      H.SheetCoordinates.vSheet left ≢ H.SheetCoordinates.vSheet right
    energySeparates :
      H.crossBandEnergy left ≢ H.crossBandEnergy right

sheetHamiltonianDistinguishingWitness :
  SheetHamiltonianDistinguishingWitness
sheetHamiltonianDistinguishingWitness = record
  { left = w₁
  ; right = w₂
  ; sameBandCoordinate = sameUSheet
  ; stateCoordinateSeparates = differentVSheet
  ; energySeparates = crossBandEnergy-distinguishes-same-u-band
  }
