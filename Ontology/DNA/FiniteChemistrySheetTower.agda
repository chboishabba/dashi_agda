module Ontology.DNA.FiniteChemistrySheetTower where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

open import Ontology.DNA.ChemistrySheetHamiltonian using (SheetCoordinates)
open import Ontology.DNA.ChemistrySheetTowerBoundary using
  (CarrierGrowthLaw; fixedFourWayNesting; MultiscaleSheetTower)

------------------------------------------------------------------------
-- A finite, exact, non-tetrational baseline instance.
--
-- The leaf level carries the complete base-indexed chemistry field and the
-- remaining levels are typed coarse slots.  Reconstruction is exact from the
-- leaf detail.  This is intentionally a conservative first inhabitant: later
-- refinements may replace the coarse slots with non-trivial block summaries
-- without changing the public tower interface.

data DNALevel : Set where
  leaf block4 block16 block64 block256 : DNALevel

Signal : Set
Signal = SheetCoordinates 256

Coefficient : DNALevel → Set
Coefficient leaf = Signal
Coefficient block4 = ⊤
Coefficient block16 = ⊤
Coefficient block64 = ⊤
Coefficient block256 = ⊤

Expanded : DNALevel → Set
Expanded = Coefficient

analyse : (ℓ : DNALevel) → Signal → Coefficient ℓ
analyse leaf x = x
analyse block4 x = tt
analyse block16 x = tt
analyse block64 x = tt
analyse block256 x = tt

expand : (ℓ : DNALevel) → Coefficient ℓ → Expanded ℓ
expand leaf x = x
expand block4 x = tt
expand block16 x = tt
expand block64 x = tt
expand block256 x = tt

detail : (ℓ : DNALevel) → Signal → Expanded ℓ
detail ℓ x = expand ℓ (analyse ℓ x)

reconstruct : ((ℓ : DNALevel) → Expanded ℓ) → ⊤ → Signal
reconstruct fields terminal = fields leaf

detail-agrees : (ℓ : DNALevel) (x : Signal) →
  detail ℓ x ≡ expand ℓ (analyse ℓ x)
detail-agrees ℓ x = refl

reconstructs : (x : Signal) →
  reconstruct (λ ℓ → detail ℓ x) tt ≡ x
reconstructs x = refl

finiteChemistrySheetTower : MultiscaleSheetTower
finiteChemistrySheetTower = record
  { Level = DNALevel
  ; growthLaw = fixedFourWayNesting
  ; Coefficient = Coefficient
  ; Expanded = Expanded
  ; Signal = Signal
  ; analyse = analyse
  ; expand = expand
  ; detail = detail
  ; Coarsest = ⊤
  ; coarsest = λ x → tt
  ; reconstruct = reconstruct
  ; detail-agrees-with-analysis = detail-agrees
  ; reconstructs = reconstructs
  }

finiteTowerIsNotTetrationalByDeclaration :
  MultiscaleSheetTower.growthLaw finiteChemistrySheetTower ≡ fixedFourWayNesting
finiteTowerIsNotTetrationalByDeclaration = refl

record NonDegenerateCoarseRefinement : Set₁ where
  field
    refinedTower : MultiscaleSheetTower
    preservesSignal : MultiscaleSheetTower.Signal refinedTower ≡ Signal
    hasBlock4Information : Set
    hasBlock16Information : Set
    hasBlock64Information : Set
    hasBlock256Information : Set
