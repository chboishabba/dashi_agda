module Ontology.DNA.ChemistrySheetHamiltonian where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Vec using (Vec; []; _∷_)

open import Ontology.DNA.Supervoxel4Adic using (Base; FlatDNA256)
open import Ontology.DNA.ChemistryQuotient using
  (Strength; weak; strong; PurineClass; pyrimidine; purine;
   strength; purineClass)
open import Ontology.DNA.ChemistryConcrete using
  (countStrong; countComplementSpan2; countHairpin6; countRCPal4)

------------------------------------------------------------------------
-- Chemistry Hamiltonian in sheet space.
-- U and V are turned into signed sheet coordinates, and chemistry energy is
-- packaged as a cross-band functional over those multiscale coordinates.

data Signed : Set where
  neg zer pos : Signed

record SheetCoordinates (n : Nat) : Set where
  constructor sheetCoordinates
  field
    uSheet : Vec Signed n
    vSheet : Vec Signed n

signStrength : Strength → Signed
signStrength weak = neg
signStrength strong = pos

signPurine : PurineClass → Signed
signPurine pyrimidine = neg
signPurine purine = pos

sheetCoordinatesOf : ∀ {n} → Vec Base n → SheetCoordinates n
sheetCoordinatesOf [] = sheetCoordinates [] []
sheetCoordinatesOf (b ∷ bs) with sheetCoordinatesOf bs
... | sheetCoordinates us vs =
      sheetCoordinates (signStrength (strength b) ∷ us)
                       (signPurine (purineClass b) ∷ vs)

uSheet-sheetCoordinatesOf-∷ :
  ∀ {n} (b : Base) (bs : Vec Base n) →
  SheetCoordinates.uSheet (sheetCoordinatesOf (b ∷ bs))
    ≡ signStrength (strength b) ∷ SheetCoordinates.uSheet (sheetCoordinatesOf bs)
uSheet-sheetCoordinatesOf-∷ b bs with sheetCoordinatesOf bs
... | sheetCoordinates us vs = refl

vSheet-sheetCoordinatesOf-∷ :
  ∀ {n} (b : Base) (bs : Vec Base n) →
  SheetCoordinates.vSheet (sheetCoordinatesOf (b ∷ bs))
    ≡ signPurine (purineClass b) ∷ SheetCoordinates.vSheet (sheetCoordinatesOf bs)
vSheet-sheetCoordinatesOf-∷ b bs with sheetCoordinatesOf bs
... | sheetCoordinates us vs = refl

sameSign : Signed → Signed → Bool
sameSign neg neg = true
sameSign zer zer = true
sameSign pos pos = true
sameSign _ _ = false

sameSign-sym : ∀ (x y : Signed) → sameSign x y ≡ sameSign y x
sameSign-sym neg neg = refl
sameSign-sym neg zer = refl
sameSign-sym neg pos = refl
sameSign-sym zer neg = refl
sameSign-sym zer zer = refl
sameSign-sym zer pos = refl
sameSign-sym pos neg = refl
sameSign-sym pos zer = refl
sameSign-sym pos pos = refl

countSignedTransitionsFrom : ∀ {n} → Signed → Vec Signed n → Nat
countSignedTransitionsFrom x [] = zero
countSignedTransitionsFrom x (y ∷ ys) with sameSign x y
... | true  = countSignedTransitionsFrom y ys
... | false = suc (countSignedTransitionsFrom y ys)

countSignedTransitions : ∀ {n} → Vec Signed n → Nat
countSignedTransitions [] = zero
countSignedTransitions (x ∷ xs) = countSignedTransitionsFrom x xs

countCrossBandCoupling : ∀ {n} → Vec Signed n → Vec Signed n → Nat
countCrossBandCoupling [] [] = zero
countCrossBandCoupling (u ∷ us) (v ∷ vs) with sameSign u v
... | true  = countCrossBandCoupling us vs
... | false = suc (countCrossBandCoupling us vs)

countCrossBandCoupling-sym :
  ∀ {n} (u v : Vec Signed n) →
  countCrossBandCoupling u v ≡ countCrossBandCoupling v u
countCrossBandCoupling-sym [] [] = refl
countCrossBandCoupling-sym (u ∷ us) (v ∷ vs) rewrite sameSign-sym u v with sameSign v u
... | true = countCrossBandCoupling-sym us vs
... | false rewrite countCrossBandCoupling-sym us vs = refl

sheetBandEnergy : ∀ {n} → SheetCoordinates n → Nat
sheetBandEnergy (sheetCoordinates u v) =
  countSignedTransitions u + countSignedTransitions v

crossBandEnergy : ∀ {n} → SheetCoordinates n → Nat
crossBandEnergy (sheetCoordinates u v) = countCrossBandCoupling u v

crossBandEnergy-sheetCoordinatesOf :
  ∀ {n} (xs : Vec Base n) →
  crossBandEnergy (sheetCoordinatesOf xs)
    ≡ countCrossBandCoupling
        (SheetCoordinates.uSheet (sheetCoordinatesOf xs))
        (SheetCoordinates.vSheet (sheetCoordinatesOf xs))
crossBandEnergy-sheetCoordinatesOf xs with sheetCoordinatesOf xs
... | sheetCoordinates u v = refl

crossBandEnergy-sym :
  ∀ {n} (u v : Vec Signed n) →
  crossBandEnergy (sheetCoordinates u v) ≡ crossBandEnergy (sheetCoordinates v u)
crossBandEnergy-sym u v = countCrossBandCoupling-sym u v

chemistryHamiltonianOf : ∀ {n} → Vec Base n → Nat
chemistryHamiltonianOf xs with sheetCoordinatesOf xs
... | sh =
      (countStrong xs + countComplementSpan2 xs + countRCPal4 xs + countHairpin6 xs)
        + sheetBandEnergy sh
        + crossBandEnergy sh

chemistryHamiltonian : FlatDNA256 → Nat
chemistryHamiltonian = chemistryHamiltonianOf
