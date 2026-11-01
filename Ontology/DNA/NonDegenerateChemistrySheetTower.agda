module Ontology.DNA.NonDegenerateChemistrySheetTower where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

open import Ontology.DNA.Supervoxel4Adic using (FlatDNA256)
open import Ontology.DNA.ChemistryConcrete using
  (countStrong; countComplementSpan2; countRCPal4; countHairpin6; admissibleConcrete)
open import Ontology.DNA.ChemistrySheetHamiltonian using
  (sheetCoordinatesOf; sheetBandEnergy; crossBandEnergy; chemistryHamiltonian)
open import Ontology.DNA.ChemistrySheetTowerBoundary using
  (MultiscaleSheetTower; fixedFourWayNesting)

------------------------------------------------------------------------
-- A non-degenerate, redundant, exactly reconstructing chemistry tower.
--
-- Each coarse level now contains an actual chemistry summary rather than Unit.
-- Reconstruction remains exact because the leaf detail is retained.  This is a
-- redundant analysis tower, not yet a critically sampled orthogonal transform.

record Summary4 : Set where
  constructor summary4
  field
    gcLoad : Nat
    reverseComplement4Risk : Nat

record Summary16 : Set where
  constructor summary16
  field
    complementSpanRisk : Nat
    shortHairpinRisk : Nat

record Summary64 : Set where
  constructor summary64
  field
    signedTransitionEnergy : Nat
    crossChannelEnergy : Nat

record Summary256 : Set where
  constructor summary256
  field
    totalChemistryEnergy : Nat
    operationallyAdmissible : Bool

data ChemistryLevel : Set where
  leaf block4 block16 block64 block256 : ChemistryLevel

Signal : Set
Signal = FlatDNA256

Coefficient : ChemistryLevel → Set
Coefficient leaf = FlatDNA256
Coefficient block4 = Summary4
Coefficient block16 = Summary16
Coefficient block64 = Summary64
Coefficient block256 = Summary256

Expanded : ChemistryLevel → Set
Expanded = Coefficient

summaryAt4 : FlatDNA256 → Summary4
summaryAt4 xs = summary4 (countStrong xs) (countRCPal4 xs)

summaryAt16 : FlatDNA256 → Summary16
summaryAt16 xs = summary16 (countComplementSpan2 xs) (countHairpin6 xs)

summaryAt64 : FlatDNA256 → Summary64
summaryAt64 xs =
  summary64
    (sheetBandEnergy (sheetCoordinatesOf xs))
    (crossBandEnergy (sheetCoordinatesOf xs))

summaryAt256 : FlatDNA256 → Summary256
summaryAt256 xs = summary256 (chemistryHamiltonian xs) (admissibleConcrete xs)

analyse : (ℓ : ChemistryLevel) → Signal → Coefficient ℓ
analyse leaf xs = xs
analyse block4 xs = summaryAt4 xs
analyse block16 xs = summaryAt16 xs
analyse block64 xs = summaryAt64 xs
analyse block256 xs = summaryAt256 xs

expand : (ℓ : ChemistryLevel) → Coefficient ℓ → Expanded ℓ
expand ℓ x = x

detail : (ℓ : ChemistryLevel) → Signal → Expanded ℓ
detail ℓ xs = expand ℓ (analyse ℓ xs)

coarsest : Signal → Summary256
coarsest = summaryAt256

reconstruct : ((ℓ : ChemistryLevel) → Expanded ℓ) → Summary256 → Signal
reconstruct fields terminal = fields leaf

detail-agrees : (ℓ : ChemistryLevel) (xs : Signal) →
  detail ℓ xs ≡ expand ℓ (analyse ℓ xs)
detail-agrees ℓ xs = refl

reconstructs : (xs : Signal) →
  reconstruct (λ ℓ → detail ℓ xs) (coarsest xs) ≡ xs
reconstructs xs = refl

nonDegenerateChemistrySheetTower : MultiscaleSheetTower
nonDegenerateChemistrySheetTower = record
  { Level = ChemistryLevel
  ; growthLaw = fixedFourWayNesting
  ; Coefficient = Coefficient
  ; Expanded = Expanded
  ; Signal = Signal
  ; analyse = analyse
  ; expand = expand
  ; detail = detail
  ; Coarsest = Summary256
  ; coarsest = coarsest
  ; reconstruct = reconstruct
  ; detail-agrees-with-analysis = detail-agrees
  ; reconstructs = reconstructs
  }

summary4-is-computed : (xs : Signal) →
  analyse block4 xs ≡ summary4 (countStrong xs) (countRCPal4 xs)
summary4-is-computed xs = refl

summary16-is-computed : (xs : Signal) →
  analyse block16 xs ≡ summary16 (countComplementSpan2 xs) (countHairpin6 xs)
summary16-is-computed xs = refl

summary256-is-computed : (xs : Signal) →
  analyse block256 xs ≡ summary256 (chemistryHamiltonian xs) (admissibleConcrete xs)
summary256-is-computed xs = refl

record CriticallySampledRefinementTarget : Set₁ where
  field
    Tower : MultiscaleSheetTower
    noLeafDuplication : Set
    orthogonalOrBiorthogonalDetails : Set
    exactReconstruction : Set
    blockLocality : Set
