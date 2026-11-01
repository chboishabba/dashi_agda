module Ontology.DNA.ChemistrySheetTowerBoundary where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Vec using (Vec)

open import Ontology.DNA.Supervoxel4Adic using
  (Base; DNA4; DNA16; DNA64; DNA256; FlatDNA256)
open import Ontology.DNA.ChemistrySheetHamiltonian using
  (Signed; SheetCoordinates; sheetCoordinatesOf; chemistryHamiltonian)

------------------------------------------------------------------------
-- Semantic boundary for the DNA "sheet" discussion.
--
-- The existing SheetCoordinates record is a base-indexed U/V coordinate pair.
-- It is useful, but by itself it is not yet a multiscale detail-sheet tower:
-- there is no scale index, projection, expansion, residual, or reconstruction
-- law in that record.  This module keeps those meanings distinct.

------------------------------------------------------------------------
-- The existing 4/16/64/256 carrier is a fixed-depth four-way nested product.
-- It must not be identified definitionally with a tetration tower.

data CarrierGrowthLaw : Set where
  fixedFourWayNesting : CarrierGrowthLaw
  repeatedExponentiation : CarrierGrowthLaw
  tetrationalComposition : CarrierGrowthLaw

canonicalDNACarrierGrowth : CarrierGrowthLaw
canonicalDNACarrierGrowth = fixedFourWayNesting

canonicalDNACarrierIsNotDeclaredTetrational : Bool
canonicalDNACarrierIsNotDeclaredTetrational = true

record CanonicalDNACarrierLadder : Set₁ where
  field
    level1 : Set
    level2 : Set
    level3 : Set
    level4 : Set

canonicalDNACarrierLadder : CanonicalDNACarrierLadder
canonicalDNACarrierLadder = record
  { level1 = DNA4
  ; level2 = DNA16
  ; level3 = DNA64
  ; level4 = DNA256
  }

------------------------------------------------------------------------
-- Four different objects that had previously been called "sheets".

data SheetRepresentation : Set where
  baseCoordinatePair : SheetRepresentation
  coefficientSheet : SheetRepresentation
  expandedDetailField : SheetRepresentation
  scalarEnergySummary : SheetRepresentation

existingUVRepresentation : SheetRepresentation
existingUVRepresentation = baseCoordinatePair

------------------------------------------------------------------------
-- A genuine multiscale detail-sheet surface.
--
-- The tower is intentionally abstract about whether its level progression is
-- ordinary block nesting, exponentiation, tetration, or another compositional
-- hierarchy.  A concrete instance must declare that law instead of inferring it
-- from a ragged heatmap shape.

record MultiscaleSheetTower : Set₁ where
  field
    Level : Set
    growthLaw : CarrierGrowthLaw

    Coefficient : Level → Set
    Expanded : Level → Set
    Signal : Set

    analyse : (ℓ : Level) → Signal → Coefficient ℓ
    expand : (ℓ : Level) → Coefficient ℓ → Expanded ℓ
    detail : (ℓ : Level) → Signal → Expanded ℓ

    Coarsest : Set
    coarsest : Signal → Coarsest
    reconstruct : ((ℓ : Level) → Expanded ℓ) → Coarsest → Signal

    detail-agrees-with-analysis :
      (ℓ : Level) (x : Signal) → detail ℓ x ≡ expand ℓ (analyse ℓ x)

    reconstructs :
      (x : Signal) → reconstruct (λ ℓ → detail ℓ x) (coarsest x) ≡ x

------------------------------------------------------------------------
-- Chemistry acts through observables or energies on a declared tower.  This
-- record does not claim that every chemistry term is quadratic, band-local, or
-- exact in an empirical parameterisation.

record SheetHamiltonianSurface (tower : MultiscaleSheetTower) : Set₁ where
  open MultiscaleSheetTower tower
  field
    Energy : Set
    bandEnergy : (ℓ : Level) → Expanded ℓ → Energy
    crossLevelEnergy : (fine coarse : Level) → Expanded fine → Expanded coarse → Energy
    totalEnergy : Signal → Energy

------------------------------------------------------------------------
-- Bridge to the currently implemented DNA chemistry object.
--
-- This records what exists today without promoting it to a multiscale tower.

record ExistingChemistryCoordinateSurface : Set₁ where
  field
    Coordinates : Nat → Set
    coordinatesOf : ∀ {n} → Vec Base n → Coordinates n
    Energy : FlatDNA256 → Nat
    representation : SheetRepresentation
    multiscaleReconstructionProvided : Bool
    tetrationalTowerProvided : Bool

existingChemistryCoordinateSurface : ExistingChemistryCoordinateSurface
existingChemistryCoordinateSurface = record
  { Coordinates = SheetCoordinates
  ; coordinatesOf = sheetCoordinatesOf
  ; Energy = chemistryHamiltonian
  ; representation = baseCoordinatePair
  ; multiscaleReconstructionProvided = false
  ; tetrationalTowerProvided = false
  }

------------------------------------------------------------------------
-- Promotion boundary.
-- A heatmap with one row per chosen level is evidence of a rendering only.
-- It becomes a sheet tower after the operators and reconstruction law above are
-- supplied.  Tetrational status additionally requires an explicit declaration
-- and semantics for tetrational composition.

record SheetTowerPromotion : Set₁ where
  field
    tower : MultiscaleSheetTower
    hasScaleSemantics : ⊤
    hasAnalysisExpansion : ⊤
    hasExactReconstruction : ⊤
    tetrationalWhenClaimed :
      MultiscaleSheetTower.growthLaw tower ≡ tetrationalComposition → ⊤

heatmapAlonePromotesToSheetTower : Bool
heatmapAlonePromotesToSheetTower = false

raggedLengthsAloneDetermineGrowthLaw : Bool
raggedLengthsAloneDetermineGrowthLaw = false
