module Ontology.DNA.ChemistrySheetTransport where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

open import Ontology.DNA.Supervoxel4Adic using (FlatDNA256)
open import Ontology.DNA.ChemistryConcrete using
  (countStrong; countComplementSpan2; countRCPal4; countHairpin6)
open import Ontology.DNA.ChemistrySheetHamiltonian using
  (SheetCoordinates; sheetCoordinatesOf; sheetBandEnergy; crossBandEnergy;
   chemistryHamiltonian)
open import Ontology.DNA.FiniteChemistrySheetTower using
  (Signal; DNALevel; leaf; finiteChemistrySheetTower)

------------------------------------------------------------------------
-- Exact ledger separating chemistry terms already represented by the signed
-- coordinate field from local motif terms that remain outside the current
-- sheet proxy.

localMotifEnergy : FlatDNA256 → Nat
localMotifEnergy xs =
  countStrong xs + countComplementSpan2 xs + countRCPal4 xs + countHairpin6 xs

signedSheetProxyEnergy : Signal → Nat
signedSheetProxyEnergy sh = sheetBandEnergy sh + crossBandEnergy sh

towerAnalysis : FlatDNA256 → Signal
towerAnalysis = sheetCoordinatesOf

towerTransportEnergy : FlatDNA256 → Nat
towerTransportEnergy xs =
  localMotifEnergy xs + signedSheetProxyEnergy (towerAnalysis xs)

chemistryTransportExact : ∀ xs →
  towerTransportEnergy xs ≡ chemistryHamiltonian xs
chemistryTransportExact xs with sheetCoordinatesOf xs
... | sh = refl

record ChemistryTransportLedger : Set where
  constructor transportLedger
  field
    localExact : Nat
    sheetProxy : Nat
    residual : Nat
    total : Nat
    total-decomposition : total ≡ localExact + sheetProxy + residual

chemistryTransportLedger : FlatDNA256 → ChemistryTransportLedger
chemistryTransportLedger xs = transportLedger
  (localMotifEnergy xs)
  (signedSheetProxyEnergy (towerAnalysis xs))
  0
  (towerTransportEnergy xs)
  refl

-- The present transport is exact because it retains the local motif residual
-- explicitly.  Promotion to a purely band-local Hamiltonian requires a
-- separate theorem proving those terms from non-degenerate coarse sheets.
record PureSheetHamiltonianPromotion : Set₁ where
  field
    bandOnlyEnergy : Signal → Nat
    agreesWithChemistry : ∀ xs →
      bandOnlyEnergy (towerAnalysis xs) ≡ chemistryHamiltonian xs
