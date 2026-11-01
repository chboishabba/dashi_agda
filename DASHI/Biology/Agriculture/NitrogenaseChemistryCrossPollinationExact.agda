module DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.Molecular.MolecularStoichiometricConservation as MolecularStoich
import DASHI.Biology.Cell.OpenMetabolicNetwork as Metabolism
import DASHI.Chemistry.AdmissibleReactionTransitionBridgeExact as Chemistry

------------------------------------------------------------------------
-- BIOLOGY <-> CHEMISTRY X-POLLINATION FOR BIOLOGICAL NITROGEN FIXATION
--
-- Mechanistic source boundary:
--   Seefeldt, Hoffman, Dean (2009), "Mechanism of Mo-dependent nitrogenase",
--   Annual Review of Biochemistry 78:701-722,
--   DOI 10.1146/annurev.biochem.78.070907.103812.
--
-- Standard limiting Mo-nitrogenase stoichiometry:
--
--   N2 + 8 H+ + 8 e- + 16 MgATP
--      -> 2 NH3 + H2 + 16 MgADP + 16 Pi.
--
-- Later structural reviews preserve this as a working/limiting overall
-- stoichiometry while noting that observed ATP/H2 ratios may deviate under
-- non-ideal conditions.  Accordingly, this module does not identify the
-- limiting equation with every in-vivo flux realization.
--
-- DASHI owns the typed carrier and cross-domain firewalls below.
------------------------------------------------------------------------

data ChemicalSpecies : Set where
  N2 : ChemicalSpecies
  Hplus : ChemicalSpecies
  electron : ChemicalSpecies
  MgATP : ChemicalSpecies
  NH3 : ChemicalSpecies
  H2 : ChemicalSpecies
  MgADP : ChemicalSpecies
  Pi : ChemicalSpecies

data Side : Set where
  reactant : Side
  product : Side

record StoichiometricTerm : Set where
  constructor term
  field
    species : ChemicalSpecies
    side : Side
    coefficient : Nat

open StoichiometricTerm public

nitrogenaseTerms : List StoichiometricTerm
nitrogenaseTerms =
  term N2 reactant 1
  ∷ term Hplus reactant 8
  ∷ term electron reactant 8
  ∷ term MgATP reactant 16
  ∷ term NH3 product 2
  ∷ term H2 product 1
  ∷ term MgADP product 16
  ∷ term Pi product 16
  ∷ []

------------------------------------------------------------------------
-- Source-exact coefficient receipts.
------------------------------------------------------------------------

n2Coefficient : Nat
n2Coefficient = 1

protonCoefficient : Nat
protonCoefficient = 8

electronCoefficient : Nat
electronCoefficient = 8

atpCoefficient : Nat
atpCoefficient = 16

ammoniaCoefficient : Nat
ammoniaCoefficient = 2

hydrogenCoefficient : Nat
hydrogenCoefficient = 1

n2CoefficientIsOne : n2Coefficient ≡ 1
n2CoefficientIsOne = refl

atpCoefficientIsSixteen : atpCoefficient ≡ 16
atpCoefficientIsSixteen = refl

electronCoefficientIsEight : electronCoefficient ≡ 8
electronCoefficientIsEight = refl

ammoniaCoefficientIsTwo : ammoniaCoefficient ≡ 2
ammoniaCoefficientIsTwo = refl

------------------------------------------------------------------------
-- Cross-pollination with DASHI's existing chemistry and biology surfaces.
--
-- MolecularStoichiometricConservation says that once a concrete molecular
-- reaction is welded to a StoichiometricSystem with a left-kernel certificate,
-- step/path conservation follows.  We reuse that architecture but do not
-- manufacture the missing concrete vector/left-kernel instantiation here.
--
-- AdmissibleReactionTransitionBridge requires a separate enablement witness:
-- reactant availability, catalyst/cofactor state, environment and compartment
-- compatibility cannot be inferred merely from a balanced equation.
--
-- OpenMetabolicNetwork similarly keeps reaction flux/environment/energy
-- gradients distinct from mere stoichiometric possibility.
------------------------------------------------------------------------

molecularStoichiometricCompilerSurface : Set₁
molecularStoichiometricCompilerSurface =
  ∀ {M R} →
  MolecularStoich.MolecularStoichiometricBridge M R → Set

chemistryEnablementSurface : Set₁
chemistryEnablementSurface =
  ∀ {transition} → Chemistry.TypedReactionSemantics transition → Set

metabolicNetworkSurface : Set₁
metabolicNetworkSurface = Metabolism.OpenMetabolicNetwork

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

record NitrogenaseCrossDomainBoundary : Set where
  constructor nitrogenaseCrossDomainBoundary
  field
    balancedEquationImpliesInVivoFlux : Bool
    balancedEquationImpliesInVivoFluxIsFalse : balancedEquationImpliesInVivoFlux ≡ false
    balancedEquationImpliesReactionEnabled : Bool
    balancedEquationImpliesReactionEnabledIsFalse : balancedEquationImpliesReactionEnabled ≡ false
    reactionEnabledImpliesSoybeanNitrogenDemandMet : Bool
    reactionEnabledImpliesSoybeanNitrogenDemandMetIsFalse : reactionEnabledImpliesSoybeanNitrogenDemandMet ≡ false
    nitrogenaseFluxImpliesWholeFieldFertilizerReplacement : Bool
    nitrogenaseFluxImpliesWholeFieldFertilizerReplacementIsFalse : nitrogenaseFluxImpliesWholeFieldFertilizerReplacement ≡ false
    limitingStoichiometryImpliesExactObservedATPCost : Bool
    limitingStoichiometryImpliesExactObservedATPCostIsFalse : limitingStoichiometryImpliesExactObservedATPCost ≡ false

canonicalNitrogenaseCrossDomainBoundary : NitrogenaseCrossDomainBoundary
canonicalNitrogenaseCrossDomainBoundary =
  nitrogenaseCrossDomainBoundary
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Highest-alpha bridge target.
--
-- This is the exact chain still required to connect molecular chemistry to the
-- agronomic substitution claim on the same object:
--
--   nitrogenase stoichiometry
--   -> enabled bacterial reaction under nodule conditions
--   -> integrated fixed-N flux
--   -> transfer/assimilation into soybean N pool
--   -> crop N demand over the season
--   -> counterfactual mineral-N requirement avoided.
------------------------------------------------------------------------

data BridgeStage : Set where
  enzymeStoichiometry : BridgeStage
  reactionEnablement : BridgeStage
  bacterialFixedNFlux : BridgeStage
  plantAssimilation : BridgeStage
  seasonalCropNDemand : BridgeStage
  avoidedMineralN : BridgeStage

stageClosed : BridgeStage → Bool
stageClosed enzymeStoichiometry = true
stageClosed reactionEnablement = false
stageClosed bacterialFixedNFlux = false
stageClosed plantAssimilation = false
stageClosed seasonalCropNDemand = false
stageClosed avoidedMineralN = false

enzymeStoichiometryClosed : stageClosed enzymeStoichiometry ≡ true
enzymeStoichiometryClosed = refl

reactionEnablementStillOpen : stageClosed reactionEnablement ≡ false
reactionEnablementStillOpen = refl

avoidedMineralNStillOpen : stageClosed avoidedMineralN ≡ false
avoidedMineralNStillOpen = refl
