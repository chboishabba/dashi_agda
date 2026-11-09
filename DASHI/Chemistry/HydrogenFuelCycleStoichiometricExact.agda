module DASHI.Chemistry.HydrogenFuelCycleStoichiometricExact where

-- Existing abstract proof ownership: DASHI.Analysis.StoichiometricConservation.
-- Selected CHO chemistry: conventional water electrolysis, Sabatier methanation
-- and methane combustion, NOT invented by Michael McLaren or this formalisation.
-- User-directed, ChatGPT-drafted repository instantiation, 2026-11-09.
--
-- This is a *projected elemental-total state*, not a molecule-resolved
-- kinetic model. It proves that each selected reaction has zero atom residual
-- and that this property composes along any finite selected reaction path.
-- Real reactor yields, species availability, temperature and efficiency
-- are separate source and measurement gates.

open import DASHI.Core.Prelude
  using (Nat; _+_; _∸_; _≡_; refl; rewrite; +-identityʳ)
import DASHI.Analysis.StoichiometricConservation as SC
import DASHI.Chemistry.HydrogenFuelCycleExact as Fuel

data SelectedReaction : Set where
  splitWater : SelectedReaction
  methanateCarbon : SelectedReaction
  burnMethane : SelectedReaction

atomsBefore : SelectedReaction → Fuel.CHO
atomsBefore splitWater = Fuel.waterElectrolysisInput
atomsBefore methanateCarbon = Fuel.sabatierInput
atomsBefore burnMethane = Fuel.methaneCombustionInput

atomsAfter : SelectedReaction → Fuel.CHO
atomsAfter splitWater = Fuel.waterElectrolysisOutput
atomsAfter methanateCarbon = Fuel.sabatierOutput
atomsAfter burnMethane = Fuel.methaneCombustionOutput

-- Absolute element-count discrepancies, not a signed stoichiometric vector.
atomResidual : Fuel.CHO → Fuel.CHO → Fuel.CHO
atomResidual before after =
  Fuel.cho
    ((Fuel.carbon before ∸ Fuel.carbon after)
      + (Fuel.carbon after ∸ Fuel.carbon before))
    ((Fuel.hydrogen before ∸ Fuel.hydrogen after)
      + (Fuel.hydrogen after ∸ Fuel.hydrogen before))
    ((Fuel.oxygen before ∸ Fuel.oxygen after)
      + (Fuel.oxygen after ∸ Fuel.oxygen before))

zeroAtoms : Fuel.CHO
zeroAtoms = Fuel.cho 0 0 0

reactionResidual : SelectedReaction → Fuel.CHO
reactionResidual r = atomResidual (atomsBefore r) (atomsAfter r)

waterResidualZero : reactionResidual splitWater ≡ zeroAtoms
waterResidualZero = refl

methanationResidualZero : reactionResidual methanateCarbon ≡ zeroAtoms
methanationResidualZero = refl

combustionResidualZero : reactionResidual burnMethane ≡ zeroAtoms
combustionResidualZero = refl

atomAddition : Fuel.CHO → Fuel.CHO → Fuel.CHO
atomAddition (Fuel.cho c h o) (Fuel.cho c' h' o') =
  Fuel.cho (c + c') (h + h') (o + o')

atomAdditionIdentity :
  (a : Fuel.CHO) → atomAddition a zeroAtoms ≡ a
atomAdditionIdentity (Fuel.cho c h o)
  rewrite +-identityʳ c | +-identityʳ h | +-identityʳ o = refl

atomAdditive : SC.AdditiveQuantity Fuel.CHO
atomAdditive = record
  { zero = zeroAtoms
  ; _⊕_ = atomAddition
  ; rightIdentity = atomAdditionIdentity
  }

elementalProjectedSystem :
  SC.StoichiometricSystem
    SelectedReaction Fuel.CHO Fuel.CHO Fuel.CHO
elementalProjectedSystem = record
  { additive = atomAdditive
  ; stoichiometricColumn = reactionResidual
  ; leftFunctional = λ x → x
  ; quantity = λ x → x
  ; step = λ r state → atomAddition state (reactionResidual r)
  ; quantityUpdate = λ r state → refl
  }

elementalLeftKernel :
  SC.LeftKernelConservation elementalProjectedSystem
elementalLeftKernel = record
  { annihilatesStoichiometry = annihilates }
  where
  annihilates :
    (r : SelectedReaction) →
    SC.leftFunctional elementalProjectedSystem
      (SC.stoichiometricColumn elementalProjectedSystem r)
      ≡ SC.zero (SC.additive elementalProjectedSystem)
  annihilates splitWater = refl
  annihilates methanateCarbon = refl
  annihilates burnMethane = refl

selectedFuelCycleCertificate :
  SC.StoichiometricConservationCertificate elementalProjectedSystem
selectedFuelCycleCertificate =
  SC.certifyStoichiometricConservation
    elementalProjectedSystem elementalLeftKernel

selectedFuelCyclePathConserves :
  (reactions : SC.List SelectedReaction) →
  (initialAtoms : Fuel.CHO) →
  SC.quantity elementalProjectedSystem
    (SC.runReactionPath elementalProjectedSystem reactions initialAtoms)
    ≡ initialAtoms
selectedFuelCyclePathConserves =
  SC.reactionPathConserves elementalProjectedSystem elementalLeftKernel
