module DASHI.Biology.Molecular.MolecularStoichiometricConservation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Analysis.StoichiometricConservation as SC
import DASHI.Biology.Molecular.MolecularAssemblyBoundary as MAB

------------------------------------------------------------------------
-- Molecular adapter for exact stoichiometric conservation.
--
-- A MolecularReactionSystem provides a contextual reaction relation but leaves
-- its conservation predicate abstract.  This bridge supplies an explicit
-- reaction-event transition, identifies it with a stoichiometric system, and
-- turns a left-kernel certificate into both equality of conserved quantities
-- and the existing domain-specific `conserved` relation.
------------------------------------------------------------------------

record MolecularStoichiometricBridge
    (M : MAB.MolecularAssemblySystem)
    (R : MAB.MolecularReactionSystem M)
    : Set₁ where
  field
    ReactionEvent : Set
    Vector : Set

    contextOf :
      ReactionEvent →
      MAB.MolecularReactionSystem.ReactionContext R

    productOf :
      ReactionEvent →
      MAB.MolecularAssemblySystem.Molecule M →
      MAB.MolecularAssemblySystem.Molecule M

    reactsTo :
      (event : ReactionEvent) →
      (molecule : MAB.MolecularAssemblySystem.Molecule M) →
      MAB.MolecularReactionSystem.ReactsTo R
        (contextOf event)
        molecule
        (productOf event molecule)

    stoichiometry :
      SC.StoichiometricSystem
        ReactionEvent
        Vector
        (MAB.MolecularReactionSystem.ConservedQuantity R)
        (MAB.MolecularAssemblySystem.Molecule M)

    stepMatchesProduct :
      (event : ReactionEvent) →
      (molecule : MAB.MolecularAssemblySystem.Molecule M) →
      SC.step stoichiometry event molecule ≡ productOf event molecule

    leftKernel :
      SC.LeftKernelConservation stoichiometry

    conservationRelationFromEquality :
      (event : ReactionEvent) →
      (molecule : MAB.MolecularAssemblySystem.Molecule M) →
      SC.quantity stoichiometry (productOf event molecule)
        ≡ SC.quantity stoichiometry molecule →
      MAB.MolecularReactionSystem.conserved R
        (contextOf event)
        molecule
        (productOf event molecule)
        (SC.quantity stoichiometry molecule)

open MolecularStoichiometricBridge public

molecularProductConserves :
  ∀ {M R} →
  (B : MolecularStoichiometricBridge M R) →
  (event : ReactionEvent B) →
  (molecule : MAB.MolecularAssemblySystem.Molecule M) →
  SC.quantity (stoichiometry B) (productOf B event molecule)
    ≡ SC.quantity (stoichiometry B) molecule
molecularProductConserves B event molecule =
  trans
    (cong
      (SC.quantity (stoichiometry B))
      (sym (stepMatchesProduct B event molecule)))
    (SC.reactionStepConserves
      (stoichiometry B)
      (leftKernel B)
      event
      molecule)

molecularReactionCarriesConservation :
  ∀ {M R} →
  (B : MolecularStoichiometricBridge M R) →
  (event : ReactionEvent B) →
  (molecule : MAB.MolecularAssemblySystem.Molecule M) →
  MAB.MolecularReactionSystem.conserved R
    (contextOf B event)
    molecule
    (productOf B event molecule)
    (SC.quantity (stoichiometry B) molecule)
molecularReactionCarriesConservation B event molecule =
  conservationRelationFromEquality B event molecule
    (molecularProductConserves B event molecule)

runMolecularReactionPath :
  ∀ {M R} →
  (B : MolecularStoichiometricBridge M R) →
  List (ReactionEvent B) →
  MAB.MolecularAssemblySystem.Molecule M →
  MAB.MolecularAssemblySystem.Molecule M
runMolecularReactionPath B [] molecule = molecule
runMolecularReactionPath B (event ∷ events) molecule =
  runMolecularReactionPath B events (productOf B event molecule)

molecularReactionPathConserves :
  ∀ {M R} →
  (B : MolecularStoichiometricBridge M R) →
  (events : List (ReactionEvent B)) →
  (molecule : MAB.MolecularAssemblySystem.Molecule M) →
  SC.quantity (stoichiometry B)
    (runMolecularReactionPath B events molecule)
    ≡ SC.quantity (stoichiometry B) molecule
molecularReactionPathConserves B [] molecule = refl
molecularReactionPathConserves B (event ∷ events) molecule =
  trans
    (molecularReactionPathConserves B events (productOf B event molecule))
    (molecularProductConserves B event molecule)

record MolecularStoichiometricCertificate
    {M : MAB.MolecularAssemblySystem}
    {R : MAB.MolecularReactionSystem M}
    (B : MolecularStoichiometricBridge M R)
    : Set₁ where
  field
    genericCertificate :
      SC.StoichiometricConservationCertificate (stoichiometry B)

    domainStepConservation :
      (event : ReactionEvent B) →
      (molecule : MAB.MolecularAssemblySystem.Molecule M) →
      MAB.MolecularReactionSystem.conserved R
        (contextOf B event)
        molecule
        (productOf B event molecule)
        (SC.quantity (stoichiometry B) molecule)

    domainPathConservation :
      (events : List (ReactionEvent B)) →
      (molecule : MAB.MolecularAssemblySystem.Molecule M) →
      SC.quantity (stoichiometry B)
        (runMolecularReactionPath B events molecule)
        ≡ SC.quantity (stoichiometry B) molecule

open MolecularStoichiometricCertificate public

certifyMolecularStoichiometry :
  ∀ {M R} →
  (B : MolecularStoichiometricBridge M R) →
  MolecularStoichiometricCertificate B
certifyMolecularStoichiometry B = record
  { genericCertificate =
      SC.certifyStoichiometricConservation
        (stoichiometry B)
        (leftKernel B)
  ; domainStepConservation = molecularReactionCarriesConservation B
  ; domainPathConservation = molecularReactionPathConserves B
  }
