module DASHI.Biology.Molecular.MolecularConstrainedMinimizerBridge where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Analysis.FiniteOperatorReductionCore as FOR
import DASHI.Biology.Molecular.MolecularAssemblyBoundary as MAB

------------------------------------------------------------------------
-- Molecular geometry is naturally a constrained variational problem.
--
-- The finite constrained-minimizer kernel was introduced for block-spin
-- Yang–Mills, but its theorem is domain-neutral: the reconstructed fine state
-- has exactly the requested coarse value.  Here Fine can be a finite nuclear /
-- electronic configuration and Constraint can encode fixed composition,
-- charge, centre of mass, symmetry, or other coarse molecular data.
--
-- Chemistry-specific admissibility and stability remain explicit.  The bridge
-- proves exact constraint satisfaction and then packages the supplied chemical
-- witnesses into the existing MolecularAssemblyWitness.
------------------------------------------------------------------------

record MolecularConstrainedMinimizerBridge
  {f c : Level}
  (M : MAB.MolecularAssemblySystem)
  (Fine : Set f)
  (Constraint : Set c)
  : Set (lsuc (f ⊔ c)) where
  field
    reduction :
      FOR.ConstrainedMinimizerData Fine Constraint

    targetConstraint :
      Constraint

    decodeMolecule :
      Fine → MAB.MolecularAssemblySystem.Molecule M

    environment :
      MAB.MolecularAssemblySystem.Environment M

    geometry :
      MAB.MolecularAssemblySystem.Geometry M

    stereo :
      MAB.MolecularAssemblySystem.Stereochemistry M

    geometryAdmissible :
      MAB.MolecularAssemblySystem.GeometryAdmissible M
        (decodeMolecule (FOR.constrainedMinimizer reduction targetConstraint))
        geometry

    stereoAdmissible :
      MAB.MolecularAssemblySystem.StereoAdmissible M
        (decodeMolecule (FOR.constrainedMinimizer reduction targetConstraint))
        stereo

    chargeBalanced :
      MAB.MolecularAssemblySystem.ChargeBalanced M
        (decodeMolecule (FOR.constrainedMinimizer reduction targetConstraint))

    electronCompatible :
      MAB.MolecularAssemblySystem.ElectronCompatible M
        (decodeMolecule (FOR.constrainedMinimizer reduction targetConstraint))

    stable :
      MAB.MolecularAssemblySystem.StableIn M
        environment
        (decodeMolecule (FOR.constrainedMinimizer reduction targetConstraint))

open MolecularConstrainedMinimizerBridge public

molecularMinimizerHasTargetConstraint :
  ∀ {f c}
    {M : MAB.MolecularAssemblySystem}
    {Fine : Set f}
    {Constraint : Set c} →
  (B : MolecularConstrainedMinimizerBridge M Fine Constraint) →
  FOR.ConstrainedMinimizerData.average (reduction B)
    (FOR.constrainedMinimizer (reduction B) (targetConstraint B))
    ≡ targetConstraint B
molecularMinimizerHasTargetConstraint B =
  FOR.constrainedMinimizerHasAverage
    (reduction B)
    (targetConstraint B)

molecularMinimizerProducesAssemblyWitness :
  ∀ {f c}
    {M : MAB.MolecularAssemblySystem}
    {Fine : Set f}
    {Constraint : Set c} →
  MolecularConstrainedMinimizerBridge M Fine Constraint →
  MAB.MolecularAssemblyWitness M
molecularMinimizerProducesAssemblyWitness B = record
  { environment = environment B
  ; molecule =
      decodeMolecule B
        (FOR.constrainedMinimizer (reduction B) (targetConstraint B))
  ; geometry = geometry B
  ; stereo = stereo B
  ; geometryAdmissible = geometryAdmissible B
  ; stereoAdmissible = stereoAdmissible B
  ; chargeBalanced = chargeBalanced B
  ; electronCompatible = electronCompatible B
  ; stable = stable B
  }
