module DASHI.Physics.Textile.JacquardPhysicalFibreBridgeExact where

------------------------------------------------------------------------
-- Jacquard execution -> topology-indexed physical textile fibre.
--
-- The existing Jacquard owner remains canonical for program execution.  This
-- bridge only attaches SI-typed material/mechanical data to the executed woven
-- observation.  Compiled and direct execution remain physically indistinguish-
-- able whenever the physical consumer depends only on the canonical WovenRows.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (Fin)

import DASHI.Computation.JacquardOperationalSemanticsExact as Jacquard
import DASHI.Physics.Textile.TextileMechanicalFibreExact as Mechanics

record JacquardPhysicalAssignment
    (Scalar : Set)
    (n : Nat)
    (program : Jacquard.JacquardProgram n) : Set₁ where
  constructor jacquard-physical-assignment
  field
    warpMaterial :
      Fin n → Mechanics.YarnConstitutiveState Scalar

    crossingConstraint :
      Jacquard.Crossing → Mechanics.LocalTextileConstraint Scalar

open JacquardPhysicalAssignment public

record PhysicalJacquardRealisation
    (Scalar : Set)
    (n : Nat)
    (program : Jacquard.JacquardProgram n) : Set₁ where
  constructor physical-jacquard-realisation
  field
    wovenRows : Jacquard.WovenRows n
    assignment : JacquardPhysicalAssignment Scalar n program
    wovenRowsAreProgramExecution :
      wovenRows ≡ Jacquard.executeProgram program

open PhysicalJacquardRealisation public

canonicalPhysicalJacquardRealisation :
  {Scalar : Set}
  {n : Nat}
  (program : Jacquard.JacquardProgram n) →
  JacquardPhysicalAssignment Scalar n program →
  PhysicalJacquardRealisation Scalar n program
canonicalPhysicalJacquardRealisation program physicalAssignment =
  physical-jacquard-realisation
    (Jacquard.executeProgram program)
    physicalAssignment
    refl

compiledPhysicalRowsAgree :
  {n : Nat} →
  (program : Jacquard.JacquardProgram n) →
  Jacquard.executeSchedule (Jacquard.compile program)
  ≡ Jacquard.executeProgram program
compiledPhysicalRowsAgree = Jacquard.compilePreservesExecution
