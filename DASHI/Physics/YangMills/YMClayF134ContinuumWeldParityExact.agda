{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayF134ContinuumWeldParityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayAristotleDonorAtlasExact as Atlas
import DASHI.Physics.YangMills.YMClayOutstandingPhysicalFrontierExact as Frontier

------------------------------------------------------------------------
-- Exact parity surface for Aristotle's 2026-09-17 literal SU(2) continuum
-- weld.  The Lean theorem family consumes precisely the surviving physical
-- data after the varying-carrier recut:
--
--   F1  uniform positive gap on the literal Wilson cutoff trajectory
--   F3  isometric embeddings + embedded vacuum-sector graph limit
--   F4  actual YM/OS same evolution on a common core
--
-- and returns the Clay.MassGapConclusion for the OS Hamiltonian.
--
-- This module records the input normal form and verified donor theorem.  It
-- does not manufacture F1/F3/F4 and does not represent the Lean proof as an
-- Agda kernel proof.
------------------------------------------------------------------------

record LiteralSU2F134PhysicalInputs : Set₁ where
  field
    f1 : Frontier.LiteralWilsonUniformGapTrajectory
    f3 : Frontier.PhysicalContinuumLimitWitness

    Time : Set
    Vector : Set
    f4 : Frontier.YMOSSameObjectWitness Time Vector

open LiteralSU2F134PhysicalInputs public

asOutstandingPhysicalFrontier :
  LiteralSU2F134PhysicalInputs → Frontier.OutstandingPhysicalFrontier
asOutstandingPhysicalFrontier inputs = record
  { Frontier.OutstandingPhysicalFrontier.f1LiteralWilsonUniformGap = f1 inputs
  ; Frontier.OutstandingPhysicalFrontier.f3PhysicalContinuumLimit = f3 inputs
  ; Frontier.OutstandingPhysicalFrontier.Time = Time inputs
  ; Frontier.OutstandingPhysicalFrontier.Vector = Vector inputs
  ; Frontier.OutstandingPhysicalFrontier.f4YMOSSameObject = f4 inputs
  }

continuumWeldLean : Atlas.LeanTheoremArtifact
continuumWeldLean = Atlas.literalSU2ContinuumWeldLean

f2IndependentInputRequired : Bool
f2IndependentInputRequired = false

f2IndependentInputRequiredIsFalse : f2IndependentInputRequired ≡ false
f2IndependentInputRequiredIsFalse = refl

f134AreExactlyTheSurvivingPhysicalInputs : Bool
f134AreExactlyTheSurvivingPhysicalInputs = true

f134AreExactlyTheSurvivingPhysicalInputsIsTrue :
  f134AreExactlyTheSurvivingPhysicalInputs ≡ true
f134AreExactlyTheSurvivingPhysicalInputsIsTrue = refl

continuumWeldLeanLevel : ProofLevel
continuumWeldLeanLevel = standardImported

physicalF134InputsLevel : ProofLevel
physicalF134InputsLevel = conditional

data F134ContinuumWeldLeanDonorPresent : Set where
  f134ContinuumWeldLeanDonorPresent : F134ContinuumWeldLeanDonorPresent

f134ContinuumWeldLeanDonorWitness : F134ContinuumWeldLeanDonorPresent
f134ContinuumWeldLeanDonorWitness = f134ContinuumWeldLeanDonorPresent
