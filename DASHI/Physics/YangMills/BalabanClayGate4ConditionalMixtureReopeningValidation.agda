module DASHI.Physics.YangMills.BalabanClayGate4ConditionalMixtureReopeningValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4ConditionalMixtureReopeningExact as Mixture

gate4ReopeningCompilerClosed :
  Mixture.gate4ConditionalMixtureReopeningCompilerLevel ≡ machineChecked
gate4ReopeningCompilerClosed = refl

gate4FineProbabilityCompilerClosed :
  Mixture.gate4ConditionalMixtureFineProbabilityCompilerLevel ≡ machineChecked
gate4FineProbabilityCompilerClosed = refl

slowFieldProbabilityLawRemainsPhysical :
  Mixture.physicalSlowFieldProbabilityLawLevel ≡ conditional
slowFieldProbabilityLawRemainsPhysical = refl
