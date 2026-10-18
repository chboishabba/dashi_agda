module DASHI.Physics.YangMills.BalabanFiniteConditionalMixtureReopeningValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteConditionalMixtureReopeningExact as Mixture

fineNonnegativeClosed :
  Mixture.finiteConditionalMixtureNonnegativeLevel ≡ machineChecked
fineNonnegativeClosed = refl

fineMassOneClosed :
  Mixture.finiteConditionalMixtureMassOneLevel ≡ machineChecked
fineMassOneClosed = refl

reopeningCompilerClosed :
  Mixture.finiteConditionalMixtureReopeningCompilerLevel ≡ machineChecked
reopeningCompilerClosed = refl

fineProbabilityCompilerClosed :
  Mixture.finiteConditionalMixtureProbabilityCompilerLevel ≡ machineChecked
fineProbabilityCompilerClosed = refl
