module DASHI.Physics.YangMills.BalabanFinitePositiveWeightNormalizationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFinitePositiveWeightNormalizationExact as N

positiveMassClosed :
  N.finitePositiveMassCompilerLevel ≡ machineChecked
positiveMassClosed = refl

normalizationClosed :
  N.finiteWeightNormalizationCompilerLevel ≡ machineChecked
normalizationClosed = refl
