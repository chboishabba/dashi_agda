module DASHI.Physics.YangMills.BalabanEmbeddedCanonicalRationalConstrainedFoldValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanEmbeddedCanonicalRationalConstrainedFoldExact as E

embeddedConstrainedFoldCompilerOwned :
  E.embeddedCanonicalRationalConstrainedFoldLevel ≡ machineChecked
embeddedConstrainedFoldCompilerOwned = refl
