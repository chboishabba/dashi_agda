module DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as L

standardLimitPrincipleImported :
  L.realSequenceLimitByVanishingErrorLevel ≡ standardImported
standardLimitPrincipleImported = refl
