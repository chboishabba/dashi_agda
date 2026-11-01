module DASHI.Physics.YangMills.BalabanRealVanishingFiniteAlgebraValidation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanRealVanishingFiniteAlgebraExact as V
finiteVanishingAlgebraImported : V.realVanishingFiniteAlgebraLevel ≡ standardImported
finiteVanishingAlgebraImported = refl
