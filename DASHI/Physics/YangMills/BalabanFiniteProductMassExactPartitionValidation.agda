module DASHI.Physics.YangMills.BalabanFiniteProductMassExactPartitionValidation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteProductMassExactPartitionExact as P
productPartitionCompilerOwned : P.productMassExactPartitionCompilerLevel ≡ machineChecked
productPartitionCompilerOwned = refl
productNormalizationCompilerOwned : P.productMassNormalizationCompilerLevel ≡ machineChecked
productNormalizationCompilerOwned = refl
oneSiteSU2PartitionStillPhysical : P.literalOneSiteSU2MassPartitionLevel ≡ conditional
oneSiteSU2PartitionStillPhysical = refl
