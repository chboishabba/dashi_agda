module DASHI.Physics.YangMills.BalabanClayGate4EmbeddedWeightedQuadratureValidation where
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4EmbeddedWeightedQuadratureExact as W
weightedQuadratureCompilerOwned : W.embeddedWeightedGate4QuadratureLevel ≡ machineChecked
weightedQuadratureCompilerOwned = refl
taggedGate4CompilerOwned : W.massExactTaggedGate4CompilerLevel ≡ machineChecked
taggedGate4CompilerOwned = refl
haarCellMassStillPhysical : W.literalGate4QuadratureMassIsHaarCellMassLevel ≡ conditional
haarCellMassStillPhysical = refl
fastFibreTagsStillPhysical : W.literalGate4FastFibreIsTaggedProductSU2Level ≡ conditional
fastFibreTagsStillPhysical = refl
tagValueStillPhysical : W.literalEquation171TagValueIsGate4OneIntegrandLevel ≡ conditional
tagValueStillPhysical = refl
