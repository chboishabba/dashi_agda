{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsExtensionalizedRepresentedOS05Round520Validation where
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsExtensionalizedRepresentedOS05Round520Exact as R520
open import DASHI.Physics.YangMills.CompactLieProofLevel
compiler : R520.round520ExtensionalClosureCompilerLevel ≡ machineChecked
compiler = refl
regularityNoAssumption : R520.literalRound520RegularityExtensionalityAssumptionRequired ≡ false
regularityNoAssumption = refl
growthNoAssumption : R520.literalRound520GrowthExtensionalityAssumptionRequired ≡ false
growthNoAssumption = refl
