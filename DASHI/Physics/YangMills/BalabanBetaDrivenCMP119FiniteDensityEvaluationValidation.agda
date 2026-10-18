module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119FiniteDensityEvaluationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119FiniteDensityEvaluationExact as Eval

familyEvaluationCompilerOwned :
  Eval.betaDrivenCMP119FiniteDensityEvaluationCompilerLevel ≡ machineChecked
familyEvaluationCompilerOwned = refl

everyScaleSourceEvaluationCompilerOwned :
  Eval.betaDrivenCMP119EveryScaleSourceEvaluationLevel ≡ machineChecked
everyScaleSourceEvaluationCompilerOwned = refl

downstreamAssemblyCompilerOwned :
  Eval.betaDrivenCMP119DownstreamAssemblyCompilerLevel ≡ machineChecked
downstreamAssemblyCompilerOwned = refl

literalFamilyEvaluationStillPhysical :
  Eval.literalBetaDrivenCMP119FiniteDensityEvaluationLevel ≡ conditional
literalFamilyEvaluationStillPhysical = refl
