module DASHI.Foundations.AdmissibilityConcentrationRegression where

open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)

open import DASHI.Foundations.BidirectionalAdmissibilityGalois
open import DASHI.Foundations.UltrametricAdmissibilityConcentration
open import DASHI.Physics.Closure.QuantumDecoherenceAdmissibilityConcentration

------------------------------------------------------------------------
-- Compact aggregate surface for the new lane.

unitPred : Pred ⊤
unitPred _ = ⊤

unitRel : Rel ⊤ ⊤
unitRel _ _ = ⊤

unitForward : Forward unitRel unitPred tt
unitForward = tt , (tt , tt)

unitSafe : SafePullback unitRel unitPred tt
unitSafe _ = tt

unitBidirectional : BidirectionallyCompatible unitRel unitPred unitPred tt
unitBidirectional = tt , unitSafe

unitMacroWitness : MacroWitness unitRel unitPred
unitMacroWitness _ = tt , (unitSafe , tt)

unitStableBranch : GaloisStableBranch unitRel unitPred
unitStableBranch = record { witnessed = unitMacroWitness }

unitBranchClosed :
  (unitPred ⊆ MacroKernel unitRel unitPred)
  ×
  (MacroKernel unitRel unitPred ⊆ unitPred)
unitBranchClosed =
  stableBranch-forward unitStableBranch
  ,
  stableBranch-backward unitStableBranch
