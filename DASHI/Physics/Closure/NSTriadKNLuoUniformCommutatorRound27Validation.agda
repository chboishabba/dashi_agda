module DASHI.Physics.Closure.NSTriadKNLuoUniformCommutatorRound27Validation where

import DASHI.Physics.Closure.NSTriadKNLuoGalerkinCriticalLedgerRound26Validation
import DASHI.Physics.Closure.NSTriadKNLuoUniformCommutatorTaxRound27Exact as Tax
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyContinuationRound27Exact as Continuation

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _*_)

finiteTaxIsCutoffIndependent :
  (cells : List Tax.DyadicCommutatorTaxCell) →
  Tax.sumShellCommutatorTax cells
  ≡ Tax.sumMotherCommutatorTax cells
finiteTaxIsCutoffIndependent =
  Tax.finiteCutoffIndependentCommutatorTax

halfDoubleCoefficientCancelsExactly :
  (moment low high tested : ℚ) →
  Tax.shellCommutatorTax
    (Tax.cellAtScale Tax.halfDoubleScalePair moment low high tested)
  ≡ moment * low * high * tested
halfDoubleCoefficientCancelsExactly = Tax.halfDoubleTaxIsMotherTax

energyIdentityFeedsContinuation :
  (trajectory : Continuation.FiniteGalerkinEnergyTrajectory) →
  (time : Continuation.Time trajectory) →
  Continuation.EnergyBoundWitness trajectory time
energyIdentityFeedsContinuation =
  Continuation.energyIdentityConstructsBoundWitness
