{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedR406ChargedLocalisationRound424Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116SelectedR406ChargedLocalisationRound424Exact as R424
open import DASHI.Physics.YangMills.CompactLieProofLevel

finiteCarrierTransportMachineChecked :
  R424.round424FiniteCarrierTransportLevel ≡ machineChecked
finiteCarrierTransportMachineChecked = refl

existingCMP116SummabilityImported :
  R424.round424CMP116SummabilityTheoremLevel ≡ standardImported
existingCMP116SummabilityImported = refl

freshResidualSummabilityTheoremPruned :
  R424.round424FreshResidualSummabilityTheoremRequired ≡ false
freshResidualSummabilityTheoremPruned = refl
