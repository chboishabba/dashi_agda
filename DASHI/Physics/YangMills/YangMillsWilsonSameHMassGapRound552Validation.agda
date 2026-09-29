{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsWilsonSameHMassGapRound552Validation where
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsWilsonSameHMassGapRound552Exact as R552
open import DASHI.Physics.YangMills.CompactLieProofLevel
compilerMachineChecked : R552.round552WilsonClusteringToGapCompilerLevel ≡ machineChecked
compilerMachineChecked = refl
spectralTransferImported : R552.round552StandardHalfRateSpectralTransferLevel ≡ standardImported
spectralTransferImported = refl
