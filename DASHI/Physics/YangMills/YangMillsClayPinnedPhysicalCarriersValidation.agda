module DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as P

carrierConstructionCompilerOwned :
  P.physicalLiteralCarrierConstructionLevel ≡ machineChecked
carrierConstructionCompilerOwned = refl

finiteMeasureMeaningCompilerOwned :
  P.physicalFiniteMeasureMeaningLevel ≡ machineChecked
finiteMeasureMeaningCompilerOwned = refl

continuumMeasureMeaningCompilerOwned :
  P.physicalContinuumMeasureMeaningLevel ≡ machineChecked
continuumMeasureMeaningCompilerOwned = refl

schwingerMeaningCompilerOwned :
  P.physicalSchwingerMeaningLevel ≡ machineChecked
schwingerMeaningCompilerOwned = refl
