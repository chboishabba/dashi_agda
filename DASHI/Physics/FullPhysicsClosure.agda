module DASHI.Physics.FullPhysicsClosure where

open import DASHI.Physics.GlobalDimensionUniqueness as GDU
open import DASHI.Physics.FiniteToContinuumGeometry as FCG
open import DASHI.Physics.BianchiLovelockCompletion as BLC
open import DASHI.Physics.CliffordRepresentationCompletion as CRC
open import DASHI.Physics.SpinDoubleCoverCompletion as SDC
open import DASHI.Physics.CCRContinuumCompletion as CCC
open import DASHI.Physics.UnitaryCompletion as UC
open import DASHI.Physics.StandardModelUniqueness as SMU

record FullPhysicsClosure : Set₁ where
  field
    dimension : GDU.GlobalDimensionClosure
    continuum : FCG.ContinuumLorentzClosure
    einstein  : BLC.EinsteinContinuumClosure
    clifford  : CRC.CliffordExistence
    spin      : SDC.SpinDoubleCoverRealization
    ccr       : CCC.CCRContinuumClosure
    unitary   : UC.UnitaryCompletionClosure
    standardModel : SMU.StandardModelCharacterization

open FullPhysicsClosure public
