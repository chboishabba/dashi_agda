module DASHI.Physics.YangMills.YMClayContinuumConstructionSameObjectBridgeValidation where

------------------------------------------------------------------------
-- Regression for the literal A continuum bridge.
--
-- The positive theorem is the compiler itself.  The status witnesses below pin
-- the authority boundary: generic OS-limit assembly is machine-checked, while
-- the physical same-object attachment to the literal Y remains conditional.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayContinuumConstructionSameObjectBridgeExact as Bridge

compilerStaysMachineChecked :
  Bridge.continuumOSConstructionCompilerLevel ≡ machineChecked
compilerStaysMachineChecked = refl

physicalAttachmentStaysConditional :
  Bridge.literalContinuumSameObjectAttachmentLevel ≡ conditional
physicalAttachmentStaysConditional = refl
