module DASHI.Physics.Moonshine.FiniteTwinedShellTraceShift where

open import Data.Maybe using (just)
open import Data.List.Base using (length)

open import DASHI.Physics.Moonshine.FiniteShellActionShift as FSAS
open import DASHI.Physics.Moonshine.FiniteTwinedShellTrace as FTST
open import DASHI.Physics.OrbitProfileComputedSignedPerm as OPCSP

shiftIdentityTwinedTrace : FTST.FiniteTwinedShellTrace
shiftIdentityTwinedTrace =
  FTST.identityTwinedTrace
    (just 31)
    (length (OPCSP.shellList 1))
    (length (OPCSP.shellList 2))

shiftNontrivialTwinedTrace : FTST.FiniteTwinedShellTrace
shiftNontrivialTwinedTrace =
  FTST.twinedTraceFromAction FSAS.shiftShellAction (just 31) FSAS.shiftNontrivialTwiner
