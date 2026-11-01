module DASHI.Physics.Moonshine.FiniteTwinedShellTraceRootSystemB4 where

open import Data.Maybe using (nothing)
open import Data.List.Base using (length)

open import DASHI.Physics.Moonshine.FiniteShellActionRootSystemB4 as FSAB4
open import DASHI.Physics.Moonshine.FiniteTwinedShellTrace as FTST
open import DASHI.Physics.RootSystemB4Carrier as B4

b4IdentityTwinedTrace : FTST.FiniteTwinedShellTrace
b4IdentityTwinedTrace =
  FTST.identityTwinedTrace
    nothing
    (length B4.shell1Points)
    (length B4.shell2Points)

b4NontrivialTwinedTrace : FTST.FiniteTwinedShellTrace
b4NontrivialTwinedTrace =
  FTST.twinedTraceFromAction FSAB4.b4ShellAction nothing FSAB4.b4NontrivialTwiner
