module DASHI.Physics.Moonshine.FiniteTwinerLibraryShift where

open import Agda.Builtin.String using (String)
open import Data.Maybe using (just)
open import Data.Bool using (false; true)
open import Data.Vec using (_∷_; [])

open import DASHI.Physics.Moonshine.FiniteShellActionShift as FSAS
open import DASHI.Physics.Moonshine.FiniteTwinedShellTrace as FTST
open import DASHI.Physics.Moonshine.FiniteTwinedShellTraceShift as FTSTS
open import DASHI.Physics.SignedPerm4 as SP

record LabeledTwinedTrace : Set where
  field
    label : String
    trace : FTST.FiniteTwinedShellTrace

shiftTwinerIdentity : LabeledTwinedTrace
shiftTwinerIdentity =
  record
    { label = "identity"
    ; trace = FTSTS.shiftIdentityTwinedTrace
    }

shiftTwinerPerm021 : LabeledTwinedTrace
shiftTwinerPerm021 =
  record
    { label = "perm021"
    ; trace = FTSTS.shiftNontrivialTwinedTrace
    }

shiftTwinerFlipT : LabeledTwinedTrace
shiftTwinerFlipT =
  record
    { label = "flipT"
    ; trace =
        FTST.twinedTraceFromAction
          FSAS.shiftShellAction
          (just 31)
          (record
            { perm = SP.p012
            ; flipT = false
            ; flipS = true ∷ true ∷ true ∷ []
            })
    }

shiftTwinerPerm120 : LabeledTwinedTrace
shiftTwinerPerm120 =
  record
    { label = "perm120"
    ; trace =
        FTST.twinedTraceFromAction
          FSAS.shiftShellAction
          (just 31)
          (record
            { perm = SP.p120
            ; flipT = true
            ; flipS = true ∷ true ∷ true ∷ []
            })
    }

shiftTwinerFlipSpace : LabeledTwinedTrace
shiftTwinerFlipSpace =
  record
    { label = "flipSpace"
    ; trace =
        FTST.twinedTraceFromAction
          FSAS.shiftShellAction
          (just 31)
          (record
            { perm = SP.p012
            ; flipT = true
            ; flipS = false ∷ true ∷ false ∷ []
            })
    }
