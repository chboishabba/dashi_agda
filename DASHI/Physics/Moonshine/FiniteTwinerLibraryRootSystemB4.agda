module DASHI.Physics.Moonshine.FiniteTwinerLibraryRootSystemB4 where

open import Agda.Builtin.String using (String)
open import Data.Bool using (true; false)
open import Data.Vec using (_∷_; [])
open import Data.Maybe using (nothing)

open import DASHI.Physics.Moonshine.FiniteShellActionRootSystemB4 as FSAB4
open import DASHI.Physics.Moonshine.FiniteTwinedShellTrace as FTST
open import DASHI.Physics.Moonshine.FiniteTwinedShellTraceRootSystemB4 as FTSTB4
open import DASHI.Physics.RootSystemB4WeylAction as W

record LabeledTwinedTrace : Set where
  field
    label : String
    trace : FTST.FiniteTwinedShellTrace

b4TwinerIdentity : LabeledTwinedTrace
b4TwinerIdentity =
  record
    { label = "identity"
    ; trace = FTSTB4.b4IdentityTwinedTrace
    }

b4TwinerPerm0132 : LabeledTwinedTrace
b4TwinerPerm0132 =
  record
    { label = "perm0132"
    ; trace = FTSTB4.b4NontrivialTwinedTrace
    }

b4TwinerFlip1 : LabeledTwinedTrace
b4TwinerFlip1 =
  record
    { label = "flip1"
    ; trace =
        FTST.twinedTraceFromAction
          FSAB4.b4ShellAction
          nothing
          (record
            { perm = W.p0123
            ; flips = false ∷ true ∷ true ∷ true ∷ []
            })
    }

b4TwinerPerm1203 : LabeledTwinedTrace
b4TwinerPerm1203 =
  record
    { label = "perm1203"
    ; trace =
        FTST.twinedTraceFromAction
          FSAB4.b4ShellAction
          nothing
          (record
            { perm = W.p1203
            ; flips = true ∷ true ∷ true ∷ true ∷ []
            })
    }

b4TwinerFlipAll : LabeledTwinedTrace
b4TwinerFlipAll =
  record
    { label = "flipAll"
    ; trace =
        FTST.twinedTraceFromAction
          FSAB4.b4ShellAction
          nothing
          (record
            { perm = W.p0123
            ; flips = false ∷ false ∷ false ∷ false ∷ []
            })
    }
