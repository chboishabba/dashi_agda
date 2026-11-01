module DASHI.Physics.Moonshine.FiniteShellActionRootSystemB4 where

open import Data.Bool using (true)
open import Data.Vec using ([]; _∷_)

open import DASHI.Physics.Moonshine.FiniteShellAction as FSA
open import DASHI.Physics.RootSystemB4Carrier as B4
open import DASHI.Physics.RootSystemB4WeylAction as W

b4ShellAction : FSA.FiniteShellAction B4.B4Point W.WeylB4
b4ShellAction =
  record
    { shell1States = B4.shell1Points
    ; shell2States = B4.shell2Points
    ; groupElements = W.allWeylB4
    ; act = W.actWeyl
    ; decEqA = B4.decEqB4Point
    }

b4IdentityTwiner : W.WeylB4
b4IdentityTwiner =
  record
    { perm = W.p0123
    ; flips = true ∷ true ∷ true ∷ true ∷ []
    }

b4NontrivialTwiner : W.WeylB4
b4NontrivialTwiner =
  record
    { perm = W.p0132
    ; flips = true ∷ true ∷ true ∷ true ∷ []
    }
