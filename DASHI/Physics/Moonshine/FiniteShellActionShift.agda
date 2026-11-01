module DASHI.Physics.Moonshine.FiniteShellActionShift where

open import Data.Bool using (true)
open import Data.Vec using ([]; _∷_)

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.Moonshine.FiniteShellAction as FSA
open import DASHI.Physics.OrbitProfileComputedSignedPerm as OPCSP
open import DASHI.Physics.SignedPerm4 as SP

shiftShellAction : FSA.FiniteShellAction (Data.Vec.Vec Trit 4) SP.SignedPerm4
shiftShellAction =
  record
    { shell1States = OPCSP.shellList 1
    ; shell2States = OPCSP.shellList 2
    ; groupElements = OPCSP.allSignedPerm4
    ; act = OPCSP.actSigned4
    ; decEqA = OPCSP.decEqVec
    }

shiftIdentityTwiner : SP.SignedPerm4
shiftIdentityTwiner =
  record
    { perm = SP.p012
    ; flipT = true
    ; flipS = true ∷ true ∷ true ∷ []
    }

shiftNontrivialTwiner : SP.SignedPerm4
shiftNontrivialTwiner =
  record
    { perm = SP.p021
    ; flipT = true
    ; flipS = true ∷ true ∷ true ∷ []
    }
