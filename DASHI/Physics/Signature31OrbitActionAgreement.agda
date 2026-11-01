module DASHI.Physics.Signature31OrbitActionAgreement where

open import Data.Vec using (Vec; _∷_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Algebra.Trit using (Trit; inv)
open import DASHI.Physics.SignedPerm4 as SP
open import DASHI.Physics.OrbitProfileComputedSignedPerm as OPCSP

-- Trit-level action induced by SignedPerm4.
actIso4Trit : SP.SignedPerm4 → Vec Trit 4 → Vec Trit 4
actIso4Trit sp x = OPCSP.actSigned4 sp x

-- Agreement lemma: computed orbit action equals the induced SignedPerm4 action.
actSigned4≡actIso4Trit :
  ∀ sp x → OPCSP.actSigned4 sp x ≡ actIso4Trit sp x
actSigned4≡actIso4Trit _ _ = refl
