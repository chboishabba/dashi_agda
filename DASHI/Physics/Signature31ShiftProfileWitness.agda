module DASHI.Physics.Signature31ShiftProfileWitness where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)
open import Data.List using ([]; _∷_)

open import DASHI.Physics.OrbitProfileComputedSignedPerm as OPCSP
open import DASHI.Physics.OrbitProfileComputedSignedPermEvidence as OPCE
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD

-- Witness layer for the current headline theorem.
-- This module does not claim cone-forcing; it only packages the concrete orbit
-- profile computed from the 4D signed-permutation shift action.

-- Concrete profile built from the internal signed-permutation orbit computation.
computedProfile : OSD.Profile
computedProfile =
  OSD.append3
    (31 ∷ [])
    OPCSP.shell1_p3_q1_computed
    OPCSP.shell2_p3_q1_computed

-- The measured profile alias is now definitionally the computed profile.
measured≡computed : OSD.MeasuredProfile ≡ computedProfile
measured≡computed = refl

-- The computed profile picks out sig31 among the 4D candidates.
computed≡sig31Profile : computedProfile ≡ OSD.ProfileOf OSD.sig31
computed≡sig31Profile =
  trans
    (sym measured≡computed)
    OPCE.measuredProfileFromComputed
  where
    sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl
