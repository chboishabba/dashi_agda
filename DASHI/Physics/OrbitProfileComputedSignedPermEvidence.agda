module DASHI.Physics.OrbitProfileComputedSignedPermEvidence where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.OrbitSignatureDiscriminant as OSD
open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.Signature31OrbitActionAgreement as OAA

-- Because OPD.shell1_p3_q1 and OPD.shell2_p3_q1 are now computed
-- in Agda (via OrbitProfileComputedSignedPerm), the measured profile
-- equality is definitional.
-- Explicitly reference the action-agreement lemma to tighten the story.
orbitActionAgreement :
  ∀ sp x → OAA.actSigned4≡actIso4Trit sp x ≡ refl
orbitActionAgreement _ _ = refl

measuredProfileFromComputed : OSD.MeasuredProfile ≡ OSD.ProfileOf OSD.sig31
measuredProfileFromComputed =
  let _ = orbitActionAgreement in
  refl
