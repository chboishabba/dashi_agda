module DASHI.Physics.ConeArrowIsotropyForcesProfileShiftInstance where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.Signature31FromConeArrowIsotropy as S31
open import DASHI.Physics.ConeArrowIsotropyForcesProfile as CAF
open import DASHI.Physics.OrbitProfileExternal as OPE
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD
open import DASHI.Physics.Signature31InstanceShiftZ as S31Z

-- Shift instance witness only:
-- this packages the concrete computed profile used by the signature theorem.
-- It should not be read as a completed proof that arbitrary cone/arrow/isotropy
-- data intrinsically force that profile.
shiftForcesProfile :
  CAF.ConeArrowIsotropyForcesProfile
    (S31.SignatureAxioms.ConeS S31Z.sigAxioms)
    (S31.SignatureAxioms.Arrow S31Z.sigAxioms)
    (S31.SignatureAxioms.Iso S31Z.sigAxioms)
    OSD.Profile
shiftForcesProfile =
  let
    pipeline = OPE.canonicalOrbitProfilePipeline
  in
  record
    { measuredProfile =
        OPE.CanonicalOrbitProfilePipeline.measuredProfile pipeline
    ; forcedProfile =
        OPE.CanonicalOrbitProfilePipeline.forcedProfile pipeline
    ; measured≡forced =
        OPE.CanonicalOrbitProfilePipeline.measured≡forced pipeline
    }

shiftMeasuredProfile :
  OSD.Profile
shiftMeasuredProfile =
  CAF.ConeArrowIsotropyForcesProfile.measuredProfile shiftForcesProfile

shiftForcedProfile :
  OSD.Profile
shiftForcedProfile =
  CAF.ConeArrowIsotropyForcesProfile.forcedProfile shiftForcesProfile

shiftMeasured≡forced :
  shiftMeasuredProfile ≡ shiftForcedProfile
shiftMeasured≡forced =
  CAF.ConeArrowIsotropyForcesProfile.measured≡forced shiftForcesProfile

shiftSignatureForced31 :
  ∀ s →
  shiftMeasuredProfile ≡ OSD.ProfileOf s →
  s ≡ OSD.sig31
shiftSignatureForced31 =
  OSD.SignatureFromMeasuredProfileUnique
