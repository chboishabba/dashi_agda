module DASHI.Physics.OrbitProfileExternal where

open import Agda.Builtin.Nat using (Nat)
open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)

open import DASHI.Physics.DimensionBoundAssumptions as DBA
open import DASHI.Physics.ShellOrbitProfileGenerator as SOPG
open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Geometry.ConeArrowIsotropyOrbitProfile as CAOP
open import DASHI.Physics.ConeArrowIsotropyOrbitProfileAgreement as CAOPA
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD

-- CSV-backed signed-block profiles for m = 4 (p+q = 4), shells |Q|=1,2.
-- These match the current isotropy action (signed permutations within blocks).

orbitProfile-p4q0-shell1 : DBA.ShellOrbitProfile 4
orbitProfile-p4q0-shell1 = SOPG.profileFromSorted {m = 4} OPD.shell1_p4_q0

orbitProfile-p4q0-shell2 : DBA.ShellOrbitProfile 4
orbitProfile-p4q0-shell2 = SOPG.profileFromSorted {m = 4} OPD.shell2_p4_q0

orbitProfile-p3q1-shell1 : DBA.ShellOrbitProfile 4
orbitProfile-p3q1-shell1 = SOPG.profileFromSorted {m = 4} OPD.shell1_p3_q1

orbitProfile-p3q1-shell2 : DBA.ShellOrbitProfile 4
orbitProfile-p3q1-shell2 = SOPG.profileFromSorted {m = 4} OPD.shell2_p3_q1

orbitProfile-p2q2-shell1 : DBA.ShellOrbitProfile 4
orbitProfile-p2q2-shell1 = SOPG.profileFromSorted {m = 4} OPD.shell1_p2_q2

orbitProfile-p2q2-shell2 : DBA.ShellOrbitProfile 4
orbitProfile-p2q2-shell2 = SOPG.profileFromSorted {m = 4} OPD.shell2_p2_q2

orbitProfile-p1q3-shell1 : DBA.ShellOrbitProfile 4
orbitProfile-p1q3-shell1 = SOPG.profileFromSorted {m = 4} OPD.shell1_p1_q3

orbitProfile-p1q3-shell2 : DBA.ShellOrbitProfile 4
orbitProfile-p1q3-shell2 = SOPG.profileFromSorted {m = 4} OPD.shell2_p1_q3

orbitProfile-p0q4-shell1 : DBA.ShellOrbitProfile 4
orbitProfile-p0q4-shell1 = SOPG.profileFromSorted {m = 4} OPD.shell1_p0_q4

orbitProfile-p0q4-shell2 : DBA.ShellOrbitProfile 4
orbitProfile-p0q4-shell2 = SOPG.profileFromSorted {m = 4} OPD.shell2_p0_q4

-- Canonical profile pipeline exported for signature discrimination consumers.
record CanonicalOrbitProfilePipeline : Set where
  field
    measuredProfile : OSD.Profile
    forcedProfile : OSD.Profile
    measured≡forced : measuredProfile ≡ forcedProfile
    measured≡discriminantMeasured :
      measuredProfile ≡ OSD.MeasuredProfile

canonicalMeasuredProfile : OSD.Profile
canonicalMeasuredProfile = CAOP.toProfile CAOPA.abstractProfile

canonicalForcedProfile : OSD.Profile
canonicalForcedProfile = OSD.ProfileOf OSD.sig31

canonicalMeasured≡forced : canonicalMeasuredProfile ≡ canonicalForcedProfile
canonicalMeasured≡forced = CAOPA.abstractMeasured≡ProfileOfSig31

canonicalMeasured≡discriminantMeasured :
  canonicalMeasuredProfile ≡ OSD.MeasuredProfile
canonicalMeasured≡discriminantMeasured =
  trans
    canonicalMeasured≡forced
    (sym OSD.measured-profile-def)

canonicalOrbitProfilePipeline : CanonicalOrbitProfilePipeline
canonicalOrbitProfilePipeline =
  record
    { measuredProfile = canonicalMeasuredProfile
    ; forcedProfile = canonicalForcedProfile
    ; measured≡forced = canonicalMeasured≡forced
    ; measured≡discriminantMeasured = canonicalMeasured≡discriminantMeasured
    }
