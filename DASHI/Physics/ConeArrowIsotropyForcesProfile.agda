module DASHI.Physics.ConeArrowIsotropyForcesProfile where

open import Agda.Primitive using (Setω)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)
open import DASHI.Geometry.ConeTimeIsotropy as CTI

-- A single seam: cone+arrow+isotropy forces a profile.
record ConeArrowIsotropyForcesProfile {X : Set} (C : CTI.ConeStructure X)
  (A : CTI.TimeArrow X) (I : CTI.IsotropyAction X) (Profile : Set) : Setω where
  field
    measuredProfile : Profile
    forcedProfile   : Profile
    measured≡forced : measuredProfile ≡ forcedProfile

open ConeArrowIsotropyForcesProfile public

mkConeArrowIsotropyForcesProfile :
  {X : Set} →
  {C : CTI.ConeStructure X} →
  {A : CTI.TimeArrow X} →
  {I : CTI.IsotropyAction X} →
  {Profile : Set} →
  (measured forced : Profile) →
  measured ≡ forced →
  ConeArrowIsotropyForcesProfile C A I Profile
mkConeArrowIsotropyForcesProfile measured forced eq =
  record
    { measuredProfile = measured
    ; forcedProfile = forced
    ; measured≡forced = eq
    }

forced≡measured :
  {X : Set} →
  {C : CTI.ConeStructure X} →
  {A : CTI.TimeArrow X} →
  {I : CTI.IsotropyAction X} →
  {Profile : Set} →
  (p : ConeArrowIsotropyForcesProfile C A I Profile) →
  forcedProfile p ≡ measuredProfile p
forced≡measured p = sym (measured≡forced p)
