module DASHI.Wikimedia.MaboWorldObjectIdentityValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Wikimedia.MaboWorldObjectIdentityExact

eddieIdentityClassPinned :
  identityClassReference eddieMaboIdentity ≡ "world-object:eddie-mabo"
eddieIdentityClassPinned = refl

eddieQidPinned :
  qidRepresentation eddieMaboIdentity ≡ "Q975866"
eddieQidPinned = refl

eddieArticlePinned :
  articleRepresentation eddieMaboIdentity ≡ "https://en.wikipedia.org/wiki/Eddie_Mabo"
eddieArticlePinned = refl

maboParticipantCandidateCountsByIdentityClass :
  countingIdentityClass maboEddieParticipantResolution ≡ "world-object:eddie-mabo"
maboParticipantCandidateCountsByIdentityClass = refl

maboParticipantResolutionCandidateOnly :
  candidateOnly maboEddieParticipantResolution ≡ true
maboParticipantResolutionCandidateOnly = refl
