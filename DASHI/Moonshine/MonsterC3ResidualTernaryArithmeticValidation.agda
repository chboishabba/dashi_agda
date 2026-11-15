module DASHI.Moonshine.MonsterC3ResidualTernaryArithmeticValidation where

open import DASHI.Core.Prelude
import DASHI.Moonshine.MonsterC3ResidualTernaryArithmeticExact as Target

residual53IsTernaryNeighbour :
  Target.residual53FromTernaryNeighbour ≡ 53
residual53IsTernaryNeighbour = refl

ogg71IsExtendedTernaryNeighbour :
  Target.ogg71FromExtendedTernaryNeighbour ≡ 71
ogg71IsExtendedTernaryNeighbour = refl

monsterDegreeFactorisesThrough71 :
  Target.oggTripleProduct ≡ 196883
monsterDegreeFactorisesThrough71 = refl

residual53MatchesCertified3B :
  Target.residual53FromTernaryNeighbour ≡ Target.certifiedMonster3BResidual
residual53MatchesCertified3B = refl

ogg71MatchesTrackedPrimeLane :
  Target.ogg71FromExtendedTernaryNeighbour ≡ Target.trackedOgg71
ogg71MatchesTrackedPrimeLane = refl

arithmeticCoincidenceDoesNotPromoteRepresentation :
  Target.TernaryResidualBoundary.arithmeticIdentityProvesRepresentationMeaning
    Target.canonicalTernaryResidualBoundary
  ≡ false
arithmeticCoincidenceDoesNotPromoteRepresentation = refl

arithmeticCoincidenceDoesNotPromoteGravity :
  Target.TernaryResidualBoundary.arithmeticIdentityProvesGravity
    Target.canonicalTernaryResidualBoundary
  ≡ false
arithmeticCoincidenceDoesNotPromoteGravity = refl
