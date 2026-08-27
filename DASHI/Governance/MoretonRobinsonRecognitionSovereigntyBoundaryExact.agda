module DASHI.Governance.MoretonRobinsonRecognitionSovereigntyBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Core.RecognitionConstitutionNonfactorabilityExact as Recognition
import DASHI.Governance.IndigenousAuthoritySourceRegistryExact as Sources

------------------------------------------------------------------------
-- AILEEN MORETON-ROBINSON: RECOGNITION / SOVEREIGNTY BOUNDARY
--
-- Source: Aileen Moreton-Robinson, The White Possessive: Property, Power,
-- and Indigenous Sovereignty, University of Minnesota Press (2015),
-- DOI 10.5749/minnesota/9780816692149.001.0001,
-- print ISBN 9780816692149.
--
-- Bounded conceptual role only.  This is not a live native-title opinion and
-- does not claim the source author states DASHI's finite algebra.
------------------------------------------------------------------------

data Standing : Set where
  exteriorIndigenousStanding settlerConferredStanding : Standing

data SettlerRecognition : Set where
  notRecognized recognized : SettlerRecognition

data SovereignAuthority : Set where
  sovereignAuthority noSovereignAuthority : SovereignAuthority

settlerObserver : Standing → SettlerRecognition
settlerObserver exteriorIndigenousStanding = notRecognized
settlerObserver settlerConferredStanding = notRecognized

authorityObserver : Standing → SovereignAuthority
authorityObserver exteriorIndigenousStanding = sovereignAuthority
authorityObserver settlerConferredStanding = noSovereignAuthority

recognitionSystem : Recognition.RecognitionSystem Standing SettlerRecognition SovereignAuthority
recognitionSystem = Recognition.recognitionSystem settlerObserver authorityObserver

sameSettlerRecognition :
  settlerObserver exteriorIndigenousStanding ≡ settlerObserver settlerConferredStanding
sameSettlerRecognition = refl

differentAuthority :
  authorityObserver exteriorIndigenousStanding ≡ authorityObserver settlerConferredStanding → ⊥
differentAuthority ()

sovereigntyRecognitionCollision : Recognition.RecognitionCollision recognitionSystem
sovereigntyRecognitionCollision =
  Recognition.recognitionCollision
    exteriorIndigenousStanding settlerConferredStanding refl (λ ())

settlerRecognitionCannotExhaustSovereignAuthority :
  Recognition.FactorsThroughRecognition recognitionSystem → ⊥
settlerRecognitionCannotExhaustSovereignAuthority =
  Recognition.collisionBlocksAuthorityFactorization sovereigntyRecognitionCollision

moretonRobinsonSource : Sources.SourceReference
moretonRobinsonSource = Sources.moretonRobinson2015

record MoretonRobinsonBoundary : Set where
  constructor moretonRobinsonBoundary
  field
    settlerRecognitionConstitutesIndigenousSovereignty : Bool
    settlerRecognitionConstitutesIndigenousSovereigntyIsFalse :
      settlerRecognitionConstitutesIndigenousSovereignty ≡ false
    lackOfSettlerRecognitionProvesNoIndigenousAuthority : Bool
    lackOfSettlerRecognitionProvesNoIndigenousAuthorityIsFalse :
      lackOfSettlerRecognitionProvesNoIndigenousAuthority ≡ false
    settlerLegalObserverExhaustsSovereignty : Bool
    settlerLegalObserverExhaustsSovereigntyIsFalse :
      settlerLegalObserverExhaustsSovereignty ≡ false
    formalWitnessIsEmpiricalAustralianLegalFinding : Bool
    formalWitnessIsEmpiricalAustralianLegalFindingIsFalse :
      formalWitnessIsEmpiricalAustralianLegalFinding ≡ false

canonicalMoretonRobinsonBoundary : MoretonRobinsonBoundary
canonicalMoretonRobinsonBoundary =
  moretonRobinsonBoundary false refl false refl false refl false refl
