module DASHI.Papers.NavierStokes.ClaimCorpusHighestAlphaRound24 where

------------------------------------------------------------------------
-- Paper-facing status surface for Round 24.
--
-- Claimed and conditional solution papers are retained as auditable source
-- objects.  Two exact countermodels are present.  The dependency-ordered Clay
-- ladder is explicit.  No source claim or repository status flag is permitted
-- to inhabit the physical theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoClaimedSolutionCorpusRound24Exact as Corpus
import DASHI.Physics.Closure.NSTriadKNLuoAbuGhuwalehAdditiveFloorNoGoExact as Abu
import DASHI.Physics.Closure.NSTriadKNLuoCamlinTemporalLiftNoGoExact as Camlin
import DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaClayLemmaLadderRound24Exact as Ladder
import DASHI.Physics.Closure.NSTriadKNLuoClaimRouteCrosswalkRound24Exact as Crosswalk

record ClaimCorpusHighestAlphaRound24Status : Set where
  constructor claimCorpusHighestAlphaRound24Status
  field
    broadClaimCorpusRecorded : Bool
    corpusDeclaredExhaustive : Bool
    additiveFloorCountermodelConstructed : Bool
    finiteHorizonCountermodelConstructed : Bool
    timeChangeIntegralInvarianceConstructed : Bool
    claimedRoutesCrosswalkedToPhysicalLemmas : Bool
    highestAlphaLadderNormalized : Bool
    allPhysicalProducersInhabited : Bool
    unconditionalClayTheoremPromoted : Bool

open ClaimCorpusHighestAlphaRound24Status public

canonicalClaimCorpusHighestAlphaRound24Status :
  ClaimCorpusHighestAlphaRound24Status
canonicalClaimCorpusHighestAlphaRound24Status =
  claimCorpusHighestAlphaRound24Status
    true false true true true true true false false

claimCorpusIsNotProofAuthority :
  Corpus.allCorpusSourcesAreProofAuthorities ≡ false
claimCorpusIsNotProofAuthority = refl

claimCorpusSearchNotDeclaredExhaustive :
  Corpus.corpusSearchIsDeclaredExhaustive ≡ false
claimCorpusSearchNotDeclaredExhaustive = refl

physicalProducersRemainOpen :
  allPhysicalProducersInhabited
    canonicalClaimCorpusHighestAlphaRound24Status
  ≡ false
physicalProducersRemainOpen = refl

clayPromotionRemainsFalse :
  unconditionalClayTheoremPromoted
    canonicalClaimCorpusHighestAlphaRound24Status
  ≡ false
clayPromotionRemainsFalse = refl

highestAlphaLadder : Ladder.HighestAlphaClayLemmaLadder
highestAlphaLadder = Ladder.canonicalHighestAlphaClayLemmaLadder

abuNoGo : Abu.AdditiveFloorNoGoWitness
abuNoGo = Abu.canonicalAdditiveFloorNoGoWitness

camlinFiniteHorizonNoGo :
  ¬ Camlin.GlobalUniformHorizonBound
camlinFiniteHorizonNoGo =
  Camlin.finiteHorizonFamilyDoesNotYieldGlobalUniformBound
  where
  open import Relation.Nullary.Negation using (¬_)

abuRouteNode : Crosswalk.LadderNode
abuRouteNode = Crosswalk.firstLoadBearingNode (Corpus.family Corpus.abuGhuwaleh)
