module DASHI.Governance.SexedHistoricalReopenableSynthesisEndOfHistoryBoundaryExact where

------------------------------------------------------------------------
-- REOPENABLE DIALECTICAL JOIN / END-OF-HISTORY SOURCE BOUNDARY
--
-- This owner makes two things explicit and keeps them separate:
--
--   1. a source-attributed historical/philosophical "end of history" lane;
--   2. a repository-native DASHI theorem that a productive dialectical join in
--      the finite sexed-history fibre model remains reopenable.
--
-- The DASHI theorem is NOT attributed to Fukuyama, Kojeve, or Hegel.  Nor is
-- the finite reopenability witness presented as a mathematical refutation of
-- any source's philosophical thesis.  The sources below only identify bounded
-- roles against which the repository's claim boundary can be stated cleanly.
--
-- SOURCE ROLES
--
-- Francis Fukuyama, "The End of History?", The National Interest 16
-- (Summer 1989), 3--18, JSTOR stable 24027184.  Source role: the thesis of an
-- endpoint of ideological evolution, not the claim that chronological events
-- literally cease.
--
-- Francis Fukuyama, The End of History and the Last Man, Free Press, 1992,
-- ISBN 9780029109755.  Source role: the book-length liberal-democratic
-- culmination thesis developed from the earlier essay.
--
-- Alexandre Kojeve, Introduction to the Reading of Hegel, French lectures
-- published 1947; English translation 1969.  Source role: a distinctive
-- twentieth-century Hegel interpretation in which the struggle for recognition
-- can culminate in a post-historical condition.  This role is NOT treated as
-- identical with Hegel's own text or with Fukuyama's later political thesis.
--
-- Hegel is retained only as reception background here.  This module does not
-- claim that "the end of history" is a direct theorem-text of Hegel, nor that
-- Kojeve/Fukuyama exhaust Hegelian historiography.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Governance.SexedHistoricalProductiveDialecticalFibreJoinExact as Join

------------------------------------------------------------------------
-- 1. Source registry.  Roles are constructor-distinct so attribution cannot
--    silently slide from Fukuyama to Kojeve to Hegel or into DASHI.
------------------------------------------------------------------------

data EndOfHistorySourceRole : Set where
  fukuyama1989IdeologicalEndpoint
  fukuyama1992LiberalDemocraticCulmination
  kojeveRecognitionCompletionReading
  hegelReceptionBackgroundOnly
  : EndOfHistorySourceRole

record EndOfHistorySource : Set where
  constructor end-of-history-source
  field
    author : String
    title : String
    stableIdentifier : String
    sourceRole : EndOfHistorySourceRole

open EndOfHistorySource public

fukuyama1989Source : EndOfHistorySource
fukuyama1989Source =
  end-of-history-source
    "Francis Fukuyama"
    "The End of History?"
    "The National Interest 16 (Summer 1989), 3-18; JSTOR 24027184"
    fukuyama1989IdeologicalEndpoint

fukuyama1992Source : EndOfHistorySource
fukuyama1992Source =
  end-of-history-source
    "Francis Fukuyama"
    "The End of History and the Last Man"
    "Free Press, 1992; ISBN 9780029109755"
    fukuyama1992LiberalDemocraticCulmination

kojeveSource : EndOfHistorySource
kojeveSource =
  end-of-history-source
    "Alexandre Kojeve"
    "Introduction to the Reading of Hegel"
    "French publication 1947; English translation 1969"
    kojeveRecognitionCompletionReading

hegelReceptionBackground : EndOfHistorySource
hegelReceptionBackground =
  end-of-history-source
    "G. W. F. Hegel"
    "Reception background only"
    "No direct end-of-history theorem attribution asserted by this DASHI owner"
    hegelReceptionBackgroundOnly

------------------------------------------------------------------------
-- 2. Reopenable synthesis dynamics.
--
-- A productive join is a historically situated state with outgoing transport.
-- The constructors are finite DASHI comparison vocabulary, not a universal
-- law that every historical join must undergo one of exactly these events.
------------------------------------------------------------------------

data JoinMoment : Set where
  productiveJoinAtT
  counterformationAtNext
  revisedJoinLater
  : JoinMoment

data ReopeningTrigger : Set where
  newCounterformation
  changedPowerRelation
  newEvidence
  networkRecomposition
  memoryReinterpretation
  : ReopeningTrigger

data JoinTransport : JoinMoment → JoinMoment → Set where
  reopenByCounterformation :
    JoinTransport productiveJoinAtT counterformationAtNext
  rejoinAfterCounterformation :
    JoinTransport counterformationAtNext revisedJoinLater

canonicalJoinHasOutgoingTransport :
  JoinTransport productiveJoinAtT counterformationAtNext
canonicalJoinHasOutgoingTransport = reopenByCounterformation

canonicalReopenedHistoryContinues :
  JoinTransport counterformationAtNext revisedJoinLater
canonicalReopenedHistoryContinues = rejoinAfterCounterformation

canonicalProductiveJoinStillAvailable : Join.ProductiveDialecticalJoin
canonicalProductiveJoinStillAvailable = Join.canonicalProductiveJoin

------------------------------------------------------------------------
-- 3. Same productive-join surface can have different next histories.
------------------------------------------------------------------------

data FineJoinPresent : Set where
  sameJoinThenCounterformation
  sameJoinThenRevision
  : FineJoinPresent

data JoinPresentSurface : Set where
  productiveJoinNow : JoinPresentSurface

data NextHistoricalContinuation : Set where
  counterformationContinuation
  revisedJoinContinuation
  : NextHistoricalContinuation

joinPresentSurface : FineJoinPresent → JoinPresentSurface
joinPresentSurface _ = productiveJoinNow

nextContinuation : FineJoinPresent → NextHistoricalContinuation
nextContinuation sameJoinThenCounterformation = counterformationContinuation
nextContinuation sameJoinThenRevision = revisedJoinContinuation

productiveJoinSurfaceCannotRecoverNextHistory :
  INF.FactorsThrough joinPresentSurface nextContinuation → ⊥
productiveJoinSurfaceCannotRecoverNextHistory =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameJoinThenCounterformation
      sameJoinThenRevision
      refl
      (λ ()))

------------------------------------------------------------------------
-- 4. Consumer-relative ternary semantics.
--
-- A scoped current join can be accepted as productive while historical
-- finality is still unresolved.  Acceptance does not transport automatically
-- between different consumers/questions.
------------------------------------------------------------------------

data HistoricalFinalityStatus : Set where
  finalityRejected
  finalityUnresolved
  finalityEstablished
  : HistoricalFinalityStatus

finalityDisposition : HistoricalFinalityStatus → Suspension.EpistemicDisposition
finalityDisposition finalityRejected = Suspension.rejectHere
finalityDisposition finalityUnresolved = Suspension.suspendAndRefine
finalityDisposition finalityEstablished = Suspension.acceptHere

currentJoinAcceptedAsProductive :
  Join.joinDisposition Join.productiveJoin ≡ Suspension.acceptHere
currentJoinAcceptedAsProductive = refl

historicalFinalityRemainsUnresolvedInCanonicalFixture :
  finalityDisposition finalityUnresolved ≡ Suspension.suspendAndRefine
historicalFinalityRemainsUnresolvedInCanonicalFixture = refl

------------------------------------------------------------------------
-- 5. Attribution / no-promotion boundaries.
------------------------------------------------------------------------

data ProductiveJoinImpliesEndOfHistory : Set where

data FukuyamaThesisIsDASHIReopenabilityTheorem : Set where

data DASHIReopenabilityRefutesFukuyamaPhilosophically : Set where

data KojeveReadingIsIdenticalToHegel : Set where

data FukuyamaThesisIsIdenticalToKojeveReading : Set where

data EndOfHistoryMeansChronologicalEventsLiterallyStop : Set where

data CurrentJoinAcceptanceImpliesHistoricalFinalityAcceptance : Set where

data ReopenabilityGuaranteesProgress : Set where

productiveJoinDoesNotImplyEndOfHistory : ProductiveJoinImpliesEndOfHistory → ⊥
productiveJoinDoesNotImplyEndOfHistory ()

fukuyamaThesisIsNotDASHIReopenabilityTheorem :
  FukuyamaThesisIsDASHIReopenabilityTheorem → ⊥
fukuyamaThesisIsNotDASHIReopenabilityTheorem ()

dashIReopenabilityDoesNotByItselfRefuteFukuyamaPhilosophically :
  DASHIReopenabilityRefutesFukuyamaPhilosophically → ⊥
dashIReopenabilityDoesNotByItselfRefuteFukuyamaPhilosophically ()

kojeveReadingIsNotPromotedToHegelIdentity : KojeveReadingIsIdenticalToHegel → ⊥
kojeveReadingIsNotPromotedToHegelIdentity ()

fukuyamaThesisIsNotCollapsedIntoKojeveReading :
  FukuyamaThesisIsIdenticalToKojeveReading → ⊥
fukuyamaThesisIsNotCollapsedIntoKojeveReading ()

endOfHistoryDoesNotMeanLiteralEventCessationHere :
  EndOfHistoryMeansChronologicalEventsLiterallyStop → ⊥
endOfHistoryDoesNotMeanLiteralEventCessationHere ()

currentJoinAcceptanceDoesNotPromoteHistoricalFinality :
  CurrentJoinAcceptanceImpliesHistoricalFinalityAcceptance → ⊥
currentJoinAcceptanceDoesNotPromoteHistoricalFinality ()

reopenabilityDoesNotGuaranteeProgress : ReopenabilityGuaranteesProgress → ⊥
reopenabilityDoesNotGuaranteeProgress ()

------------------------------------------------------------------------
-- 6. Boundary summary.
------------------------------------------------------------------------

record ReopenableSynthesisEndOfHistoryBoundary : Set where
  constructor reopenable-synthesis-end-of-history-boundary
  field
    productiveJoinCanHaveOutgoingTransport : Bool
    sameJoinSurfaceCanHaveDifferentContinuation : Bool
    productiveJoinIsHistoricallyFinal : Bool
    currentJoinAcceptanceTransfersToFinalityConsumer : Bool
    reopenabilityGuaranteesProgress : Bool
    fukuyamaThesisEqualsDASHITheorem : Bool
    kojeveReadingEqualsHegelText : Bool
    fukuyamaEqualsKojeveWithoutResidual : Bool
    bookTitleMeansLiteralEventCessation : Bool
    attributionRolesRemainSeparate : Bool

canonicalReopenableSynthesisEndOfHistoryBoundary :
  ReopenableSynthesisEndOfHistoryBoundary
canonicalReopenableSynthesisEndOfHistoryBoundary =
  reopenable-synthesis-end-of-history-boundary
    true true false false false false false false false true
