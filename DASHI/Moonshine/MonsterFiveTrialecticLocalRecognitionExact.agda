module DASHI.Moonshine.MonsterFiveTrialecticLocalRecognitionExact where

------------------------------------------------------------------------
-- MONSTER-5 SOURCE -> TRIALECTIC LOCAL RECOGNITION CONTRACT
--
-- DASHI CONTRIBUTION
--
-- The pre-RH trialectic side now owns:
--
--   ABSection -> ModePhaseQuotient9
--
-- together with an involutive signed C2 transport and exact observer
-- intertwining.
--
-- The remaining arithmetic/Monster payment is therefore not another finite
-- carrier theorem.  It is a source recognition map:
--
--   SourceState -> ABSection
--
-- plus a distinguished source transport that maps to local sign inversion.
--
-- Once those are supplied, the nine-state observer intertwining follows
-- automatically.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Foundations.Base369FiveModePhaseQuotientExact as Five
import DASHI.Moonshine.MonsterFivePrimaryRelationalModelBoundaryExact as Source
import DASHI.Reasoning.Trialectic369DescentNaturalityExact as Descent
import DASHI.Reasoning.Trialectic369DyadicLocalNineObserverCandidateExact as Candidate

------------------------------------------------------------------------
-- 1. Recognition contract against an independently supplied Monster source.
------------------------------------------------------------------------

record MonsterFiveTrialecticRecognition
  (source : Source.MonsterFivePrimaryRelationalObserver) : Set₁ where
  constructor monster-five-trialectic-recognition
  field
    sourceToLocal :
      Source.ActualState source ->
      Descent.ABSection

    distinguishedTransport :
      Source.ActualTransport source

    sourceTransportBecomesLocalNegation :
      (state : Source.ActualState source) ->
      sourceToLocal
        (Source.applyActualTransport source distinguishedTransport state)
      ≡
      Candidate.negateABLocal (sourceToLocal state)

    sourceObserverAgreesWithLocalObserver :
      (state : Source.ActualState source) ->
      Source.observeStableMode source state
      ≡ Candidate.observeABCanonicalModeNine (sourceToLocal state)

open MonsterFiveTrialecticRecognition public

------------------------------------------------------------------------
-- 2. Induced finite transport theorem.
------------------------------------------------------------------------

sourceObserverAfterDistinguishedTransport :
  {source : Source.MonsterFivePrimaryRelationalObserver} ->
  (recognition : MonsterFiveTrialecticRecognition source) ->
  (state : Source.ActualState source) ->
  Source.observeStableMode source
    (Source.applyActualTransport source
      (distinguishedTransport recognition)
      state)
  ≡
  Candidate.negateModeNine
    (Source.observeStableMode source state)
sourceObserverAfterDistinguishedTransport
  {source} recognition state =
  trans
    (sourceObserverAgreesWithLocalObserver recognition
      (Source.applyActualTransport source
        (distinguishedTransport recognition)
        state))
    (trans
      (cong Candidate.observeABCanonicalModeNine
        (sourceTransportBecomesLocalNegation recognition state))
      (trans
        (Candidate.modeObserverIntertwinesNegation
          (sourceToLocal recognition state))
        (cong Candidate.negateModeNine
          (sourceObserverAgreesWithLocalObserver recognition state))))

------------------------------------------------------------------------
-- 3. Compare with the source's own model transport.
------------------------------------------------------------------------

record DistinguishedTransportMatchesCandidateModel
  {source : Source.MonsterFivePrimaryRelationalObserver}
  (recognition : MonsterFiveTrialecticRecognition source) : Set where
  constructor distinguished-transport-matches-candidate-model
  field
    sourceModelTransportIsCandidateNegation :
      (mode : Five.ModePhaseQuotient9) ->
      Source.modelTransport source
        (distinguishedTransport recognition)
        mode
      ≡ Candidate.negateModeNine mode

open DistinguishedTransportMatchesCandidateModel public

sourceIntertwinerFactorsThroughCandidate :
  {source : Source.MonsterFivePrimaryRelationalObserver} ->
  (recognition : MonsterFiveTrialecticRecognition source) ->
  (match : DistinguishedTransportMatchesCandidateModel recognition) ->
  (state : Source.ActualState source) ->
  Source.observeStableMode source
    (Source.applyActualTransport source
      (distinguishedTransport recognition)
      state)
  ≡
  Source.modelTransport source
    (distinguishedTransport recognition)
    (Source.observeStableMode source state)
sourceIntertwinerFactorsThroughCandidate
  {source} recognition match state =
  trans
    (sourceObserverAfterDistinguishedTransport recognition state)
    (cong (λ mode → mode)
      (sym
        (sourceModelTransportIsCandidateNegation match
          (Source.observeStableMode source state))))
  where
    open import Relation.Binary.PropositionalEquality using (sym)

------------------------------------------------------------------------
-- 4. Firewall / frontier.
------------------------------------------------------------------------

data TrialecticCandidateAloneConstructsMonsterSource : Set where
data FiniteC2AloneIdentifiesAnalyticFricke : Set where

candidateDoesNotConstructMonsterSource :
  TrialecticCandidateAloneConstructsMonsterSource -> ⊥
candidateDoesNotConstructMonsterSource ()

finiteC2DoesNotIdentifyAnalyticFricke :
  FiniteC2AloneIdentifiesAnalyticFricke -> ⊥
finiteC2DoesNotIdentifyAnalyticFricke ()

record MonsterFiveTrialecticRecognitionBoundary : Set where
  constructor monster-five-trialectic-recognition-boundary
  field
    finiteLocalModeObserverPaid : Bool
    finiteSignedC2IntertwinerPaid : Bool
    sourceToLocalRecognitionRequired : Bool
    distinguishedSourceTransportRequired : Bool
    modelTransportComparisonRequired : Bool
    actualMonsterSourceConstructedHere : Bool
    analyticFrickeIdentifiedHere : Bool

canonicalMonsterFiveTrialecticRecognitionBoundary :
  MonsterFiveTrialecticRecognitionBoundary
canonicalMonsterFiveTrialecticRecognitionBoundary =
  monster-five-trialectic-recognition-boundary
    true true true true true false false
