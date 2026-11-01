module DASHI.Moonshine.MonsterFiveTrialecticC3PointedRecognitionExact where

------------------------------------------------------------------------
-- MONSTER-5 TRIALECTIC RECOGNITION: C3 CHART INDEPENDENCE + POINTED UPGRADE
--
-- DASHI CONTRIBUTION
--
-- The finite candidate side is already paid on one dyadic local chart U_AB.
-- Participant C3 symmetry shows that this choice is arbitrary.  This module:
--
--   1. transports any AB-source recognition canonically to BC and CA charts;
--   2. proves the signed local transport commutes with those retypings;
--   3. states the stronger pointed source contract needed to compare the
--      source completion/basepoint semantics with the newly constructed
--      pointed dyadic restriction system.
--
-- No actual Monster source carrier is manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Moonshine.MonsterFivePrimaryRelationalModelBoundaryExact as Source
import DASHI.Moonshine.MonsterFiveTrialecticLocalRecognitionExact as Recognition
import DASHI.Reasoning.Trialectic369DescentNaturalityExact as Descent
import DASHI.Reasoning.Trialectic369DyadicLocalNineObserverCandidateExact as Candidate
import DASHI.Reasoning.Trialectic369DyadicC3LocalComplementSymmetryExact as C3
import DASHI.Reasoning.Trialectic369DyadicPointedRelativeLocalExact as Pointed

------------------------------------------------------------------------
-- 1. Signed transport on BC/CA by retyping the canonical AB involution.
------------------------------------------------------------------------

negateBCLocal :
  Descent.BCSection ->
  Descent.BCSection
negateBCLocal section =
  C3.abAsBC
    (Candidate.negateABLocal
      (C3.bcAsAB section))

negateCALocal :
  Descent.CASection ->
  Descent.CASection
negateCALocal section =
  C3.abAsCA
    (Candidate.negateABLocal
      (C3.caAsAB section))

negateBCInvolutive :
  (section : Descent.BCSection) ->
  negateBCLocal (negateBCLocal section) ≡ section
negateBCInvolutive
  (Descent.bc-section bb bc cb cc) =
  cong C3.abAsBC
    (Candidate.negateABLocalInvolutive
      (C3.bcAsAB (Descent.bc-section bb bc cb cc)))

negateCAInvolutive :
  (section : Descent.CASection) ->
  negateCALocal (negateCALocal section) ≡ section
negateCAInvolutive
  (Descent.ca-section cc ca ac aa) =
  cong C3.abAsCA
    (Candidate.negateABLocalInvolutive
      (C3.caAsAB (Descent.ca-section cc ca ac aa)))

------------------------------------------------------------------------
-- 2. Any AB recognition induces BC/CA local recognition maps.
------------------------------------------------------------------------

sourceToBC :
  {source : Source.MonsterFivePrimaryRelationalObserver} ->
  Recognition.MonsterFiveTrialecticRecognition source ->
  Source.ActualState source ->
  Descent.BCSection
sourceToBC recognition state =
  C3.abAsBC
    (Recognition.sourceToLocal recognition state)

sourceToCA :
  {source : Source.MonsterFivePrimaryRelationalObserver} ->
  Recognition.MonsterFiveTrialecticRecognition source ->
  Source.ActualState source ->
  Descent.CASection
sourceToCA recognition state =
  C3.abAsCA
    (Recognition.sourceToLocal recognition state)

sourceTransportBecomesBCNegation :
  {source : Source.MonsterFivePrimaryRelationalObserver} ->
  (recognition : Recognition.MonsterFiveTrialecticRecognition source) ->
  (state : Source.ActualState source) ->
  sourceToBC recognition
    (Source.applyActualTransport source
      (Recognition.distinguishedTransport recognition)
      state)
  ≡
  negateBCLocal (sourceToBC recognition state)
sourceTransportBecomesBCNegation recognition state =
  cong C3.abAsBC
    (Recognition.sourceTransportBecomesLocalNegation recognition state)

sourceTransportBecomesCANegation :
  {source : Source.MonsterFivePrimaryRelationalObserver} ->
  (recognition : Recognition.MonsterFiveTrialecticRecognition source) ->
  (state : Source.ActualState source) ->
  sourceToCA recognition
    (Source.applyActualTransport source
      (Recognition.distinguishedTransport recognition)
      state)
  ≡
  negateCALocal (sourceToCA recognition state)
sourceTransportBecomesCANegation recognition state =
  cong C3.abAsCA
    (Recognition.sourceTransportBecomesLocalNegation recognition state)

------------------------------------------------------------------------
-- 3. Pointed source upgrade.
--
-- The existing source interface has only completionWitness : ActualState->Bool.
-- It does not select a source basepoint or prove that completionWitness
-- characterises it.  A pointed recognition must therefore receive that extra
-- source datum explicitly.
------------------------------------------------------------------------

record PointedMonsterFiveSource
  (source : Source.MonsterFivePrimaryRelationalObserver) : Set₁ where
  constructor pointed-monster-five-source
  field
    sourceBasepoint : Source.ActualState source

    completionAtBasepoint :
      Source.completionWitness source sourceBasepoint ≡ true

open PointedMonsterFiveSource public

record PointedMonsterFiveTrialecticRecognition
  {source : Source.MonsterFivePrimaryRelationalObserver}
  (pointedSource : PointedMonsterFiveSource source)
  (recognition : Recognition.MonsterFiveTrialecticRecognition source) : Set₁ where
  constructor pointed-monster-five-trialectic-recognition
  field
    distinguishedTransportPreservesSourceBasepoint :
      Source.applyActualTransport source
        (Recognition.distinguishedTransport recognition)
        (sourceBasepoint pointedSource)
      ≡ sourceBasepoint pointedSource

    sourceBasepointMapsToLocalBasepoint :
      Recognition.sourceToLocal recognition
        (sourceBasepoint pointedSource)
      ≡ Pointed.basepoint Pointed.ABPointed

open PointedMonsterFiveTrialecticRecognition public

------------------------------------------------------------------------
-- 4. The pointed datum transports to all C3-conjugate local charts.
------------------------------------------------------------------------

sourceBasepointMapsToBCBasepoint :
  {source : Source.MonsterFivePrimaryRelationalObserver} ->
  {pointedSource : PointedMonsterFiveSource source} ->
  {recognition : Recognition.MonsterFiveTrialecticRecognition source} ->
  PointedMonsterFiveTrialecticRecognition pointedSource recognition ->
  sourceToBC recognition (sourceBasepoint pointedSource)
  ≡ Pointed.basepoint Pointed.BCPointed
sourceBasepointMapsToBCBasepoint pointedRecognition =
  cong C3.abAsBC
    (sourceBasepointMapsToLocalBasepoint pointedRecognition)

sourceBasepointMapsToCABasepoint :
  {source : Source.MonsterFivePrimaryRelationalObserver} ->
  {pointedSource : PointedMonsterFiveSource source} ->
  {recognition : Recognition.MonsterFiveTrialecticRecognition source} ->
  PointedMonsterFiveTrialecticRecognition pointedSource recognition ->
  sourceToCA recognition (sourceBasepoint pointedSource)
  ≡ Pointed.basepoint Pointed.CAPointed
sourceBasepointMapsToCABasepoint pointedRecognition =
  cong C3.abAsCA
    (sourceBasepointMapsToLocalBasepoint pointedRecognition)

------------------------------------------------------------------------
-- 5. Source-interface insufficiency is now explicit.
------------------------------------------------------------------------

data CompletionBooleanAloneSelectsCanonicalSourceBasepoint : Set where
data FiniteCandidateConstructsPointedMonsterSource : Set where
data C3ChartIndependenceConstructsMonsterSource : Set where

completionBooleanAloneDoesNotSelectSourceBasepoint :
  CompletionBooleanAloneSelectsCanonicalSourceBasepoint -> ⊥
completionBooleanAloneDoesNotSelectSourceBasepoint ()

finiteCandidateDoesNotConstructPointedMonsterSource :
  FiniteCandidateConstructsPointedMonsterSource -> ⊥
finiteCandidateDoesNotConstructPointedMonsterSource ()

chartIndependenceDoesNotConstructMonsterSource :
  C3ChartIndependenceConstructsMonsterSource -> ⊥
chartIndependenceDoesNotConstructMonsterSource ()

------------------------------------------------------------------------
-- 6. Frontier.
------------------------------------------------------------------------

data MonsterFivePointedRecognitionResidual : Set where
  missingActualMonsterFiveSourceCarrier : MonsterFivePointedRecognitionResidual
  missingCanonicalSourceBasepoint : MonsterFivePointedRecognitionResidual
  missingSourceToTrialecticLocalMap : MonsterFivePointedRecognitionResidual
  missingSourceTransportToLocalNegation : MonsterFivePointedRecognitionResidual
  missingSourceCompletionToPointedLocalLaw : MonsterFivePointedRecognitionResidual
  missingAnalyticFrickeIdentification : MonsterFivePointedRecognitionResidual

record MonsterFiveTrialecticC3PointedRecognitionBoundary : Set where
  constructor monster-five-trialectic-c3-pointed-recognition-boundary
  field
    finiteABRecognitionContractExisting : Bool
    BCRecognitionDerivedFromAB : Bool
    CARecognitionDerivedFromAB : Bool
    signedTransportC3ChartIndependent : Bool
    pointedLocalSystemExisting : Bool
    pointedSourceUpgradeContractOwned : Bool
    completionBooleanAlreadyDeterminesBasepoint : Bool
    actualMonsterFiveSourceConstructed : Bool
    analyticFrickeIdentified : Bool
    firstResidual : MonsterFivePointedRecognitionResidual

canonicalMonsterFiveTrialecticC3PointedRecognitionBoundary :
  MonsterFiveTrialecticC3PointedRecognitionBoundary
canonicalMonsterFiveTrialecticC3PointedRecognitionBoundary =
  monster-five-trialectic-c3-pointed-recognition-boundary
    true true true true true true
    false false false
    missingActualMonsterFiveSourceCarrier
