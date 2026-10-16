module DASHI.Moonshine.JackDanielsJCoarseFineNaturalRecognitionExact where

------------------------------------------------------------------------
-- JACK DANIEL'S NATURAL RECOGNITION x jCOARSE/jFINE
--
-- ATTRIBUTION / CLAIM BOUNDARY
--
-- Existing source authority remains where it already lives:
--   * Katz--Mazur / Ogg / Duncan--Ono own the literal modular-curve / Fricke /
--     supersingular mathematics imported through ModularCurveJFrickeInterface;
--   * the Monster/McKay--Thompson/Hauptmodul authority remains in the existing
--     Moonshine owners;
--   * DASHI owns the finite jCoarse/jFine observer, its Fricke transport, and
--     the consumer-relative coarse/fine bookkeeping.
--
-- This module does NOT identify the finite 3^11 chart with a modular curve and
-- does NOT infer a Monster class from a finite code.  It makes the correct
-- factorisation question proof-relevant:
--
--   supersingular j
--      -> full modular datum
--      -> literal fine modular point
--      -> finite jCoarse/jFine observation
--
-- while the Monster datum continues to be computed from the FULL modular datum.
-- A further theorem may prove that the finite observation is sufficient for
-- that Monster consumer; until then the observer fibre is retained explicitly.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Moonshine.JackDanielsNaturalMonsterRecognitionMaxCutExact as JD
import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular
import DASHI.Moonshine.JInvariantJCoarseFineElevenTritChartShiftExact as Chart
import DASHI.Moonshine.JInvariantAnalyticJCoarseFineObserverExact as Observer
import DASHI.Biology.JCoarseFineConsumerReductionBridgeExact as Consumer

------------------------------------------------------------------------
-- 1. Adapter from the generic J3 ModularDatum to a literal fine modular point.
--
-- J3 deliberately leaves ModularDatum abstract.  jCoarse/jFine already knows
-- how to observe a ModularJFrickeSystem.FinePoint, so the only legitimate weld
-- is an explicit same-object adapter.
------------------------------------------------------------------------

record JCoarseFineModularDatumAdapter
    {p : Nat}
    (recognition : JD.SupersingularMonsterRecognition p) : Set₁ where
  constructor jcoarse-jfine-modular-datum-adapter
  field
    modularSystem : Modular.ModularJFrickeSystem
    structuredObserver : Observer.AnalyticJStructuredObserver modularSystem

    modularDatumToFinePoint :
      JD.ModularDatum recognition -> Modular.FinePoint modularSystem

    FinePointSameObjectWitness : Set
    finePointSameObject : FinePointSameObjectWitness

    FrickeCompatibilityWitness : Set
    frickeCompatibility : FrickeCompatibilityWitness

open JCoarseFineModularDatumAdapter public

------------------------------------------------------------------------
-- 2. Existing J3 recognition now acquires a structured observer receipt for
--    every supersingular input without replacing the full modular datum.
------------------------------------------------------------------------

record SupersingularJCoarseFineReceipt
    {p : Nat}
    (recognition : JD.SupersingularMonsterRecognition p)
    (adapter : JCoarseFineModularDatumAdapter recognition) : Set₁ where
  constructor supersingular-jcoarse-jfine-receipt
  field
    supersingularJ : JD.SupersingularJ recognition

    modularDatum : JD.ModularDatum recognition
    modularDatumIsRecognition :
      modularDatum ≡ JD.supersingularToModular recognition supersingularJ

    finePoint : Modular.FinePoint (modularSystem adapter)
    finePointIsAdaptedModularDatum :
      finePoint ≡ modularDatumToFinePoint adapter modularDatum

    structuredObservation : Chart.JTwoPlusNine
    structuredObservationIsObserver :
      structuredObservation
      ≡ Observer.observe (structuredObserver adapter) finePoint

    monsterDatum : JD.MonsterDatum recognition
    monsterDatumIsRecognition :
      monsterDatum ≡ JD.modularToMonster recognition modularDatum

    observerFibre :
      Observer.ObserverFibre
        (structuredObserver adapter)
        structuredObservation
        finePoint

open SupersingularJCoarseFineReceipt public

compileSupersingularJCoarseFineReceipt :
  ∀ {p : Nat}
    (recognition : JD.SupersingularMonsterRecognition p)
    (adapter : JCoarseFineModularDatumAdapter recognition)
    (j : JD.SupersingularJ recognition) ->
  SupersingularJCoarseFineReceipt recognition adapter
compileSupersingularJCoarseFineReceipt recognition adapter j =
  supersingular-jcoarse-jfine-receipt
    j
    modular
    refl
    point
    refl
    observation
    refl
    monster
    refl
    refl
  where
    modular = JD.supersingularToModular recognition j
    point = modularDatumToFinePoint adapter modular
    observation = Observer.observe (structuredObserver adapter) point
    monster = JD.modularToMonster recognition modular

------------------------------------------------------------------------
-- 3. Fricke transport is inherited from the existing analytic observer.
------------------------------------------------------------------------

frickeCarriesSupersingularObserverFibre :
  ∀ {p : Nat}
    {recognition : JD.SupersingularMonsterRecognition p}
    (adapter : JCoarseFineModularDatumAdapter recognition)
    {state : Chart.JTwoPlusNine}
    {point : Modular.FinePoint (modularSystem adapter)} ->
  Observer.ObserverFibre (structuredObserver adapter) state point ->
  Observer.ObserverFibre
    (structuredObserver adapter)
    (Observer.Finite.transportedFiniteFricke state)
    (Modular.fricke (modularSystem adapter) point)
frickeCarriesSupersingularObserverFibre adapter =
  Observer.frickeCarriesObserverFibre (structuredObserver adapter)

------------------------------------------------------------------------
-- 4. Stronger sufficiency theorem: when, and only when, the Monster consumer
--    factors through the finite jCoarse/jFine observation.
------------------------------------------------------------------------

record JCoarseFineMonsterFactorization
    {p : Nat}
    (recognition : JD.SupersingularMonsterRecognition p)
    (adapter : JCoarseFineModularDatumAdapter recognition) : Set₁ where
  constructor jcoarse-jfine-monster-factorization
  field
    structuredToMonster :
      Chart.JTwoPlusNine -> JD.MonsterDatum recognition

    factorsMonsterMap :
      (datum : JD.ModularDatum recognition) ->
      structuredToMonster
        (Observer.observe
          (structuredObserver adapter)
          (modularDatumToFinePoint adapter datum))
      ≡ JD.modularToMonster recognition datum

open JCoarseFineMonsterFactorization public

sameJCoarseFineObservationForcesSameMonsterDatum :
  ∀ {p : Nat}
    {recognition : JD.SupersingularMonsterRecognition p}
    {adapter : JCoarseFineModularDatumAdapter recognition}
    (factorization : JCoarseFineMonsterFactorization recognition adapter)
    (left right : JD.ModularDatum recognition) ->
    Observer.observe
      (structuredObserver adapter)
      (modularDatumToFinePoint adapter left)
    ≡
    Observer.observe
      (structuredObserver adapter)
      (modularDatumToFinePoint adapter right) ->
    JD.modularToMonster recognition left
    ≡ JD.modularToMonster recognition right
sameJCoarseFineObservationForcesSameMonsterDatum factorization left right sameObservation =
  trans
    (sym (factorsMonsterMap factorization left))
    (trans
      (cong (structuredToMonster factorization) sameObservation)
      (factorsMonsterMap factorization right))

------------------------------------------------------------------------
-- 5. Wrong-type firewalls.
------------------------------------------------------------------------

data FiniteJObservationIsLiteralModularPoint : Set where
data JCoarseAloneSelectsMonsterClass : Set where
data ObserverFibreCanBeDiscardedWithoutConsumerFactorization : Set where

data CardinalityThreePowerElevenCreatesMonsterRecognition : Set where

finiteObservationIsNotLiteralModularPoint :
  FiniteJObservationIsLiteralModularPoint -> ⊥
finiteObservationIsNotLiteralModularPoint ()

jCoarseAloneDoesNotSelectMonsterClass :
  JCoarseAloneSelectsMonsterClass -> ⊥
jCoarseAloneDoesNotSelectMonsterClass ()

observerFibreCannotBeSilentlyDiscarded :
  ObserverFibreCanBeDiscardedWithoutConsumerFactorization -> ⊥
observerFibreCannotBeSilentlyDiscarded ()

threePowerElevenDoesNotCreateMonsterRecognition :
  CardinalityThreePowerElevenCreatesMonsterRecognition -> ⊥
threePowerElevenDoesNotCreateMonsterRecognition ()

------------------------------------------------------------------------
-- 6. Existing consumer-relative reduction discipline is explicitly imported.
------------------------------------------------------------------------

jCoarseFineConsumerBoundary : Consumer.JCoarseFineConsumerReductionBoundary
jCoarseFineConsumerBoundary = Consumer.canonicalJCoarseFineConsumerReductionBoundary

------------------------------------------------------------------------
-- 7. Machine-readable max-cut.
------------------------------------------------------------------------

record JackDanielsJCoarseFineBoundary : Set where
  constructor jack-daniels-jcoarse-jfine-boundary
  field
    analyticObserverArchitectureAlreadyPaid : Bool
    frickeObserverFibreTransportAlreadyPaid : Bool
    coarseFineConsumerReductionDisciplineAlreadyPaid : Bool
    j3ToFinePointAdapterSpecified : Bool
    supersingularReceiptCompilerPaidConditionalOnJ3AndAdapter : Bool
    finiteObservationMonsterFactorizationSpecified : Bool

    j3NaturalRecognitionInhabitedHere : Bool
    j3FinePointAdapterInhabitedHere : Bool
    finiteObservationSufficientForMonsterConsumerPaid : Bool
    coarseObservationAlonePromotedToMonsterClass : Bool

canonicalJackDanielsJCoarseFineBoundary : JackDanielsJCoarseFineBoundary
canonicalJackDanielsJCoarseFineBoundary =
  jack-daniels-jcoarse-jfine-boundary
    true true true true true true
    false false false false
