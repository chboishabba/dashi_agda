module DASHI.Governance.InverseJusticeAttractorExact where

------------------------------------------------------------------------
-- CONCRETE INVERSE-JUSTICE ATTRACTOR WITNESS
--
-- JusticeCrossPollinationBridgeExact defines the generic specialization of the
-- existing trauma/exploitation FixedPoint carrier.  This file proves that the
-- specialization is inhabited by an exact finite model: historical recursion
-- has a fixed point, and an explicit justice interpreter maps that point to an
-- already-proved inverse-justice transition.
--
-- This is a finite structural witness only.  It does not diagnose any named
-- family, institution, population, conflict or political system as an
-- attractor.  Such an application still requires external evidence and a
-- case-specific interpreter.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.JusticeCrossPollinationBridgeExact as Cross
import DASHI.Governance.SituatedInverseJusticeFibreExact as Justice
import DASHI.Governance.TraumaExploitationAttractor as Trauma

------------------------------------------------------------------------
-- Singleton historical recursion.
------------------------------------------------------------------------

canonicalTraumaSystem : Trauma.TraumaExploitationSystem
canonicalTraumaSystem = record
  { Trauma.HistoricalState = ⊤
  ; Trauma.SufferingField = ⊤
  ; Trauma.ExploitationProtocol = ⊤
  ; Trauma.Institution = ⊤
  ; Trauma.Observable = ⊤
  ; Trauma.traumaProduction = λ state → tt
  ; Trauma.exploitationExtraction = λ suffering → tt
  ; Trauma.institutionalise = λ protocol → tt
  ; Trauma.reproduce = λ institution state → tt
  ; Trauma.observe = λ state → tt
  }

canonicalHistoricalFixedPoint : Trauma.FixedPoint canonicalTraumaSystem
canonicalHistoricalFixedPoint = record
  { Trauma.FixedPoint.point = tt
  ; Trauma.FixedPoint.fixed = refl
  }

------------------------------------------------------------------------
-- Explicit justice interpreter.  The fixed point does not create normative
-- status by itself; the interpreter is an independent proof-bearing input.
------------------------------------------------------------------------

canonicalJusticeInterpreter :
  Trauma.HistoricalState canonicalTraumaSystem →
  Justice.JusticeTransition Justice.preservingFibre Justice.violatingFibre
canonicalJusticeInterpreter state = Justice.violatingAction

canonicalInverseJusticeAttractor :
  Cross.InverseJusticeAttractor
    canonicalTraumaSystem
    canonicalJusticeInterpreter
canonicalInverseJusticeAttractor =
  Cross.fixedPointPlusInverseInterpreterYieldsInverseJusticeAttractor
    canonicalHistoricalFixedPoint
    Justice.violatingActionIsInverseJustice

canonicalAttractorPointIsInverseJustice :
  Justice.InverseJusticeOperator
    (canonicalJusticeInterpreter
      (Trauma.FixedPoint.point canonicalHistoricalFixedPoint))
canonicalAttractorPointIsInverseJustice =
  Justice.violatingActionIsInverseJustice

------------------------------------------------------------------------
-- The existing repair carrier is independently inhabited too.  Identity
-- repair/recovery is enough to show that reversibility data is a separate
-- structure from fixed-point/inverse-justice data; no repair is inferred merely
-- because an attractor was identified.
------------------------------------------------------------------------

canonicalRepairTransport : Trauma.RepairTransport canonicalTraumaSystem
canonicalRepairTransport = record
  { Trauma.RepairTransport.repair = λ state → state
  ; Trauma.RepairTransport.recover = λ state → state
  ; Trauma.RepairTransport.leftInverse = λ state → refl
  ; Trauma.RepairTransport.rightInverse = λ state → refl
  }

record InverseJusticeAttractorBoundary : Set where
  constructor inverseJusticeAttractorBoundary
  field
    fixedPointAloneCreatesInverseJustice : Bool
    justiceInterpreterRequired : Bool
    finiteAttractorWitnessInhabited : Bool
    repairTransportSeparateFromAttractorStatus : Bool
    namedWorldApplicationRequiresExternalEvidence : Bool

canonicalInverseJusticeAttractorBoundary : InverseJusticeAttractorBoundary
canonicalInverseJusticeAttractorBoundary =
  inverseJusticeAttractorBoundary false true true true true
