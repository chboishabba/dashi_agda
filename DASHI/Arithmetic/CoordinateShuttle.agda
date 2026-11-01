module DASHI.Arithmetic.CoordinateShuttle where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Unit using (⊤)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec)

open import Ontology.GodelLattice using (Vec15)

import DASHI.Arithmetic.ArithmeticIntegerEmbedding as AIE
import DASHI.Arithmetic.ArithmeticPrimeProfileBridge as APPB
import DASHI.Arithmetic.WeightedValuationEnergy as WVE
import DASHI.Physics.Closure.DeltaToQuadraticBridgeTheorem as DQ
import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
import DASHI.Geometry.ProjectionDefect as PD
import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

AdditivePair : Set
AdditivePair = AIE.Int × AIE.Int

MultiplicativeValuationCarrier : Set
MultiplicativeValuationCarrier = Vec15 Nat

WeightedQuadraticCarrier : Set
WeightedQuadraticCarrier = Vec ℤ 15

record ECoordinateShuttle : Set₁ where
  field
    additiveCarrier : Set
    multiplicativeCarrier : Set
    quadraticCarrier : Set

    E : additiveCarrier → multiplicativeCarrier
    toQuadratic : multiplicativeCarrier → quadraticCarrier

    dual : multiplicativeCarrier → multiplicativeCarrier
    dualIsSymmetry : Set

    rawSeverityMonotonicityClaim : Set
    admissibleAsCoordinateChange : Set

primeE : AdditivePair → MultiplicativeValuationCarrier
primeE (a , b) = AIE.delta15 a b

primeQuadraticTransport : AdditivePair → WeightedQuadraticCarrier
primeQuadraticTransport (a , b) =
  DQ.liftPrimeContributionVec (APPB.embeddedProfileCarrier a b)

primeWeightedQuadraticTransport : AdditivePair → WeightedQuadraticCarrier
primeWeightedQuadraticTransport (a , b) =
  WVE.weightedQuadraticVecℤ a

primeValuationShuttle : ECoordinateShuttle
primeValuationShuttle = record
  { additiveCarrier = AdditivePair
  ; multiplicativeCarrier = MultiplicativeValuationCarrier
  ; quadraticCarrier = WeightedQuadraticCarrier
  ; E = primeE
  ; toQuadratic = DQ.liftPrimeContributionVec
  ; dual = λ v → v
  ; dualIsSymmetry = ∀ (v : MultiplicativeValuationCarrier) → v ≡ v
  ; rawSeverityMonotonicityClaim = ⊤
  ; admissibleAsCoordinateChange = ⊤
  }

primeE-is-delta15 :
  ∀ a b → primeE (a , b) ≡ AIE.delta15 a b
primeE-is-delta15 a b = refl

primeQuadraticTransport-is-canonical-profile :
  ∀ a b →
  primeQuadraticTransport (a , b)
  ≡
  DQ.liftPrimeContributionVec (APPB.embeddedProfileCarrier a b)
primeQuadraticTransport-is-canonical-profile a b = refl

canonicalDeltaTransportFromPrimeE :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  AdditivePair →
  PD.Additive.Carrier
    (QES.AdditiveVecℤ
      {CFQT.ContractionForcesQuadraticTheorem.dimension theorem})
canonicalDeltaTransportFromPrimeE =
  DQ.canonicalDeltaTransport

record EAdmissibilityBoundary
  (theorem : CFQT.ContractionForcesQuadraticTheorem)
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) : Setω where
  field
    shuttle : ECoordinateShuttle
    pressureCompatibility :
      DQ.CancellationPressureCompatibility theorem dim≡15

  transportedEnergyAgreement :
    ∀ s →
      DQ.CancellationPressureCompatibility.arithmeticEnergyℤ
        pressureCompatibility
        s
      ≡
      DQ.contractionEnergy theorem
        (DQ.CancellationPressureCompatibility.stateTransport
          pressureCompatibility
          s)
  transportedEnergyAgreement =
    DQ.CancellationPressureCompatibility.candidateQuadraticAgreement
      pressureCompatibility
