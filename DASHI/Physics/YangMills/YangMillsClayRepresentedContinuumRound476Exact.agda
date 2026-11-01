{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND476: REPRESENTATION-FIRST CONTINUUM SPECIALIZATION
--
-- The legacy physical continuum carrier stores only an expectation functional.
-- This owner keeps the real mathematical object first:
--
--   countably-additive mu
--       -> E_mu(F) := integral F dmu
--       -> physical continuum expectation carrier
--       -> Schwinger family from that exact carrier.
--
-- Equalities expressing these construction choices are definitional.  The
-- nontrivial theorem is the existence/countable-additivity/source-limit
-- identification of the represented measure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger

record RepresentedContinuum
    (Observable : Set) : Set₁ where
  field
    MeasureObject : Set
    IsCountablyAdditive : MeasureObject → Set

    measure : MeasureObject
    integrate : MeasureObject → Observable → ℝ

    countablyAdditive :
      IsCountablyAdditive measure

open RepresentedContinuum public

asPhysicalContinuum :
  ∀ {Observable} →
  RepresentedContinuum Observable →
  Physical.PhysicalContinuumYMMeasure Observable ℝ
asPhysicalContinuum represented =
  Physical.physicalContinuumMeasure
    (integrate represented (measure represented))

physicalExpectationIsIntegral :
  ∀ {Observable}
    (represented : RepresentedContinuum Observable)
    observable →
  Physical.expectation (asPhysicalContinuum represented) observable
  ≡ integrate represented (measure represented) observable
physicalExpectationIsIntegral represented observable = refl

representedSchwinger :
  ∀ {Observable Position} →
  Schwinger.CylinderSchwingerEncoding Observable Position →
  (represented : RepresentedContinuum Observable) →
  Physical.PhysicalSchwingerFamily Observable Position ℝ
representedSchwinger encoding represented =
  Schwinger.schwingerFromMeasure
    encoding
    (asPhysicalContinuum represented)

representedSchwingerIsIntegralExpectation :
  ∀ {Observable Position}
    (encoding : Schwinger.CylinderSchwingerEncoding Observable Position)
    (represented : RepresentedContinuum Observable)
    observable left right →
  Physical.schwinger
    (representedSchwinger encoding represented)
    observable left right
  ≡
  integrate represented (measure represented)
    (Schwinger.twoPointCylinder encoding observable left right)
representedSchwingerIsIntegralExpectation encoding represented observable left right =
  refl

record SourceLimitRepresentation
    (Observable : Set)
    (sourceExpectation : Observable → ℝ)
    : Set₁ where
  field
    represented : RepresentedContinuum Observable

    sourceLimitIsIntegral :
      ∀ observable →
      sourceExpectation observable
      ≡ integrate represented (measure represented) observable

open SourceLimitRepresentation public

sourceLimitEqualsPhysicalExpectation :
  ∀ {Observable sourceExpectation}
    (representation :
      SourceLimitRepresentation Observable sourceExpectation)
    observable →
  sourceExpectation observable
  ≡ Physical.expectation
      (asPhysicalContinuum (represented representation))
      observable
sourceLimitEqualsPhysicalExpectation representation observable =
  sourceLimitIsIntegral representation observable

modelChoiceExpectationEqualityIsDefinitional : Bool
modelChoiceExpectationEqualityIsDefinitional = true

modelChoiceSchwingerEqualityIsDefinitional : Bool
modelChoiceSchwingerEqualityIsDefinitional = true

expectationFunctionalAloneIsCountablyAdditiveMeasure : Bool
expectationFunctionalAloneIsCountablyAdditiveMeasure = false

postHocRepresentedMeasureExpectationWeldRequired : Bool
postHocRepresentedMeasureExpectationWeldRequired = false

round476RepresentationFirstCompilerLevel : ProofLevel
round476RepresentationFirstCompilerLevel = machineChecked

literalRound476CountablyAdditiveRepresentationLevel : ProofLevel
literalRound476CountablyAdditiveRepresentationLevel = conditional
