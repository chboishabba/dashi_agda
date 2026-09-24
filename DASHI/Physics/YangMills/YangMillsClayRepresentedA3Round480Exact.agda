{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayRepresentedA3Round480Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND480: REPRESENTED LITERAL CONTINUUM AT FIXED G
--
-- The literal physical carrier historically names an expectation functional
-- "ContinuumMeasure".  R476 provides the representation-first object carrying
-- an actual countably-additive measure.  This owner requires A3 to terminate on
-- the projection of THAT object, and constructs the Schwinger family from the
-- same represented expectation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476

record RepresentedA3At
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum : Set)
    (S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ
          (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    (group : G)
    (finiteFamily :
      Nat → Physical.PhysicalFiniteYMMeasure Configuration ℝ)
    (encoding :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position)
    : Set₂ where
  field
    represented :
      R476.RepresentedContinuum (Configuration → ℝ)

    literalContinuumLimit :
      Top.IsContinuumLimitOf S group
        finiteFamily
        (R476.asPhysicalContinuum represented)

    literalSchwingerBelongs :
      Top.SchwingerBelongsToMeasure S
        (R476.asPhysicalContinuum represented)
        (R476.representedSchwinger encoding represented)

open RepresentedA3At public

continuumMeasureAt :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S group
      finiteFamily encoding} →
  RepresentedA3At
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    S group finiteFamily encoding →
  Physical.PhysicalContinuumYMMeasure (Configuration → ℝ) ℝ
continuumMeasureAt dataSet =
  R476.asPhysicalContinuum (represented dataSet)

schwingerAt :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S group
      finiteFamily encoding} →
  (dataSet :
    RepresentedA3At
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      S group finiteFamily encoding) →
  Physical.PhysicalSchwingerFamily (Configuration → ℝ) Position ℝ
schwingerAt {encoding = encoding} dataSet =
  R476.representedSchwinger encoding (represented dataSet)

continuumExpectationIsRepresentedIntegral :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S group
      finiteFamily encoding}
    (dataSet :
      RepresentedA3At
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        S group finiteFamily encoding)
    observable →
  Physical.expectation (continuumMeasureAt dataSet) observable
  ≡
  R476.integrate (represented dataSet)
    (R476.measure (represented dataSet))
    observable
continuumExpectationIsRepresentedIntegral dataSet observable =
  R476.physicalExpectationIsIntegral (represented dataSet) observable

postHocContinuumFunctionalToMeasurePromotionRequired : Bool
postHocContinuumFunctionalToMeasurePromotionRequired = false

independentSchwingerCarrierChoiceRequired : Bool
independentSchwingerCarrierChoiceRequired = false

round480RepresentedA3CompilerLevel : ProofLevel
round480RepresentedA3CompilerLevel = machineChecked

literalRound480RepresentedContinuumSemanticsLevel : ProofLevel
literalRound480RepresentedContinuumSemanticsLevel = conditional
