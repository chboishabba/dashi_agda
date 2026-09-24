{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayRepresentedLiteralConstructionRound483Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND483: REPRESENTATION-FIRST LITERAL YM CONSTRUCTION
--
-- Specialize the full physical Clay object so that, for every compact-simple G,
-- the continuum object is chosen as an actual represented countably-additive
-- measure first.  The legacy physical expectation carrier and Schwinger family
-- are then projections of that object by construction.
--
-- This removes, globally:
--   represented measure = chosen continuum expectation
--   Schwinger-from-measure = independently chosen Schwinger
-- as theorem obligations.  The remaining obligations concern the actual
-- continuum/source theorem and the physical semantics of the derived objects.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476

record RepresentedLiteralYMConstruction
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum : Set)
    (S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ
          (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    : Set₂ where
  field
    spacetime : X

    finiteMeasure :
      G → Nat → Physical.PhysicalFiniteYMMeasure Configuration ℝ

    representedContinuum :
      G → R476.RepresentedContinuum (Configuration → ℝ)

    cylinderEncoding :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position

    localObservable :
      G → Position → Configuration → ℝ

    curvatureOperator :
      G → CurvaturePolynomial → LocalOperator

    opeCoefficient :
      G →
      LocalOperator → LocalOperator → LocalOperator →
      Position → OPECoefficient

    opeRemainder :
      G →
      LocalOperator → LocalOperator →
      Position → Nat → ℚ

    stressTensor :
      G → StressTensor

    hilbertSpace :
      G → Hilbert

    hamiltonian :
      G → Hamiltonian

    vacuum :
      G → Vacuum

    massGap :
      G → ℚ

open RepresentedLiteralYMConstruction public

continuumMeasure :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S} →
  RepresentedLiteralYMConstruction
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S →
  G → Physical.PhysicalContinuumYMMeasure (Configuration → ℝ) ℝ
continuumMeasure representedYM group =
  R476.asPhysicalContinuum
    (representedContinuum representedYM group)

schwinger :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S} →
  (representedYM :
    RepresentedLiteralYMConstruction
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S) →
  G → Physical.PhysicalSchwingerFamily (Configuration → ℝ) Position ℝ
schwinger representedYM group =
  R476.representedSchwinger
    (cylinderEncoding representedYM)
    (representedContinuum representedYM group)

asLiteralConstruction :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S} →
  RepresentedLiteralYMConstruction
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S →
  Top.LiteralYangMillsConstruction
    (Physical.physicalLiteralCarriers
      G X Nat Configuration ℝ
      (Configuration → ℝ) Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      Hilbert Hamiltonian Vacuum)
    S
asLiteralConstruction representedYM = record
  { Top.LiteralYangMillsConstruction.spacetime =
      spacetime representedYM
  ; Top.LiteralYangMillsConstruction.finiteMeasure =
      finiteMeasure representedYM
  ; Top.LiteralYangMillsConstruction.continuumMeasure =
      continuumMeasure representedYM
  ; Top.LiteralYangMillsConstruction.schwinger =
      schwinger representedYM
  ; Top.LiteralYangMillsConstruction.localObservable =
      localObservable representedYM
  ; Top.LiteralYangMillsConstruction.curvatureOperator =
      curvatureOperator representedYM
  ; Top.LiteralYangMillsConstruction.opeCoefficient =
      opeCoefficient representedYM
  ; Top.LiteralYangMillsConstruction.opeRemainder =
      opeRemainder representedYM
  ; Top.LiteralYangMillsConstruction.stressTensor =
      stressTensor representedYM
  ; Top.LiteralYangMillsConstruction.hilbertSpace =
      hilbertSpace representedYM
  ; Top.LiteralYangMillsConstruction.hamiltonian =
      hamiltonian representedYM
  ; Top.LiteralYangMillsConstruction.vacuum =
      vacuum representedYM
  ; Top.LiteralYangMillsConstruction.massGap =
      massGap representedYM
  }

literalContinuumExpectationIsIntegral :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S}
    (representedYM :
      RepresentedLiteralYMConstruction
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S)
    group observable →
  Physical.expectation
    (Top.continuumMeasure
      (asLiteralConstruction representedYM) group)
    observable
  ≡
  R476.integrate
    (representedContinuum representedYM group)
    (R476.measure (representedContinuum representedYM group))
    observable
literalContinuumExpectationIsIntegral representedYM group observable =
  R476.physicalExpectationIsIntegral
    (representedContinuum representedYM group)
    observable

continuumCarrierChosenIndependentlyFromRepresentedMeasure : Bool
continuumCarrierChosenIndependentlyFromRepresentedMeasure = false

schwingerChosenIndependentlyFromContinuumCarrier : Bool
schwingerChosenIndependentlyFromContinuumCarrier = false

round483RepresentedLiteralConstructionCompilerLevel : ProofLevel
round483RepresentedLiteralConstructionCompilerLevel = machineChecked
