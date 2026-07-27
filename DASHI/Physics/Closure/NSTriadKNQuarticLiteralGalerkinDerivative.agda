module DASHI.Physics.Closure.NSTriadKNQuarticLiteralGalerkinDerivative where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: David Darrow; Elizabeth Carlson; David Goluskin.
-- Title: "Quartic Lyapunov functions for global fluid stability".
-- Venue/year: arXiv preprint, 2026.
-- Journal DOI: none recorded on arXiv v1.
-- arXiv/DataCite DOI: 10.48550/arXiv.2606.18232.
-- arXiv: 2606.18232v1.
-- Uses: equations (21)--(25), derivative decomposition by degree.
-- Relationship: adapts the quadratic/cubic/quartic bookkeeping to the
-- coefficient-exact periodic Galerkin equation already formalised by DASHI.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Equation
import DASHI.Physics.Closure.NSTriadKNQuarticAnalyticFiniteSums as Candidate

record LiteralQuarticGalerkinLieData
    {r c : Level}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (P : Candidate.FourierQuarticParameters {r} {c} F)
    (system : Equation.FiniteComplex3GalerkinSystem F E I) :
    Set (lsuc (r ⊔ c)) where
  field
    kineticEnergyTimeDerivative coherenceTimeDerivative
      quadraticCorrectionTimeDerivative quarticTimeDerivative :
      C3.Carrier F

    energyLinear energyNonlinear : C3.Carrier F
    coherenceLinear coherenceNonlinear : C3.Carrier F
    correctionLinear correctionNonlinear : C3.Carrier F

    complexSquaredMagnitudeDerivativeLHS
      complexSquaredMagnitudeDerivativeRHS :
      C3.Carrier F
    complexSquaredMagnitudeDerivative :
      complexSquaredMagnitudeDerivativeLHS
      ≡ complexSquaredMagnitudeDerivativeRHS

    complex3SquaredMagnitudeDerivativeLHS
      complex3SquaredMagnitudeDerivativeRHS :
      C3.Carrier F
    complex3SquaredMagnitudeDerivative :
      complex3SquaredMagnitudeDerivativeLHS
      ≡ complex3SquaredMagnitudeDerivativeRHS

    finiteScalarSumDerivativeLHS
      finiteScalarSumDerivativeRHS :
      C3.Carrier F
    finiteScalarSumDerivative :
      finiteScalarSumDerivativeLHS
      ≡ finiteScalarSumDerivativeRHS

    kineticEnergyDerivative :
      kineticEnergyTimeDerivative
      ≡ C3.add F energyLinear energyNonlinear

    coherenceCoordinateDerivative :
      coherenceTimeDerivative
      ≡ C3.add F coherenceLinear coherenceNonlinear

    quadraticCorrectionDerivative :
      quadraticCorrectionTimeDerivative
      ≡ C3.add F correctionLinear correctionNonlinear

    quarticProductChainRule :
      quarticTimeDerivative
      ≡
      C3.add F
        (C3.add F
          (C3.multiply F (Candidate.two F)
            (C3.multiply F
              (Candidate.kineticEnergy P
                (Equation.cutoff system)
                (Equation.velocity system))
              kineticEnergyTimeDerivative))
          (C3.multiply F (Candidate.two F)
            (C3.add F
              (C3.multiply F kineticEnergyTimeDerivative
                (Candidate.selectedCoherence P
                  (Equation.cutoff system)
                  (Equation.velocity system)))
              (C3.multiply F
                (Candidate.kineticEnergy P
                  (Equation.cutoff system)
                  (Equation.velocity system))
                coherenceTimeDerivative))))
        quadraticCorrectionTimeDerivative

    energyNonlinearVanishes :
      energyNonlinear ≡ C3.zero F

    energyNonlinearTermVanishes :
      energyNonlinear ≡ C3.zero F

    energyViscousDerivative :
      kineticEnergyTimeDerivative ≡ energyLinear

    coherenceLinearNonlinearSplit :
      coherenceTimeDerivative
      ≡ C3.add F coherenceLinear coherenceNonlinear

    quadraticCorrectionLinearNonlinearSplit :
      quadraticCorrectionTimeDerivative
      ≡ C3.add F correctionLinear correctionNonlinear

    literalProjectedEquation :
      Equation.ExactProjectedGalerkinEquation system

    literalFiniteSumDerivative viscousScalarDerivative
      physicalTriadScalarDerivative : C3.Carrier F

    literalDerivativeSplits : literalFiniteSumDerivative
      ≡ C3.add F
          viscousScalarDerivative
          physicalTriadScalarDerivative

    linearPiecesAgreeWithViscousTerm :
      C3.add F
        (C3.add F energyLinear coherenceLinear)
        correctionLinear
      ≡ viscousScalarDerivative

    nonlinearPiecesAgreeWithPhysicalTriadSum :
      C3.add F
        (C3.add F energyNonlinear coherenceNonlinear)
        correctionNonlinear
      ≡ physicalTriadScalarDerivative

    literalQuadraticTriadSum literalCoherenceTriadSum
      symmetrisedPhysicalTriadSum : C3.Carrier F

    quadraticNonlinearityLiteralTriadExpansion :
      correctionNonlinear ≡ literalQuadraticTriadSum

    coherenceNonlinearityLiteralTriadExpansion :
      coherenceNonlinear ≡ literalCoherenceTriadSum

    weightedTriadSymmetrisationIdentity :
      physicalTriadScalarDerivative
      ≡ symmetrisedPhysicalTriadSum

    fixedChartSelectedDerivativeAgreement :
      quarticTimeDerivative ≡ literalFiniteSumDerivative

    fixedChartResidual : C3.Carrier F
    fixedChartResidualClassVanishes :
      fixedChartResidual ≡ C3.zero F

    ChartSwitch : Set c
    oldChartValue newChartValue : ChartSwitch → C3.Carrier F
    ChartValueNonincrease :
      C3.Carrier F → C3.Carrier F → Set r
    chartSwitchSeparatedFromContinuousDerivative : ∀ event →
      ChartValueNonincrease (newChartValue event) (oldChartValue event)

open LiteralQuarticGalerkinLieData public

quarticDerivativeNoQuinticTerm :
  ∀ {r c} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {P : Candidate.FourierQuarticParameters {r} {c} F}
    {system : Equation.FiniteComplex3GalerkinSystem F E I}
    (D : LiteralQuarticGalerkinLieData P system) →
  energyNonlinear D ≡ C3.zero F
quarticDerivativeNoQuinticTerm D =
  energyNonlinearTermVanishes D

quadraticDerivativePart :
  ∀ {r c} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {P : Candidate.FourierQuarticParameters {r} {c} F}
    {system : Equation.FiniteComplex3GalerkinSystem F E I} →
  LiteralQuarticGalerkinLieData P system → C3.Carrier F
quadraticDerivativePart D = correctionLinear D

cubicDerivativePart :
  ∀ {r c} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {P : Candidate.FourierQuarticParameters {r} {c} F}
    {system : Equation.FiniteComplex3GalerkinSystem F E I} →
  LiteralQuarticGalerkinLieData P system → C3.Carrier F
cubicDerivativePart {F = F} {P = P} {system = system} D =
  C3.add F
    (C3.add F
      (correctionNonlinear D)
      (C3.multiply F (Candidate.two F)
        (C3.multiply F
          (energyLinear D)
          (Candidate.selectedCoherence P
            (Equation.cutoff system)
            (Equation.velocity system)))))
    (C3.multiply F (Candidate.two F)
      (C3.multiply F
        (Candidate.kineticEnergy P
          (Equation.cutoff system)
          (Equation.velocity system))
        (coherenceLinear D)))

quarticDerivativePart :
  ∀ {r c} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {P : Candidate.FourierQuarticParameters {r} {c} F}
    {system : Equation.FiniteComplex3GalerkinSystem F E I} →
  LiteralQuarticGalerkinLieData P system → C3.Carrier F
quarticDerivativePart {F = F} {P = P} {system = system} D =
  C3.add F
    (C3.multiply F (Candidate.two F)
      (C3.multiply F
        (Candidate.kineticEnergy P
          (Equation.cutoff system)
          (Equation.velocity system))
        (energyLinear D)))
    (C3.multiply F (Candidate.two F)
      (C3.multiply F
        (Candidate.kineticEnergy P
          (Equation.cutoff system)
          (Equation.velocity system))
        (coherenceNonlinear D)))

quarticDerivativeByDegree :
  ∀ {r c} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {P : Candidate.FourierQuarticParameters {r} {c} F}
    {system : Equation.FiniteComplex3GalerkinSystem F E I} →
  LiteralQuarticGalerkinLieData P system → C3.Carrier F
quarticDerivativeByDegree {F = F} D =
  C3.add F
    (C3.add F
      (quadraticDerivativePart D)
      (cubicDerivativePart D))
    (quarticDerivativePart D)

quarticDerivativeHasExactThreeDegreePieces :
  ∀ {r c} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {P : Candidate.FourierQuarticParameters {r} {c} F}
    {system : Equation.FiniteComplex3GalerkinSystem F E I}
    (D : LiteralQuarticGalerkinLieData P system) →
  quarticDerivativeByDegree D
  ≡
  C3.add F
    (C3.add F
      (quadraticDerivativePart D)
      (cubicDerivativePart D))
    (quarticDerivativePart D)
quarticDerivativeHasExactThreeDegreePieces D = refl

quarticDerivativeExactDegreeSplit :
  ∀ {r c} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {P : Candidate.FourierQuarticParameters {r} {c} F}
    {system : Equation.FiniteComplex3GalerkinSystem F E I}
    (D : LiteralQuarticGalerkinLieData P system) →
  quarticDerivativeByDegree D
  ≡
  C3.add F
    (C3.add F
      (quadraticDerivativePart D)
      (cubicDerivativePart D))
    (quarticDerivativePart D)
quarticDerivativeExactDegreeSplit =
  quarticDerivativeHasExactThreeDegreePieces

record LiteralDerivativeIdentification
    {r c : Level}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {P : Candidate.FourierQuarticParameters {r} {c} F}
    {system : Equation.FiniteComplex3GalerkinSystem F E I}
    (D : LiteralQuarticGalerkinLieData P system) :
    Set (lsuc (r ⊔ c)) where
  field
    actualTimeDerivativeOfQuartic : C3.Carrier F
    actualDerivativeAgrees :
      actualTimeDerivativeOfQuartic
      ≡ quarticDerivativeByDegree D
    literalDerivativeEqualsPhysicalTriadDerivative :
      physicalTriadScalarDerivative D
      ≡
      C3.add F
        (correctionNonlinear D)
        (C3.add F
          (coherenceNonlinear D)
          (energyNonlinear D))

open LiteralDerivativeIdentification public

degreeDecompositionFormulaImplemented : Bool
degreeDecompositionFormulaImplemented = true

degreeDecompositionFormulaImplementedIsTrue :
  degreeDecompositionFormulaImplemented ≡ true
degreeDecompositionFormulaImplementedIsTrue = refl

literalChainRuleIdentificationClosed : Bool
literalChainRuleIdentificationClosed = false

literalChainRuleIdentificationClosedIsFalse :
  literalChainRuleIdentificationClosed ≡ false
literalChainRuleIdentificationClosedIsFalse = refl
