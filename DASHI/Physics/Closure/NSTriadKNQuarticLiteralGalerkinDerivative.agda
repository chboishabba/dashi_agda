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
    energyLinear energyNonlinear : C3.Carrier F
    coherenceLinear coherenceNonlinear : C3.Carrier F
    correctionLinear correctionNonlinear : C3.Carrier F

    energyNonlinearVanishes :
      energyNonlinear ≡ C3.zero F

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

open LiteralQuarticGalerkinLieData public

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
