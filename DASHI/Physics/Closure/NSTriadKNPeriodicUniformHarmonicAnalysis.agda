module DASHI.Physics.Closure.NSTriadKNPeriodicUniformHarmonicAnalysis where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Venue/year: Grundlehren der mathematischen Wissenschaften 343,
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
-- Uses: Chapter 2, Littlewood--Paley theory, Bernstein inequalities,
-- paraproducts and Fourier multipliers.
-- Relationship: adapts these standard estimates to the periodic,
-- duplicate-free finite Fourier carrier with constants outside the cutoff.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator estimates and the Euler and Navier-Stokes equations".
-- Venue/year: Communications on Pure and Applied Mathematics 41 (1988),
-- 891--907.
-- DOI: 10.1002/cpa.3160410704.
-- Uses: commutator estimate mechanism.
-- Relationship: adapts the multiplier-commutator gain to dyadic shells.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.Base using (_≤_)

record PeriodicUniformHarmonicAnalysis {c s : Level} :
    Set (lsuc (c ⊔ s)) where
  field
    Cutoff : Set c
    State : Set s

    physicalL2Squared fourierL2Squared :
      Cutoff → State → Nat
    weightedConvolutionNorm inputProductNorm :
      Cutoff → State → Nat
    shellL2 shellLInfinity shellVorticityInfinity :
      Nat → Cutoff → State → Nat
    biotSavartVelocity biotSavartVorticity :
      Nat → Cutoff → State → Nat
    shellLatticeCount :
      Nat → Cutoff → Nat
    rowSchur columnSchur schurOperator :
      Cutoff → State → Nat
    commutatorRemainder farHighTail sobolevControl :
      Cutoff → State → Nat

    weightedYoungConstant bernsteinConstant biotSavartConstant : Nat
    shellCountConstant rowSchurConstant columnSchurConstant : Nat
    schurOperatorConstant commutatorConstant tailConstant : Nat

    periodicParseval : ∀ N state →
      physicalL2Squared N state ≡ fourierL2Squared N state

    integerShellWeightedConvolutionUniform : ∀ N state →
      weightedConvolutionNorm N state
      ≤ weightedYoungConstant * inputProductNorm N state

    shellBernsteinUniform : ∀ shell N state →
      shellLInfinity shell N state
      ≤ bernsteinConstant * shellL2 shell N state

    shellVorticityBernstein : ∀ shell N state →
      shellVorticityInfinity shell N state
      ≤ bernsteinConstant * shellLInfinity shell N state

    shellBiotSavartUniform : ∀ shell N state →
      biotSavartVelocity shell N state
      ≤ biotSavartConstant * biotSavartVorticity shell N state

    duplicateFreeShellCounting : ∀ shell N →
      shellLatticeCount shell N ≤ shellCountConstant

    fullShellRowSchurUniform : ∀ N state →
      rowSchur N state
      ≤ rowSchurConstant * sobolevControl N state

    fullShellColumnSchurUniform : ∀ N state →
      columnSchur N state
      ≤ columnSchurConstant * sobolevControl N state

    fullShellSchurOperatorBound : ∀ N state →
      schurOperator N state
      ≤ schurOperatorConstant * sobolevControl N state

    lowHighMultiplierCommutatorIdentity : ∀ N state →
      commutatorRemainder N state
      ≤ commutatorConstant * sobolevControl N state

    farHighSobolevTailGainsRadius : ∀ N state →
      farHighTail N state
      ≤ tailConstant * sobolevControl N state

open PeriodicUniformHarmonicAnalysis public

uniformHarmonicAnalysisTheoremSurfaceImplemented : Bool
uniformHarmonicAnalysisTheoremSurfaceImplemented = true

uniformHarmonicAnalysisTheoremSurfaceImplementedIsTrue :
  uniformHarmonicAnalysisTheoremSurfaceImplemented ≡ true
uniformHarmonicAnalysisTheoremSurfaceImplementedIsTrue = refl

uniformHarmonicAnalysisPackageClosed : Bool
uniformHarmonicAnalysisPackageClosed = false

uniformHarmonicAnalysisPackageClosedIsFalse :
  uniformHarmonicAnalysisPackageClosed ≡ false
uniformHarmonicAnalysisPackageClosedIsFalse = refl
