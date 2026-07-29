module DASHI.Physics.Closure.NSTriadKNOutputRelocationFiniteSquaredCoefficientMajorant where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz; Sergei
-- Bernstein; Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin; Raphael
-- Danchin; Loukas Grafakos; Seungly Oh; DASHI repository contributors.
-- Title: "The Kato-Ponce Inequality"; "Fourier Analysis and Nonlinear
-- Partial Differential Equations"; and "Exact finite squared coefficient
-- majorant for the output-relocation shell".
-- Venue/year: Communications in Partial Differential Equations 39 (2014),
-- 1128--1157; Springer, 2011; DASHI formal development, 2026.
-- DOI: 10.1080/03605302.2013.822885;
-- 10.1007/978-3-642-16830-7; the repository finite theorem has no DOI.
-- Uses: the existing exact rational finite Cauchy--Schwarz theorem, the
-- restricted resonant output-fibre model, multiplier-square domination and
-- the shell-cardinality collapse already proved in DASHI.
-- Relationship: closes the finite squared analytic core of the literal
-- output-low estimate.  It deliberately stops before taking square roots or
-- identifying a native constructive-real coefficient with the rational fibre
-- realization; those transports are proved in sibling bridge modules.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)
open import Data.Rational.Base using (ℚ; 1ℚ; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNRationalDirectConvolutionBound as Direct

unitFibreMajorantSquared :
  ∀ {multiplier pairs} →
  Direct.FibreMajorant 1ℚ 1ℚ 1ℚ multiplier pairs →
  Direct.fibreValueSquared multiplier pairs ≤ 1ℚ
unitFibreMajorantSquared {multiplier} {pairs} majorant =
  subst
    (λ upper → Direct.fibreValueSquared multiplier pairs ≤ upper)
    (solve [])
    (Direct.fibreMajorantSquared majorant)

unitOutputFibreSquared :
  Direct.OutputFibre 1ℚ 1ℚ 1ℚ → ℚ
unitOutputFibreSquared = Direct.outputFibreSquared

unitOutputShellSquared :
  List (Direct.OutputFibre 1ℚ 1ℚ 1ℚ) → ℚ
unitOutputShellSquared = Direct.sumOutputFibreSquares

unitOutputShellMajorantSquared :
  ∀ {outputs} →
  (cardinality : Direct.ShellCardinalityMajorant
    {1ℚ} {1ℚ} {1ℚ} outputs) →
  unitOutputShellSquared outputs
  ≤ Direct.shellCardinalityFactor cardinality
unitOutputShellMajorantSquared {outputs} cardinality =
  subst
    (λ upper → unitOutputShellSquared outputs ≤ upper)
    (solve (Direct.shellCardinalityFactor cardinality ∷ []))
    (Direct.finiteLowOutputShellBoundSquared cardinality)

record FiniteOutputRelocationSquaredModel : Set where
  field
    outputs : List (Direct.OutputFibre 1ℚ 1ℚ 1ℚ)
    cardinality : Direct.ShellCardinalityMajorant
      {1ℚ} {1ℚ} {1ℚ} outputs

open FiniteOutputRelocationSquaredModel public

finiteModelSquaredBound :
  (model : FiniteOutputRelocationSquaredModel) →
  unitOutputShellSquared (outputs model)
  ≤ Direct.shellCardinalityFactor (cardinality model)
finiteModelSquaredBound model =
  unitOutputShellMajorantSquared (cardinality model)

finiteSquaredOutputCoefficientMajorantClosed : Bool
finiteSquaredOutputCoefficientMajorantClosed = true

finiteSquaredOutputCoefficientMajorantClosedIsTrue :
  finiteSquaredOutputCoefficientMajorantClosed ≡ true
finiteSquaredOutputCoefficientMajorantClosedIsTrue = refl
