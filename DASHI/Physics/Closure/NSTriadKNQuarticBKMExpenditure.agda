module DASHI.Physics.Closure.NSTriadKNQuarticBKMExpenditure where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the breakdown of smooth solutions for the 3-D Euler
-- equations".
-- Venue/year: Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01212349.
-- Uses: vorticity-infinity continuation criterion.
-- Relationship: adapts the continuation endpoint to cutoff-uniform periodic
-- Galerkin approximations; it does not attribute the new weighted-shell
-- expenditure estimate to Beale--Kato--Majda.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Venue/year: Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
-- Uses: Chapter 2 Bernstein inequalities and dyadic summation.
-- Relationship: adapts the shell envelope dominating vorticity infinity.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as Nat

record QuarticControlToUniformBKMExpenditure {c t s : Level} :
    Set (lsuc (c ⊔ t ⊔ s)) where
  field
    Cutoff : Set c
    Time : Set t
    State : Set s

    solution : Cutoff → Time → State
    weightedShellEnvelope :
      Cutoff → Time → State → Nat
    vorticityInfinity :
      Cutoff → Time → State → Nat
    integratedEnvelope integratedVorticity :
      Cutoff → Nat

    bernsteinConstant expenditureBound : Nat

    envelopeDominatesVorticityInfinity : ∀ N time →
      vorticityInfinity N time (solution N time)
      ≤ bernsteinConstant *
        weightedShellEnvelope N time (solution N time)

    integratedBernstein : ∀ N →
      integratedVorticity N
      ≤ bernsteinConstant * integratedEnvelope N

    quarticControlImpliesUniformEnvelopeExpenditure : ∀ N →
      bernsteinConstant * integratedEnvelope N
      ≤ expenditureBound

    BKMContinuation : Cutoff → Set
    finiteVorticityIntegralImpliesContinuation : ∀ N →
      integratedVorticity N ≤ expenditureBound →
      BKMContinuation N

open QuarticControlToUniformBKMExpenditure public

finiteVorticityTimeIntegral :
  ∀ {c t s}
    (B : QuarticControlToUniformBKMExpenditure {c} {t} {s})
    (N : Cutoff B) →
  integratedVorticity B N ≤ expenditureBound B
finiteVorticityTimeIntegral B N =
  Nat.≤-trans
    (integratedBernstein B N)
    (quarticControlImpliesUniformEnvelopeExpenditure B N)

compactGammaBKMContinuation :
  ∀ {c t s}
    (B : QuarticControlToUniformBKMExpenditure {c} {t} {s})
    (N : Cutoff B) →
  BKMContinuation B N
compactGammaBKMContinuation B N =
  finiteVorticityIntegralImpliesContinuation B N
    (finiteVorticityTimeIntegral B N)

bkmExpenditureCompositionImplemented : Bool
bkmExpenditureCompositionImplemented = true

bkmExpenditureCompositionImplementedIsTrue :
  bkmExpenditureCompositionImplemented ≡ true
bkmExpenditureCompositionImplementedIsTrue = refl

quarticControlImpliesUniformBKMExpenditureClosed : Bool
quarticControlImpliesUniformBKMExpenditureClosed = false

quarticControlImpliesUniformBKMExpenditureClosedIsFalse :
  quarticControlImpliesUniformBKMExpenditureClosed ≡ false
quarticControlImpliesUniformBKMExpenditureClosedIsFalse = refl
