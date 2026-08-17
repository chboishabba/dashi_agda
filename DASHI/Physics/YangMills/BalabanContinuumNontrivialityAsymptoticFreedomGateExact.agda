module DASHI.Physics.YangMills.BalabanContinuumNontrivialityAsymptoticFreedomGateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / ADVERSARIAL CONTEXT
--
-- David J. Gross and Frank Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories",
-- Physical Review Letters 30 (1973), 1343--1346.
-- DOI: 10.1103/PhysRevLett.30.1343.
--
-- H. David Politzer,
-- "Reliable Perturbative Results for Strong Interactions?",
-- Physical Review Letters 30 (1973), 1346--1349.
-- DOI: 10.1103/PhysRevLett.30.1346.
--
-- Michael Aizenman and Hugo Duminil-Copin,
-- "Marginal triviality of the scaling limits of critical 4D Ising and
-- phi^4_4 models", Annals of Mathematics 194 (2021), 163--235.
-- DOI: 10.4007/annals.2021.194.1.3.
-- Corrigendum: Annals of Mathematics 199 (2024), 479.
-- DOI: 10.4007/annals.2024.199.1.7.
--
-- DASHI CONTRIBUTION
--
-- Nontrivial continuum survival must not float independently of the
-- asymptotic-freedom calculation.  Four-dimensional scalar phi^4 supplies the
-- exact adversarial failure mode: a controlled lattice family can have a
-- Gaussian scaling limit.  Positive Yang--Mills one-loop flow is therefore a
-- load-bearing INPUT to E3, though by itself it is not a proof of E3.
--
-- This file welds the already-separated B/C quantities algebraically.  If the
-- certified one-loop lower contribution is decomposed as
--
--   oneLoopLower = survivalMargin + quarticPenalty
--
-- and the physical beta quantity is bounded below by
--
--   oneLoopLower - quarticPenalty,
--
-- then the SAME survivalMargin is a lower bound for the physical beta.
-- Thus the finite perturbative programme must leave a nonvanishing margin
-- after the five g^4 channels are charged, before any continuum nontriviality
-- argument can legitimately start.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record AsymptoticFreedomSurvivalMarginData : Set where
  field
    oneLoopLower : ℚ
    quarticPenalty : ℚ
    survivalMargin : ℚ
    physicalBeta : ℚ

    oneLoopSplitsIntoMarginAndPenalty :
      oneLoopLower ≡ survivalMargin + quarticPenalty

    physicalBetaAfterQuarticCharge :
      oneLoopLower - quarticPenalty ≤ physicalBeta
open AsymptoticFreedomSurvivalMarginData public

oneLoopAfterQuarticChargeIsSurvivalMargin :
  ∀ data →
  oneLoopLower data - quarticPenalty data ≡ survivalMargin data
oneLoopAfterQuarticChargeIsSurvivalMargin data =
  trans
    (cong
      (λ selected → selected - quarticPenalty data)
      (oneLoopSplitsIntoMarginAndPenalty data))
    (ℚRing.solve-∀
      (survivalMargin data) (quarticPenalty data))

survivalMarginBelowPhysicalBeta :
  ∀ data → survivalMargin data ≤ physicalBeta data
survivalMarginBelowPhysicalBeta data =
  subst
    (λ lower → lower ≤ physicalBeta data)
    (oneLoopAfterQuarticChargeIsSurvivalMargin data)
    (physicalBetaAfterQuarticCharge data)

asymptoticFreedomQuarticSurvivalMarginLevel : ProofLevel
asymptoticFreedomQuarticSurvivalMarginLevel = machineChecked

-- The hard continuum theorem remains separate: prove that a genuinely
-- interacting gauge-invariant observable/cumulant survives the SAME scaling
-- subsequence.  The theorem above makes positive perturbative flow an upstream
-- quantitative gate; it deliberately does not identify beta>0 with
-- non-Gaussianity.
continuumInteractingObservableSurvivalLevel : ProofLevel
continuumInteractingObservableSurvivalLevel = conditional
