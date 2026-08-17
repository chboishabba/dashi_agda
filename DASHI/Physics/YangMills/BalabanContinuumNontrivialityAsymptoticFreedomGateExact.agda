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
-- SOURCE-SCOPE NOTE
--
-- Aizenman--Duminil-Copin is used here as a precise adversarial precedent,
-- not as a universal no-go theorem for every four-dimensional scalar QFT.
-- Their theorem concerns critical/near-critical scaling limits in the
-- nearest-neighbour ferromagnetic Ising / lambda-phi^4_4 universality class.
-- Its role in this module is to demonstrate a concrete failure mode in which
-- a controlled lattice family has a Gaussian continuum scaling limit.  Yang--
-- Mills lies outside those hypotheses; asymptotic freedom is exactly why the
-- perturbative B/C lane is treated as a possible escape mechanism rather than
-- evidence that nontrivial survival is hopeless.
--
-- DASHI CONTRIBUTION
--
-- Nontrivial continuum survival must not float independently of the
-- asymptotic-freedom calculation.  Positive Yang--Mills one-loop flow is a
-- load-bearing INPUT to E3, though by itself it is not a proof of E3.
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

continuumInteractingObservableSurvivalLevel : ProofLevel
continuumInteractingObservableSurvivalLevel = conditional
