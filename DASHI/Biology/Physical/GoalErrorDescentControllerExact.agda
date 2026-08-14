module DASHI.Biology.Physical.GoalErrorDescentControllerExact where

------------------------------------------------------------------------
-- SOURCE-FACING MOTIVATION
-- Nikolai Bessonov, Michael Levin, Nadya Morozova, Natalia Reinberg,
-- Alen Tosenberger, Vitaly Volpert,
-- "Target morphology and cell memory: a model of regenerative pattern
-- formation", Neural Regeneration Research 10 (2015), 1901-1905.
-- DOI: 10.4103/1673-5374.165216.
--
-- Finite exact controller: every positive defect decreases by one, the target
-- is fixed, and distinct bounded perturbations recover to the same goal.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

Defect : Set
Defect = Nat

repairStep : Defect → Defect
repairStep zero = zero
repairStep (suc n) = n

targetFixed : repairStep zero ≡ zero
targetFixed = refl

positiveDefectStrictlyDecreases :
  (n : Nat) → repairStep (suc n) < suc n
positiveDefectStrictlyDecreases n = ≤-refl

repairTwice : Defect → Defect
repairTwice x = repairStep (repairStep x)

oneStepRecovery : repairStep 1 ≡ 0
oneStepRecovery = refl

twoStepRecovery : repairTwice 2 ≡ 0
twoStepRecovery = refl

------------------------------------------------------------------------
-- A finite basin with multiple perturbation trajectories.
------------------------------------------------------------------------

data Perturbation : Set where
  mild severe : Perturbation

perturbTarget : Perturbation → Defect
perturbTarget mild = 1
perturbTarget severe = 2

mildRecovers : repairTwice (perturbTarget mild) ≡ 0
mildRecovers = refl

severeRecovers : repairTwice (perturbTarget severe) ≡ 0
severeRecovers = refl

record BasinWitness : Set where
  constructor basinWitness
  field
    initialDefect : Defect
    recoveredAfterTwo : repairTwice initialDefect ≡ 0

open BasinWitness public

mildBasin severeBasin : BasinWitness
mildBasin = basinWitness 1 refl
severeBasin = basinWitness 2 refl

------------------------------------------------------------------------
-- Policy degeneracy: distinct first actions/paths can reach the same endpoint.
------------------------------------------------------------------------

data LocalPolicy : Set where
  direct staged : LocalPolicy

policyOutcome : LocalPolicy → Defect → Defect
policyOutcome direct x = repairStep x
policyOutcome staged x = repairTwice x

directFromOneHitsTarget : policyOutcome direct 1 ≡ 0
directFromOneHitsTarget = refl

stagedFromTwoHitsTarget : policyOutcome staged 2 ≡ 0
stagedFromTwoHitsTarget = refl

-- This is deliberately a finite descent certificate, not a theorem that real
-- morphogenesis globally minimizes one scalar energy function.
