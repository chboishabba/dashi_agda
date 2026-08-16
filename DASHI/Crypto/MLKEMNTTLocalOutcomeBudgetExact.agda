module DASHI.Crypto.MLKEMNTTLocalOutcomeBudgetExact where

------------------------------------------------------------------------
-- ML-KEM NTT: FINITE LOCAL-OUTCOME SUPPORT BUDGET
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- This file discharges one layer beneath
-- MLKEMNTTSingularBudgetUncertaintyExact.  Instead of accepting
--
--   harmonicSupport <= survivingSupport + singularBudget
--
-- as an opaque numeric premise, we classify every local quadratic residue by
-- one of the only admissible outcomes:
--
--   inactive / regular,
--   inactive / singular,
--   active and survives / regular,
--   active and survives / singular,
--   active and killed / singular.
--
-- There is deliberately NO constructor for "active and killed / regular".
-- That impossible case is exactly the local-injectivity theorem which the
-- FIPS-specific linear-algebra layer must justify.  Once the finite family is
-- represented by this proof-refined outcome type, the support-budget inequality
-- is structural and follows by pointwise counting.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat using (Nat; zero; suc; _+_; _≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP

------------------------------------------------------------------------
-- Proof-refined local outcome alphabet.
------------------------------------------------------------------------

data LocalResidueOutcome : Set where
  inactiveRegular
  inactiveSingular
  activeSurvivesRegular
  activeSurvivesSingular
  activeKilledSingular : LocalResidueOutcome

activeWeight : LocalResidueOutcome → Nat
activeWeight inactiveRegular = 0
activeWeight inactiveSingular = 0
activeWeight activeSurvivesRegular = 1
activeWeight activeSurvivesSingular = 1
activeWeight activeKilledSingular = 1

survivingWeight : LocalResidueOutcome → Nat
survivingWeight inactiveRegular = 0
survivingWeight inactiveSingular = 0
survivingWeight activeSurvivesRegular = 1
survivingWeight activeSurvivesSingular = 1
survivingWeight activeKilledSingular = 0

singularWeight : LocalResidueOutcome → Nat
singularWeight inactiveRegular = 0
singularWeight inactiveSingular = 1
singularWeight activeSurvivesRegular = 0
singularWeight activeSurvivesSingular = 1
singularWeight activeKilledSingular = 1

-- Pointwise charge is exactly "surviving + singular" at one residue.  A
-- surviving singular residue is charged twice, matching the robust upper bound
-- rather than trying to partition the two sets.
budgetWeight : LocalResidueOutcome → Nat
budgetWeight outcome = survivingWeight outcome + singularWeight outcome

localActiveWithinBudget :
  (outcome : LocalResidueOutcome) →
  activeWeight outcome ≤ budgetWeight outcome
localActiveWithinBudget inactiveRegular = z≤n
localActiveWithinBudget inactiveSingular = z≤n
localActiveWithinBudget activeSurvivesRegular = s≤s z≤n
localActiveWithinBudget activeSurvivesSingular = s≤s z≤n
localActiveWithinBudget activeKilledSingular = s≤s z≤n

------------------------------------------------------------------------
-- Finite-family counting.
------------------------------------------------------------------------

sumWeight : (LocalResidueOutcome → Nat) → List LocalResidueOutcome → Nat
sumWeight weight [] = 0
sumWeight weight (outcome ∷ rest) =
  weight outcome + sumWeight weight rest

activeCount : List LocalResidueOutcome → Nat
activeCount = sumWeight activeWeight

survivingCount : List LocalResidueOutcome → Nat
survivingCount = sumWeight survivingWeight

singularCount : List LocalResidueOutcome → Nat
singularCount = sumWeight singularWeight

-- This is the pointwise-summed form of survivingSupport + singularBudget.
-- Keeping the sum pointwise avoids importing any additional finite-set/cardinal
-- machinery into this small theorem layer.
budgetCount : List LocalResidueOutcome → Nat
budgetCount = sumWeight budgetWeight

activeCountWithinBudget :
  (outcomes : List LocalResidueOutcome) →
  activeCount outcomes ≤ budgetCount outcomes
activeCountWithinBudget [] = z≤n
activeCountWithinBudget (outcome ∷ rest) =
  NatP.+-mono-≤
    (localActiveWithinBudget outcome)
    (activeCountWithinBudget rest)

------------------------------------------------------------------------
-- Direct uncertainty composition for a proof-refined finite local family.
------------------------------------------------------------------------

finiteOutcomeBudgetUncertainty128 :
  (sourceSupport : Nat) →
  (outcomes : List LocalResidueOutcome) →
  128 ≤ sourceSupport * activeCount outcomes →
  128 ≤ sourceSupport * budgetCount outcomes
finiteOutcomeBudgetUncertainty128 sourceSupport outcomes uncertainty128 =
  NatP.≤-trans
    uncertainty128
    (NatP.*-monoʳ-≤ sourceSupport (activeCountWithinBudget outcomes))

------------------------------------------------------------------------
-- Boundary: this layer proves the counting theorem, not the local matrix law.
-- The missing FIPS-specific constructor is a classifier which, from the actual
-- local public matrix and transformed perturbation at residue i, returns one of
-- the five outcomes above.  Its regular-active-killed branch must be impossible
-- by local injectivity/full-rank linear algebra.
------------------------------------------------------------------------
