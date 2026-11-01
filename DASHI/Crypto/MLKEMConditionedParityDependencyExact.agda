module DASHI.Crypto.MLKEMConditionedParityDependencyExact where

------------------------------------------------------------------------
-- CONDITIONED-PARITY PUBLIC EQUATIONS: GLOBAL SOURCE DEPENDENCY
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- After conditioning one source parity block, each remaining secret-polynomial
-- NTT scalar component is a linear combination of all 128 source coefficients
-- in the other parity class.  Each public module row sums over all k secret
-- polynomials, and BaseCaseMultiply lets that remaining component contribute to
-- either public output component.  At the formula/dataflow level, therefore,
-- each conditioned public scalar equation potentially depends on the complete
-- 128*k remaining source-variable block.
--
-- Potential dependency is not a nonzero Jacobian theorem: concrete A entries or
-- cancellations may remove numerical influence.  This is the source-formula
-- dependency graph that any local-search claim must refine with stronger facts.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin; zero)

import DASHI.Crypto.MLKEMFIPS203SourceExact as FIPS
import DASHI.Crypto.MLKEMNTTDataflowCouplingExact as NTT

record RemainingSourceVariable (p : FIPS.MLKEMParameters) : Set where
  constructor remainingSourceVariable
  field
    secretPolynomial : Fin (FIPS.k p)
    parityCoefficient : NTT.Index128

open RemainingSourceVariable public

record ConditionedPublicEquation (p : FIPS.MLKEMParameters) : Set where
  constructor conditionedPublicEquation
  field
    publicRow : Fin (FIPS.k p)
    residue : NTT.Index128
    outputComponent : NTT.ResidueComponent

open ConditionedPublicEquation public

------------------------------------------------------------------------
-- Formula-level potential dependency relation.
------------------------------------------------------------------------

data PotentiallyDependsOn {p : FIPS.MLKEMParameters} :
    ConditionedPublicEquation p → RemainingSourceVariable p → Set where
  baseCaseModuleDependency :
    ∀ equation variable → PotentiallyDependsOn equation variable

allConditionedEquationsSeeAllRemainingVariables :
  ∀ {p}
    (equation : ConditionedPublicEquation p)
    (variable : RemainingSourceVariable p) →
  PotentiallyDependsOn equation variable
allConditionedEquationsSeeAllRemainingVariables = baseCaseModuleDependency

------------------------------------------------------------------------
-- Concrete approved-parameter witnesses.
------------------------------------------------------------------------

first512Variable : RemainingSourceVariable FIPS.params512
first512Variable = remainingSourceVariable zero NTT.zeroIndex128

first768Variable : RemainingSourceVariable FIPS.params768
first768Variable = remainingSourceVariable zero NTT.zeroIndex128

first1024Variable : RemainingSourceVariable FIPS.params1024
first1024Variable = remainingSourceVariable zero NTT.zeroIndex128

conditioned512EveryEquationSharesFirstVariable :
  ∀ equation → PotentiallyDependsOn equation first512Variable
conditioned512EveryEquationSharesFirstVariable equation =
  allConditionedEquationsSeeAllRemainingVariables equation first512Variable

conditioned768EveryEquationSharesFirstVariable :
  ∀ equation → PotentiallyDependsOn equation first768Variable
conditioned768EveryEquationSharesFirstVariable equation =
  allConditionedEquationsSeeAllRemainingVariables equation first768Variable

conditioned1024EveryEquationSharesFirstVariable :
  ∀ equation → PotentiallyDependsOn equation first1024Variable
conditioned1024EveryEquationSharesFirstVariable equation =
  allConditionedEquationsSeeAllRemainingVariables equation first1024Variable

------------------------------------------------------------------------
-- Boundary: formula-level complete dependency rules out a naive independent
-- equation partition, but not conditional algebra, cancellations, sparse values,
-- low-rank phenomena, or a more sophisticated recovery algorithm.
------------------------------------------------------------------------
