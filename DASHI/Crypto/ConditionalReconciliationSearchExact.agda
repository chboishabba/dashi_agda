module DASHI.Crypto.ConditionalReconciliationSearchExact where

------------------------------------------------------------------------
-- CONDITIONAL RECONCILIATION SEARCH
--
-- A connected local-constraint graph does not force Cartesian reconciliation.
-- If fixing one local block functionally determines a compatible mate in the
-- other block, search can enumerate only the outer block and construct the mate
-- directly.  This is the precise positive seam left open by the Round-17 NTT
-- coupling no-go.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Crypto.SearchFactorisationExact as Search

record LeftConditionedMate
    (problem : Search.FactorizedSearchProblem) : Set₁ where
  constructor leftConditionedMate
  field
    mate : Search.Left problem → Search.Right problem
    rightValidFromLeft : ∀ left →
      Search.LocalL problem left →
      Search.LocalR problem (mate left)
    reconcilesFromLeft : ∀ left →
      Search.LocalL problem left →
      Search.Reconcile problem left (mate left)

open LeftConditionedMate public

leftCandidateGivesReconciledLocals :
  ∀ {problem : Search.FactorizedSearchProblem}
    (conditional : LeftConditionedMate problem)
    (left : Search.Left problem) →
  Search.LocalL problem left →
  Search.ReconciledLocalSolutions problem
leftCandidateGivesReconciledLocals conditional left leftValid =
  Search.reconciledLocalSolutions
    (Search.localSolutions
      left
      (mate conditional left)
      leftValid
      (rightValidFromLeft conditional left leftValid))
    (reconcilesFromLeft conditional left leftValid)

leftCandidateGivesGlobal :
  ∀ {problem : Search.FactorizedSearchProblem}
    (assembly : Search.Assembly problem)
    (conditional : LeftConditionedMate problem)
    (left : Search.Left problem)
    (leftValid : Search.LocalL problem left) →
  Search.Global problem
    (Search.assemble assembly left (mate conditional left))
leftCandidateGivesGlobal assembly conditional left leftValid =
  Search.reconciledLocalSolutionsGiveGlobal
    assembly
    (leftCandidateGivesReconciledLocals conditional left leftValid)

------------------------------------------------------------------------
-- Cost layer.
--
-- If n outer candidates are enumerated and each conditional mate/reconciliation
-- costs T_cond, the conditional route costs n*T_cond rather than n_L*n_R*T_C.
-- Local enumeration cost may be added separately by the application.
------------------------------------------------------------------------

conditionalMateWork : Nat → Nat → Nat
conditionalMateWork outerCandidates conditionalCost =
  outerCandidates * conditionalCost

cartesianPairWork : Nat → Nat → Nat → Nat
cartesianPairWork leftCandidates rightCandidates perPairCost =
  (leftCandidates * rightCandidates) * perPairCost

conditionalThreeByFive : conditionalMateWork 3 4 ≡ 12
conditionalThreeByFive = refl

cartesianThreeByFive : cartesianPairWork 3 5 2 ≡ 30
cartesianThreeByFive = refl

------------------------------------------------------------------------
-- Boundary: Round 17's structural connectedness result therefore does not end
-- the search programme.  The concrete ML-KEM question becomes whether one can
-- supply a conditional mate/reconciliation theorem with a genuinely lower cost
-- on the actual transported prior and public equations.
------------------------------------------------------------------------
