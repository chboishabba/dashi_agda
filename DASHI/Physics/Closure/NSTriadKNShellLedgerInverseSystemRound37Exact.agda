module DASHI.Physics.Closure.NSTriadKNShellLedgerInverseSystemRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Give the Round-36/37 projective ledger an actual finite bonding map.  A
-- refined shell shadow stores `(I,B)`: internalized owner resource and the
-- unresolved boundary.  One canonical refinement moves exactly half the old
-- boundary into the internal budget, leaving half unresolved.  Therefore the
-- natural coarse projection is
--
--   pi(I,B) = (I - B, 2 B).
--
-- On the canonical shadows we prove exactly
--
--   pi(L_(Q+1)) = L_Q.
--
-- Thus the finite owner ledgers now form a literal inverse-system skeleton,
-- not only a family carrying compatible scalar identities.  The analytic
-- inverse-limit step still requires boundary vanishing/compactness and is not
-- asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadFiniteShellBudgetGluingRound35Exact as Budget

record LedgerShadow : Set where
  constructor ledger-shadow
  field
    internal boundary : ℚ

open LedgerShadow public

ledgerExt : ∀ {left right : LedgerShadow} →
  internal left ≡ internal right →
  boundary left ≡ boundary right →
  left ≡ right
ledgerExt {ledger-shadow a b} {ledger-shadow .a .b} refl refl = refl

canonicalLedger : ℚ → Nat → LedgerShadow
canonicalLedger eta shell =
  ledger-shadow
    (Budget.internalBudget
      (Budget.canonicalFiniteShellBudgetGluing eta shell))
    (Budget.boundaryBudget
      (Budget.canonicalFiniteShellBudgetGluing eta shell))

coarsenLedger : LedgerShadow → LedgerShadow
coarsenLedger shadow =
  ledger-shadow
    (internal shadow - boundary shadow)
    (Sharp.two * boundary shadow)

successorBoundaryDoublesBack : ∀ eta shell →
  Sharp.two * boundary (canonicalLedger eta (suc shell))
  ≡ boundary (canonicalLedger eta shell)
successorBoundaryDoublesBack eta shell =
  trans
    (cong
      (Sharp.two *_)
      (Budget.boundaryBudgetHalves eta shell))
    (solve
      (boundary (canonicalLedger eta shell) ∷ []))

nextGainIsSuccessorBoundary : ∀ eta shell →
  Sharp.requiredHHBadGain eta (suc shell)
  ≡ boundary (canonicalLedger eta (suc shell))
nextGainIsSuccessorBoundary eta shell =
  solve
    ( eta
    ∷ Sharp.inverseDyadicScale (suc shell)
    ∷ [])

successorInternalProjectsBack : ∀ eta shell →
  internal (canonicalLedger eta (suc shell))
    - boundary (canonicalLedger eta (suc shell))
  ≡ internal (canonicalLedger eta shell)
successorInternalProjectsBack eta shell =
  let
    increment = Budget.internalBudgetIncrementIsNextGain eta shell
    incrementAsBoundary :
      internal (canonicalLedger eta (suc shell))
        - internal (canonicalLedger eta shell)
      ≡ boundary (canonicalLedger eta (suc shell))
    incrementAsBoundary =
      trans increment (nextGainIsSuccessorBoundary eta shell)

    exposeIncrement :
      internal (canonicalLedger eta (suc shell))
        - boundary (canonicalLedger eta (suc shell))
      ≡
      internal (canonicalLedger eta shell)
        + (internal (canonicalLedger eta (suc shell))
          - internal (canonicalLedger eta shell))
        - boundary (canonicalLedger eta (suc shell))
    exposeIncrement =
      solve
        ( internal (canonicalLedger eta (suc shell))
        ∷ internal (canonicalLedger eta shell)
        ∷ boundary (canonicalLedger eta (suc shell))
        ∷ [])
  in
  trans
    exposeIncrement
    (trans
      (cong
        (λ delta →
          internal (canonicalLedger eta shell)
          + delta
          - boundary (canonicalLedger eta (suc shell)))
        incrementAsBoundary)
      (solve
        ( internal (canonicalLedger eta shell)
        ∷ boundary (canonicalLedger eta (suc shell))
        ∷ [])))

coarsenCanonicalSuccessor : ∀ eta shell →
  coarsenLedger (canonicalLedger eta (suc shell))
  ≡ canonicalLedger eta shell
coarsenCanonicalSuccessor eta shell =
  ledgerExt
    (successorInternalProjectsBack eta shell)
    (successorBoundaryDoublesBack eta shell)

record ExactShellLedgerInverseSystem (eta : ℚ) : Set where
  field
    shadow : Nat → LedgerShadow
    projection : LedgerShadow → LedgerShadow
    canonicalShadow : ∀ shell → shadow shell ≡ canonicalLedger eta shell
    successorProjects : ∀ shell →
      projection (shadow (suc shell)) ≡ shadow shell

open ExactShellLedgerInverseSystem public

canonicalShellLedgerInverseSystem :
  ∀ eta → ExactShellLedgerInverseSystem eta
canonicalShellLedgerInverseSystem eta = record
  { shadow = canonicalLedger eta
  ; projection = coarsenLedger
  ; canonicalShadow = λ shell → refl
  ; successorProjects = coarsenCanonicalSuccessor eta
  }

shellLedgerInverseSystemClosed : Bool
shellLedgerInverseSystemClosed = true

analyticOwnerLedgerInverseLimitConstructed : Bool
analyticOwnerLedgerInverseLimitConstructed = false

shellLedgerInverseSystemClosedIsTrue :
  shellLedgerInverseSystemClosed ≡ true
shellLedgerInverseSystemClosedIsTrue = refl

analyticOwnerLedgerInverseLimitConstructedIsFalse :
  analyticOwnerLedgerInverseLimitConstructed ≡ false
analyticOwnerLedgerInverseLimitConstructedIsFalse = refl
