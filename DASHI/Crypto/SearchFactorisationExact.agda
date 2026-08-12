module DASHI.Crypto.SearchFactorisationExact where

------------------------------------------------------------------------
-- SEARCH FACTORISATION
--
-- The central theorem-bearing boundary for verification -> search.  A global
-- verifier may factor into local predicates plus reconciliation, but a simple
-- additive search bound is justified only when reconciliation itself avoids a
-- Cartesian-product search.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)

record _↔_ (A B : Set) : Set where
  constructor iff
  field to : A → B
        from : B → A
open _↔_ public

record FactorizedSearchProblem : Set₁ where
  constructor factorizedSearchProblem
  field
    Hidden Left Right : Set
    ρL : Hidden → Left
    ρR : Hidden → Right
    LocalL : Left → Set
    LocalR : Right → Set
    Reconcile : Left → Right → Set
    Global : Hidden → Set
    globalFactorisation : ∀ h →
      Global h ↔
      (LocalL (ρL h) × (LocalR (ρR h) × Reconcile (ρL h) (ρR h)))

open FactorizedSearchProblem public

record LocalSolutions (problem : FactorizedSearchProblem) : Set₁ where
  constructor localSolutions
  field
    leftSolution : Left problem
    rightSolution : Right problem
    leftValid : LocalL problem leftSolution
    rightValid : LocalR problem rightSolution

open LocalSolutions public

record ReconciledLocalSolutions (problem : FactorizedSearchProblem) : Set₁ where
  constructor reconciledLocalSolutions
  field
    locals : LocalSolutions problem
    compatible : Reconcile problem (leftSolution locals) (rightSolution locals)

open ReconciledLocalSolutions public

-- Application-supplied assembly is the constructive seam from local coordinates
-- back to a hidden state.  It is not implied by local verification alone.
record Assembly (problem : FactorizedSearchProblem) : Set₁ where
  constructor assembly
  field
    assemble : Left problem → Right problem → Hidden problem
    ρL-assemble : ∀ l r → ρL problem (assemble l r) ≡ l
    ρR-assemble : ∀ l r → ρR problem (assemble l r) ≡ r

open Assembly public

------------------------------------------------------------------------
-- Cost laws.  Nat expressions are exact accounting formulas, not claims about
-- any concrete cryptosystem until its enumerators/reconciler instantiate them.
------------------------------------------------------------------------

genericReconciliationBound : Nat → Nat → Nat → Nat → Nat → Nat
genericReconciliationBound T-L T-R n-L n-R T-C =
  T-L + T-R + (n-L * n-R) * T-C

functionalReconciliationBound : Nat → Nat → Nat → Nat
functionalReconciliationBound T-L T-R T-C = T-L + T-R + T-C

record GenericSearchCost : Set where
  constructor genericSearchCost
  field
    localLeftCost localRightCost : Nat
    survivingLeft survivingRight : Nat
    reconcilePerPairCost : Nat

open GenericSearchCost public

totalGenericCost : GenericSearchCost → Nat
totalGenericCost c = genericReconciliationBound
  (localLeftCost c) (localRightCost c)
  (survivingLeft c) (survivingRight c)
  (reconcilePerPairCost c)

record FunctionalReconciliation : Set₁ where
  constructor functionalReconciliation
  field
    Left Right : Set
    mate : Left → Right

open FunctionalReconciliation public

-- Crucial boundary: T_L + T_R + T_C is a valid architecture only when the
-- reconciliation route is supplied without enumerating all n_L*n_R pairs.
record AdditiveSearchCertificate : Set where
  constructor additiveSearchCertificate
  field
    localLeftCost localRightCost reconcileCost : Nat
    certifiedTotal : Nat
    exactTotal : certifiedTotal ≡
      functionalReconciliationBound localLeftCost localRightCost reconcileCost

open AdditiveSearchCertificate public

additiveCertificate : ∀ T-L T-R T-C → AdditiveSearchCertificate
additiveCertificate T-L T-R T-C =
  additiveSearchCertificate T-L T-R T-C
    (functionalReconciliationBound T-L T-R T-C) refl
