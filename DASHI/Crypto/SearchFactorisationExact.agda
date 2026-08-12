module DASHI.Crypto.SearchFactorisationExact where

------------------------------------------------------------------------
-- SEARCH FACTORISATION
--
-- A global verifier may factor into local predicates plus reconciliation, but
-- a simple additive search bound is justified only when reconciliation avoids
-- a Cartesian-product search.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; subst)

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

record Assembly (problem : FactorizedSearchProblem) : Set₁ where
  constructor assembly
  field
    assemble : Left problem → Right problem → Hidden problem
    ρL-assemble : ∀ l r → ρL problem (assemble l r) ≡ l
    ρR-assemble : ∀ l r → ρR problem (assemble l r) ≡ r
open Assembly public

transport₂ :
  ∀ {A B : Set} {P : A → B → Set}
    {a a' : A} {b b' : B} →
  a ≡ a' → b ≡ b' → P a b → P a' b'
transport₂ refl refl proof = proof

-- Main constructive theorem: local enumeration is enough only once we also
-- possess compatible local witnesses and an assembly map back to the hidden
-- carrier.
reconciledLocalSolutionsGiveGlobal :
  ∀ {problem : FactorizedSearchProblem} →
  Assembly problem →
  (solutions : ReconciledLocalSolutions problem) →
  Global problem
    (assemble _
      (leftSolution (locals solutions))
      (rightSolution (locals solutions)))
reconciledLocalSolutionsGiveGlobal {problem} assemblyMap solutions =
  from (globalFactorisation problem hidden)
    (leftProof , (rightProof , couplingProof))
  where
  l = leftSolution (locals solutions)
  r = rightSolution (locals solutions)
  hidden = assemble assemblyMap l r

  leftEq : ρL problem hidden ≡ l
  leftEq = ρL-assemble assemblyMap l r

  rightEq : ρR problem hidden ≡ r
  rightEq = ρR-assemble assemblyMap l r

  leftProof : LocalL problem (ρL problem hidden)
  leftProof = subst (LocalL problem) (sym leftEq) (leftValid (locals solutions))

  rightProof : LocalR problem (ρR problem hidden)
  rightProof = subst (LocalR problem) (sym rightEq) (rightValid (locals solutions))

  couplingProof : Reconcile problem (ρL problem hidden) (ρR problem hidden)
  couplingProof = transport₂ (sym leftEq) (sym rightEq) (compatible solutions)

------------------------------------------------------------------------
-- Exact cost accounting.
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
