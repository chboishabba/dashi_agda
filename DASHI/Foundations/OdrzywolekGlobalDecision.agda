module DASHI.Foundations.OdrzywolekGlobalDecision where

open import Agda.Builtin.Equality using (_≡_; refl; subst; trans)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.TernaryElementaryOperatorCandidate
open import DASHI.Foundations.TernaryEMLDecision using (TernaryDomainObstruction)

------------------------------------------------------------------------
-- The intended ordinary model uses the same scalar carrier for EML and T.  This
-- identity-carrier formulation prevents an exotic embedding from hiding the
-- actual functional-completeness question.

record SharedTernaryEMLModel : Set₁ where
  field
    Value : Set
    one : Value
    exp log : Value → Value
    sub : Value → Value → Value
    ternary : Value → Value → Value → Value

  emlModel : ExpLogSubModel
  emlModel =
    record
      { Carrier = Value
      ; one = one
      ; exp = exp
      ; log = log
      ; sub = sub
      }

  ternaryModel : TernaryModel
  ternaryModel =
    record
      { CarrierT = Value
      ; ternary = ternary
      }

open SharedTernaryEMLModel public

record IdentityTernaryRepresentsEML
  (M : SharedTernaryEMLModel) : Set₁ where
  field
    translate : EMLExpr → TernaryExpr
    translateCorrect : ∀ ρ t →
      evalTernary (ternaryModel M) ρ (translate t)
      ≡ evalEML (emlModel M) ρ t

open IdentityTernaryRepresentsEML public

cong₃ :
  ∀ {A B C D : Set}
    (f : A → B → C → D)
    {a a′ b b′ c c′} →
  a ≡ a′ → b ≡ b′ → c ≡ c′ →
  f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

evalTernaryEnvironmentCongruent :
  ∀ {M : SharedTernaryEMLModel}
    (ρ σ : Var → Value M) →
  (∀ x → ρ x ≡ σ x) →
  ∀ t →
  evalTernary (ternaryModel M) ρ t
  ≡ evalTernary (ternaryModel M) σ t
evalTernaryEnvironmentCongruent ρ σ agree (varT x) = agree x
evalTernaryEnvironmentCongruent {M} ρ σ agree (nodeT a b c) =
  cong₃
    (ternary M)
    (evalTernaryEnvironmentCongruent ρ σ agree a)
    (evalTernaryEnvironmentCongruent ρ σ agree b)
    (evalTernaryEnvironmentCongruent ρ σ agree c)

identityRepresentationPromotes :
  ∀ {M : SharedTernaryEMLModel} →
  IdentityTernaryRepresentsEML M →
  TernaryRepresentsEML (ternaryModel M) (emlModel M)
identityRepresentationPromotes {M} R =
  record
    { embedCarrier = λ x → x
    ; translate = translate R
    ; translate-correct = λ ρ ρT agreement t →
        trans
          (evalTernaryEnvironmentCongruent ρT ρ agreement (translate R t))
          (translateCorrect R ρ t)
    }

------------------------------------------------------------------------
-- A semantic invariant gives a genuine global impossibility theorem when it is
-- preserved by every T-node but violated by one EML target under one admissible
-- environment.

record TernarySemanticInvariant
  (M : SharedTernaryEMLModel) : Set₁ where
  field
    Invariant : Value M → Set
    preservedByTernary : ∀ {x y z} →
      Invariant x →
      Invariant y →
      Invariant z →
      Invariant (ternary M x y z)

open TernarySemanticInvariant public

allTernaryTreesPreserveInvariant :
  ∀ {M : SharedTernaryEMLModel}
    (I : TernarySemanticInvariant M)
    (ρ : Var → Value M) →
  (∀ x → Invariant I (ρ x)) →
  ∀ t →
  Invariant I (evalTernary (ternaryModel M) ρ t)
allTernaryTreesPreserveInvariant I ρ variables (varT x) = variables x
allTernaryTreesPreserveInvariant I ρ variables (nodeT a b c) =
  preservedByTernary I
    (allTernaryTreesPreserveInvariant I ρ variables a)
    (allTernaryTreesPreserveInvariant I ρ variables b)
    (allTernaryTreesPreserveInvariant I ρ variables c)

record GlobalInvariantObstruction
  (M : SharedTernaryEMLModel) : Set₁ where
  field
    invariant : TernarySemanticInvariant M
    environment : Var → Value M
    variablesSatisfyInvariant : ∀ x →
      Invariant invariant (environment x)
    target : EMLExpr
    targetViolatesInvariant :
      Invariant invariant (evalEML (emlModel M) environment target) → ⊥

open GlobalInvariantObstruction public

invariantObstructionRefutesIdentityUniversality :
  ∀ {M : SharedTernaryEMLModel} →
  GlobalInvariantObstruction M →
  IdentityTernaryRepresentsEML M →
  ⊥
invariantObstructionRefutesIdentityUniversality {M} O R =
  targetViolatesInvariant O
    (subst
      (Invariant (invariant O))
      (translateCorrect R (environment O) (target O))
      treeInvariant)
  where
    treeInvariant :
      Invariant (invariant O)
        (evalTernary
          (ternaryModel M)
          (environment O)
          (translate R (target O)))
    treeInvariant =
      allTernaryTreesPreserveInvariant
        (invariant O)
        (environment O)
        (variablesSatisfyInvariant O)
        (translate R (target O))

------------------------------------------------------------------------
-- Global research outcome for the intended shared scalar carrier.

data GlobalTernaryEMLDecision
  (M : SharedTernaryEMLModel) : Set₁ where
  globallyRepresented :
    IdentityTernaryRepresentsEML M →
    GlobalTernaryEMLDecision M

  globallyInvariantRefuted :
    GlobalInvariantObstruction M →
    GlobalTernaryEMLDecision M

  generatedUnitRouteRefuted :
    TernaryDomainObstruction →
    GlobalTernaryEMLDecision M

record BoundedRefutationPromotion
  (M : SharedTernaryEMLModel) : Set₁ where
  field
    depth : Nat
    CandidateAtDepth : TernaryExpr → Set
    target : EMLExpr
    RepresentsTarget : TernaryExpr → Set
    Covered : TernaryExpr → Set

    exhaustive : ∀ t → CandidateAtDepth t → Covered t
    noCandidateRepresents : ∀ t →
      Covered t →
      RepresentsTarget t →
      ⊥

open BoundedRefutationPromotion public
