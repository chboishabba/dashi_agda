module DASHI.Foundations.TernaryWitnessIndependentRepresentation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.TernaryElementaryOperatorCandidate

------------------------------------------------------------------------
-- A generated unit must be reusable independently of the particular admissible
-- witness value occupying its distinguished variable.

record ReusableWitnessUnit (M : TernaryModel) : Set₁ where
  field
    witnessVariable : Var
    unitValue : CarrierT M
    unitTree : TernaryExpr
    AdmissibleEnvironment : TEnv M → Set

    unitTreeCorrect :
      ∀ ρ →
      AdmissibleEnvironment ρ →
      evalTernary M ρ unitTree ≡ unitValue

    witnessIndependent :
      ∀ ρ σ →
      AdmissibleEnvironment ρ →
      AdmissibleEnvironment σ →
      evalTernary M ρ unitTree ≡ evalTernary M σ unitTree

open ReusableWitnessUnit public

reusableUnitFromDiagonal :
  ∀ (M : TernaryModel) →
  (C : DiagonalUnitCandidate M) →
  (witness : Var) →
  ReusableWitnessUnit M
reusableUnitFromDiagonal M C witness =
  record
    { witnessVariable = witness
    ; unitValue = unit C
    ; unitTree = generatedUnit witness
    ; AdmissibleEnvironment =
        λ ρ → AdmissibleDiagonal C (ρ witness)
    ; unitTreeCorrect =
        λ ρ admissible →
          generatedUnit-correct M C ρ witness admissible
    ; witnessIndependent =
        λ ρ σ admissibleρ admissibleσ →
          trans
            (generatedUnit-correct M C ρ witness admissibleρ)
            (sym
              (generatedUnit-correct M C σ witness admissibleσ))
    }

------------------------------------------------------------------------
-- Context reduction for the full ternary theorem.
--
-- Once one constant-free tree represents 1, variables are embedded, and one
-- ternary context implements the EML node on already-correct child trees, the
-- complete translation follows by structural recursion.

record TernaryEMLContexts
  (TM : TernaryModel)
  (EM : ExpLogSubModel) : Set₁ where
  field
    embedCarrierC : Carrier EM → CarrierT TM

    unitTreeC : TernaryExpr
    variableTreeC : Var → TernaryExpr
    emlContextC : TernaryExpr → TernaryExpr → TernaryExpr

    unitTreeCorrectC :
      ∀ (ρ : Env EM) (ρT : TEnv TM) →
      (∀ x → ρT x ≡ embedCarrierC (ρ x)) →
      evalTernary TM ρT unitTreeC
      ≡ embedCarrierC (one EM)

    variableTreeCorrectC :
      ∀ (ρ : Env EM) (ρT : TEnv TM) →
      (∀ x → ρT x ≡ embedCarrierC (ρ x)) →
      ∀ x →
      evalTernary TM ρT (variableTreeC x)
      ≡ embedCarrierC (ρ x)

    emlContextCorrectC :
      ∀ (ρT : TEnv TM)
        (leftTree rightTree : TernaryExpr)
        (x y : Carrier EM) →
      evalTernary TM ρT leftTree ≡ embedCarrierC x →
      evalTernary TM ρT rightTree ≡ embedCarrierC y →
      evalTernary TM ρT (emlContextC leftTree rightTree)
      ≡ embedCarrierC (eml EM x y)

open TernaryEMLContexts public

translateByContexts :
  ∀ {TM : TernaryModel} {EM : ExpLogSubModel} →
  TernaryEMLContexts TM EM →
  EMLExpr → TernaryExpr
translateByContexts C oneM = unitTreeC C
translateByContexts C (varM x) = variableTreeC C x
translateByContexts C (emlM s t) =
  emlContextC C
    (translateByContexts C s)
    (translateByContexts C t)

translateByContexts-correct :
  ∀ {TM : TernaryModel} {EM : ExpLogSubModel} →
  (C : TernaryEMLContexts TM EM) →
  ∀ (ρ : Env EM) (ρT : TEnv TM) →
  (compatible : ∀ x → ρT x ≡ embedCarrierC C (ρ x)) →
  ∀ t →
  evalTernary TM ρT (translateByContexts C t)
  ≡ embedCarrierC C (evalEML EM ρ t)
translateByContexts-correct C ρ ρT compatible oneM =
  unitTreeCorrectC C ρ ρT compatible
translateByContexts-correct C ρ ρT compatible (varM x) =
  variableTreeCorrectC C ρ ρT compatible x
translateByContexts-correct C ρ ρT compatible (emlM s t) =
  emlContextCorrectC C ρT
    (translateByContexts C s)
    (translateByContexts C t)
    (evalEML _ ρ s)
    (evalEML _ ρ t)
    (translateByContexts-correct C ρ ρT compatible s)
    (translateByContexts-correct C ρ ρT compatible t)

contextsGiveTernaryRepresentation :
  ∀ {TM : TernaryModel} {EM : ExpLogSubModel} →
  TernaryEMLContexts TM EM →
  TernaryRepresentsEML TM EM
contextsGiveTernaryRepresentation C =
  record
    { embedCarrier = embedCarrierC C
    ; translate = translateByContexts C
    ; translate-correct =
        λ ρ ρT compatible t →
          translateByContexts-correct C ρ ρT compatible t
    }

record TernaryCompletenessCut
  (TM : TernaryModel)
  (EM : ExpLogSubModel) : Set₁ where
  field
    reusableUnit : ReusableWitnessUnit TM
    contexts : TernaryEMLContexts TM EM
    representation : TernaryRepresentsEML TM EM
    representationIsFromContexts :
      representation ≡ contextsGiveTernaryRepresentation contexts

open TernaryCompletenessCut public
