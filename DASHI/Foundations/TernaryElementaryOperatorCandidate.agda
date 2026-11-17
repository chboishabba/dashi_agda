module DASHI.Foundations.TernaryElementaryOperatorCandidate where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat)
open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)

open import DASHI.Foundations.ElementarySingleOperator
  using (Var; ExpLogSubModel; Carrier; Env; EMLExpr; evalEML)

------------------------------------------------------------------------
-- Three typed child slots reuse the repository's canonical TriTruth carrier.
-- This is an arity/address use only: it does not identify complex numbers with
-- balanced ternary values.

leftSlot middleSlot rightSlot : TriTruth
leftSlot = tri-low
middleSlot = tri-mid
rightSlot = tri-high

data TernaryExpr : Set where
  varT : Var → TernaryExpr
  nodeT : TernaryExpr → TernaryExpr → TernaryExpr → TernaryExpr

record TernaryModel : Set₁ where
  field
    CarrierT : Set
    ternary : CarrierT → CarrierT → CarrierT → CarrierT

open TernaryModel public

TEnv : TernaryModel → Set
TEnv M = Var → CarrierT M

evalTernary :
  (M : TernaryModel) →
  TEnv M →
  TernaryExpr →
  CarrierT M
evalTernary M ρ (varT x) = ρ x
evalTernary M ρ (nodeT a b c) =
  ternary M
    (evalTernary M ρ a)
    (evalTernary M ρ b)
    (evalTernary M ρ c)

------------------------------------------------------------------------
-- Constant-free unit generation.

record DiagonalUnitCandidate (M : TernaryModel) : Set₁ where
  field
    unit : CarrierT M
    AdmissibleDiagonal : CarrierT M → Set
    diagonalUnit :
      ∀ x →
      AdmissibleDiagonal x →
      ternary M x x x ≡ unit

open DiagonalUnitCandidate public

generatedUnit : Var → TernaryExpr
generatedUnit x = nodeT (varT x) (varT x) (varT x)

generatedUnit-correct :
  ∀ (M : TernaryModel) →
  (C : DiagonalUnitCandidate M) →
  (ρ : TEnv M) →
  (x : Var) →
  AdmissibleDiagonal C (ρ x) →
  evalTernary M ρ (generatedUnit x) ≡ unit C
generatedUnit-correct M C ρ x admissible =
  diagonalUnit C (ρ x) admissible

------------------------------------------------------------------------
-- Exact analytic formula named in arXiv:2603.21852v2:
--
--   T(x,y,z) = (exp x / log x) * (log z / exp y).
--
-- The paper labels this a candidate and says the dedicated analysis is in
-- preparation.  We therefore expose the formula and its exact proof boundary,
-- rather than asserting unconditional functional completeness.

record ExpLogDivisionModel : Set₁ where
  field
    Scalar : Set
    oneS : Scalar
    expS : Scalar → Scalar
    logS : Scalar → Scalar
    mulS : Scalar → Scalar → Scalar
    divS : Scalar → Scalar → Scalar

open ExpLogDivisionModel public

odrzywolekTernary :
  (M : ExpLogDivisionModel) →
  Scalar M →
  Scalar M →
  Scalar M →
  Scalar M
odrzywolekTernary M x y z =
  mulS M
    (divS M (expS M x) (logS M x))
    (divS M (logS M z) (expS M y))

odrzywolekTernaryModel :
  (M : ExpLogDivisionModel) →
  TernaryModel
CarrierT (odrzywolekTernaryModel M) = Scalar M
ternary (odrzywolekTernaryModel M) = odrzywolekTernary M

record OdrzywolekDiagonalLaws (M : ExpLogDivisionModel) : Set₁ where
  field
    Admissible : Scalar M → Set
    diagonalIsOne :
      ∀ x →
      Admissible x →
      odrzywolekTernary M x x x ≡ oneS M

open OdrzywolekDiagonalLaws public

odrzywolekDiagonalCandidate :
  ∀ (M : ExpLogDivisionModel) →
  OdrzywolekDiagonalLaws M →
  DiagonalUnitCandidate (odrzywolekTernaryModel M)
unit (odrzywolekDiagonalCandidate M laws) = oneS M
AdmissibleDiagonal (odrzywolekDiagonalCandidate M laws) = Admissible laws
diagonalUnit (odrzywolekDiagonalCandidate M laws) = diagonalIsOne laws

------------------------------------------------------------------------
-- The missing universality cut is stated as a translator, not hidden in a
-- status flag.  Once a ternary tree can represent every EML tree and preserve
-- evaluation, constant-free universality follows by composition with the EML
-- compiler theorem.

record TernaryRepresentsEML
  (TM : TernaryModel)
  (EM : ExpLogSubModel)
  : Set₁ where
  field
    embedCarrier : Carrier EM → CarrierT TM
    translate : EMLExpr → TernaryExpr
    translate-correct :
      ∀ (ρ : Env EM) (ρT : TEnv TM) →
      (∀ x → ρT x ≡ embedCarrier (ρ x)) →
      ∀ t →
      evalTernary TM ρT (translate t)
      ≡ embedCarrier (evalEML EM ρ t)

open TernaryRepresentsEML public

data TernaryCandidateStatus : Set where
  exactFormulaRecorded : TernaryCandidateStatus
  diagonalUnitBoundaryRecorded : TernaryCandidateStatus
  emlTranslationStillRequired : TernaryCandidateStatus
