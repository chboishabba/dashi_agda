module DASHI.Physics.Closure.NSFactorizedCrossShellBound where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

open import DASHI.Analysis.BlockSchurCoercivity
open import DASHI.Analysis.ThreeStageBoundComposition
open import DASHI.Physics.Closure.NSShellSchurInstance
open import DASHI.Physics.Closure.NSCrossShellSchurBound

record SchurMultiplicativeLaws
    {s : Level}
    (Scalar : Set s)
    (O : SchurOrderLaws Scalar) : Set (lsuc s) where
  field
    schurMultiply : Scalar → Scalar → Scalar
    schur≤-trans :
      ∀ {a b c} → _≤_ O a b → _≤_ O b c → _≤_ O a c
    schurMultiplyMonotoneLeft :
      ∀ left {a b} →
      _≤_ O a b →
      _≤_ O (schurMultiply left a) (schurMultiply left b)

open SchurMultiplicativeLaws public

asMultiplicativeBoundLaws :
  ∀ {s} {Scalar : Set s} {O : SchurOrderLaws Scalar} →
  SchurMultiplicativeLaws Scalar O →
  MultiplicativeBoundLaws Scalar
asMultiplicativeBoundLaws {O = O} M = record
  { _≤_ = _≤_ O
  ; _⊗_ = schurMultiply M
  ; ≤-trans = schur≤-trans M
  ; multiplyMonotoneLeft = schurMultiplyMonotoneLeft M
  }

record NSFactorizedCrossShellEvidence
    {v s : Level}
    {ShellVector : Set v}
    {Scalar : Set s}
    {O : SchurOrderLaws Scalar}
    (M : SchurMultiplicativeLaws Scalar O)
    (I : NSShellSchurStructure ShellVector Scalar O) : Set (lsuc (v ⊔ s)) where
  field
    afterK01 : ShellVector → Scalar
    afterLowResolvent : ShellVector → Scalar
    afterK10 : ShellVector → Scalar
    c01 r0 c10 : Scalar
    correctionControlledByReturn :
      ∀ x → _≤_ O (inner I x (crossCorrection I x)) (afterK10 x)
    k10Bound :
      ∀ x → _≤_ O (afterK10 x) (schurMultiply M c10 (afterLowResolvent x))
    lowResolventBound :
      ∀ x → _≤_ O (afterLowResolvent x) (schurMultiply M r0 (afterK01 x))
    k01Bound :
      ∀ x → _≤_ O (afterK01 x) c01

open NSFactorizedCrossShellEvidence public

factorizedComposition :
  ∀ {v s} {ShellVector : Set v} {Scalar : Set s}
    {O : SchurOrderLaws Scalar}
    (M : SchurMultiplicativeLaws Scalar O)
    (I : NSShellSchurStructure ShellVector Scalar O) →
  NSFactorizedCrossShellEvidence M I →
  ThreeStageBound ShellVector Scalar (asMultiplicativeBoundLaws M)
factorizedComposition M I E = record
  { target = λ x → inner I x (crossCorrection I x)
  ; stage01 = afterK01 E
  ; stageR = afterLowResolvent E
  ; stage10 = afterK10 E
  ; c01 = c01 E
  ; r0 = r0 E
  ; c10 = c10 E
  ; targetToStage10 = correctionControlledByReturn E
  ; stage10Bound = k10Bound E
  ; resolventBound = lowResolventBound E
  ; stage01Bound = k01Bound E
  }

factorizedCrossBudget :
  ∀ {v s} {ShellVector : Set v} {Scalar : Set s}
    {O : SchurOrderLaws Scalar}
    {M : SchurMultiplicativeLaws Scalar O}
    {I : NSShellSchurStructure ShellVector Scalar O} →
  NSFactorizedCrossShellEvidence M I → Scalar
factorizedCrossBudget {M = M} E =
  schurMultiply M (c10 E) (schurMultiply M (r0 E) (c01 E))

factorizedEvidenceBoundsCorrection :
  ∀ {v s} {ShellVector : Set v} {Scalar : Set s}
    {O : SchurOrderLaws Scalar}
    (M : SchurMultiplicativeLaws Scalar O)
    (I : NSShellSchurStructure ShellVector Scalar O)
    (E : NSFactorizedCrossShellEvidence M I)
    (x : ShellVector) →
  _≤_ O (inner I x (crossCorrection I x)) (factorizedCrossBudget E)
factorizedEvidenceBoundsCorrection M I E =
  threeStageBoundComposes
    (asMultiplicativeBoundLaws M)
    (factorizedComposition M I E)

record NSFactorizedBudgetDischarge
    {v s : Level}
    {ShellVector : Set v}
    {Scalar : Set s}
    {O : SchurOrderLaws Scalar}
    (M : SchurMultiplicativeLaws Scalar O)
    (I : NSShellSchurStructure ShellVector Scalar O)
    (E : NSFactorizedCrossShellEvidence M I) : Set s where
  field
    structureBudgetIsFactorized : crossBudget I ≡ factorizedCrossBudget E
    factorizedBudgetBelowGap : _≤_ O (factorizedCrossBudget E) (highGap I)

open NSFactorizedBudgetDischarge public

factorizedEvidenceDischargesCrossShell :
  ∀ {v s} {ShellVector : Set v} {Scalar : Set s}
    {O : SchurOrderLaws Scalar}
    (M : SchurMultiplicativeLaws Scalar O)
    (I : NSShellSchurStructure ShellVector Scalar O)
    (E : NSFactorizedCrossShellEvidence M I) →
  NSFactorizedBudgetDischarge M I E →
  NSCrossShellCorrectionBound I
factorizedEvidenceDischargesCrossShell M I E D = record
  { correctionBound = λ x →
      subst
        (λ budget → _≤_ O (inner I x (crossCorrection I x)) budget)
        (sym (structureBudgetIsFactorized D))
        (factorizedEvidenceBoundsCorrection M I E x)
  ; budgetBelowDiagonalGap =
      subst
        (λ budget → _≤_ O budget (highGap I))
        (sym (structureBudgetIsFactorized D))
        (factorizedBudgetBelowGap D)
  }
