module DASHI.Physics.Closure.NSCrossShellSchurBound where

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import DASHI.Analysis.BlockSchurCoercivity
open import DASHI.Physics.Closure.NSShellSchurInstance

------------------------------------------------------------------------
-- Exact frontier split.
--
-- Diagonal shell control and the non-adversarial cross-shell estimate are
-- independent inputs.  The generic Schur theorem shows that no additional
-- block-algebra lemma is needed after these are joined.
------------------------------------------------------------------------

record NSDiagonalShellGap
    {v s : Level}
    {ShellVector : Set v}
    {Scalar : Set s}
    {O : SchurOrderLaws Scalar}
    (I : NSShellSchurInputs ShellVector Scalar O) : Set (v ⊔ s) where
  field
    diagonalGap :
      ∀ x → _≤_ O (highGap I) (inner I x (highBlock I x))

open NSDiagonalShellGap public

record NSCrossShellCorrectionBound
    {v s : Level}
    {ShellVector : Set v}
    {Scalar : Set s}
    {O : SchurOrderLaws Scalar}
    (I : NSShellSchurInputs ShellVector Scalar O) : Set (v ⊔ s) where
  field
    correctionBound :
      ∀ x →
      _≤_ O
        (inner I x (crossCorrection I x))
        (crossBudget I)

    budgetBelowDiagonalGap :
      _≤_ O (crossBudget I) (highGap I)

open NSCrossShellCorrectionBound public

record NSSchurFrontierDischarge
    {v s : Level}
    {ShellVector : Set v}
    {Scalar : Set s}
    (O : SchurOrderLaws Scalar)
    (I : NSShellSchurInputs ShellVector Scalar O) : Set (lsuc (v ⊔ s)) where
  field
    diagonal : NSDiagonalShellGap I
    crossShell : NSCrossShellCorrectionBound I

open NSSchurFrontierDischarge public

frontierDischargeImpliesFrameGap :
  ∀ {v s}
    {ShellVector : Set v}
    {Scalar : Set s}
    (O : SchurOrderLaws Scalar)
    (I : NSShellSchurInputs ShellVector Scalar O)
    (F : NSSchurFrontierDischarge O I)
    (x : ShellVector) →
  _≤_ O
    (_⊖_ O (highGap I) (crossBudget I))
    (inner I x (schurComplement I x))
frontierDischargeImpliesFrameGap O I F x =
  subtractLowerBound O
    (diagonalGap (diagonal F) x)
    (correctionBound (crossShell F) x)
    (budgetBelowDiagonalGap (crossShell F))
  where
  -- The target is definitionally the Schur quadratic form after rewriting by
  -- the identity already carried by NSShellSchurInputs.
  -- Reuse the canonical theorem to perform that rewrite.
  canonical :
    _≤_ O
      (_⊖_ O (highGap I) (crossBudget I))
      (inner I x (schurComplement I x))
  canonical = nsShellSchurCoercive O I x
