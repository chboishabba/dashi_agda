module DASHI.Physics.Closure.NSFactorizedSchurFrameGap where

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import DASHI.Analysis.BlockSchurCoercivity
open import DASHI.Physics.Closure.NSShellSchurInstance
open import DASHI.Physics.Closure.NSCrossShellSchurBound
open import DASHI.Physics.Closure.NSFactorizedCrossShellBound

------------------------------------------------------------------------
-- End-to-end conditional Wall-1 Schur discharge.
------------------------------------------------------------------------

record NSFactorizedSchurDischarge
    {v s : Level}
    {ShellVector : Set v}
    {Scalar : Set s}
    {O : SchurOrderLaws Scalar}
    (M : SchurMultiplicativeLaws Scalar O)
    (I : NSShellSchurStructure ShellVector Scalar O) : Set (lsuc (v ⊔ s)) where
  field
    diagonal : NSDiagonalShellGap I
    factorizedEvidence : NSFactorizedCrossShellEvidence M I
    factorizedBudget :
      NSFactorizedBudgetDischarge M I factorizedEvidence

open NSFactorizedSchurDischarge public

factorizedFrontierDischarge :
  ∀ {v s}
    {ShellVector : Set v}
    {Scalar : Set s}
    {O : SchurOrderLaws Scalar}
    (M : SchurMultiplicativeLaws Scalar O)
    (I : NSShellSchurStructure ShellVector Scalar O) →
  NSFactorizedSchurDischarge M I →
  NSSchurFrontierDischarge O I
factorizedFrontierDischarge M I D = record
  { diagonal = diagonal D
  ; crossShell =
      factorizedEvidenceDischargesCrossShell
        M I
        (factorizedEvidence D)
        (factorizedBudget D)
  }

factorizedBoundsImplyFrameGap :
  ∀ {v s}
    {ShellVector : Set v}
    {Scalar : Set s}
    (O : SchurOrderLaws Scalar)
    (M : SchurMultiplicativeLaws Scalar O)
    (I : NSShellSchurStructure ShellVector Scalar O)
    (D : NSFactorizedSchurDischarge M I)
    (x : ShellVector) →
  _≤_ O
    (_⊖_ O (highGap I) (crossBudget I))
    (inner I x (schurComplement I x))
factorizedBoundsImplyFrameGap O M I D =
  frontierDischargeImpliesFrameGap O I
    (factorizedFrontierDischarge M I D)
