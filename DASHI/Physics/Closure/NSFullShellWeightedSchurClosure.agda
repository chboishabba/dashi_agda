module DASHI.Physics.Closure.NSFullShellWeightedSchurClosure where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSCompactGammaFullShellSchur as FullShell
import DASHI.Physics.Closure.NSCutoffUniformIntegerShellSchur as Cutoff

------------------------------------------------------------------------
-- Final synthesis gate for the full-shell weighted Schur lane.
--
-- The repository already owns:
--   * exact pair-incidence folds and shell/cutoff enumerations;
--   * local Fourier majorization and no-duplication obligations;
--   * SC1--SC9 integer-shell, zero-mode, cutoff and Schur obligations;
--   * the squared Schur action theorem.
--
-- This record prevents those components from being supplied independently.
-- Promotion requires one shared FullShellFourierFamily together with coherent
-- row/column constants for the finite-fold and cutoff-uniform views.
------------------------------------------------------------------------

record FullShellWeightedSchurClosure
    {p m s i v : Level}
    (Pair : Set p)
    (Mode : Set m)
    (Scalar : Set s)
    (Vector : Set v)
    (F : FullShell.FullShellFourierFamily {i = i} Pair Mode Scalar) :
    Set (lsuc (p ⊔ m ⊔ s ⊔ i ⊔ v)) where
  field
    finiteFoldProgram : FullShell.FullShellSchurProgram F
    cutoffUniformProgram :
      Cutoff.CutoffUniformIntegerShellSchurProgram
        Pair Mode Scalar Vector F

    rowBudgetCoherent :
      FullShell.rowBudget
        (FullShell.uniformSchur finiteFoldProgram)
      ≡
      Cutoff.rowBudget
        (Cutoff.cutoffUniformKernel cutoffUniformProgram)

    columnBudgetCoherent :
      FullShell.columnBudget
        (FullShell.uniformSchur finiteFoldProgram)
      ≡
      Cutoff.columnBudget
        (Cutoff.cutoffUniformKernel cutoffUniformProgram)

open FullShellWeightedSchurClosure public

closureRowEstimate :
  ∀ {p m s i v}
    {Pair : Set p}
    {Mode : Set m}
    {Scalar : Set s}
    {Vector : Set v}
    {F : FullShell.FullShellFourierFamily {i = i} Pair Mode Scalar} →
  (C : FullShellWeightedSchurClosure Pair Mode Scalar Vector F) →
  ∀ K N target →
  FullShell._≤_ (FullShell.fullShellKernelAt F K N)
    (FullShell.rowWeightedSum (FullShell.fullShellKernelAt F K N) target)
    (FullShell.multiply (FullShell.fullShellKernelAt F K N)
      (Cutoff.rowBudget (Cutoff.cutoffUniformKernel (cutoffUniformProgram C)))
      (FullShell.rowWeight (FullShell.fullShellKernelAt F K N) target))
closureRowEstimate C =
  Cutoff.rowEstimate (Cutoff.cutoffUniformKernel (cutoffUniformProgram C))

closureColumnEstimate :
  ∀ {p m s i v}
    {Pair : Set p}
    {Mode : Set m}
    {Scalar : Set s}
    {Vector : Set v}
    {F : FullShell.FullShellFourierFamily {i = i} Pair Mode Scalar} →
  (C : FullShellWeightedSchurClosure Pair Mode Scalar Vector F) →
  ∀ K N source →
  FullShell._≤_ (FullShell.fullShellKernelAt F K N)
    (FullShell.columnWeightedSum (FullShell.fullShellKernelAt F K N) source)
    (FullShell.multiply (FullShell.fullShellKernelAt F K N)
      (Cutoff.columnBudget (Cutoff.cutoffUniformKernel (cutoffUniformProgram C)))
      (FullShell.colWeight (FullShell.fullShellKernelAt F K N) source))
closureColumnEstimate C =
  Cutoff.columnEstimate (Cutoff.cutoffUniformKernel (cutoffUniformProgram C))

closureSquaredSchur :
  ∀ {p m s i v}
    {Pair : Set p}
    {Mode : Set m}
    {Scalar : Set s}
    {Vector : Set v}
    {F : FullShell.FullShellFourierFamily {i = i} Pair Mode Scalar} →
  (C : FullShellWeightedSchurClosure Pair Mode Scalar Vector F) →
  ∀ K N f →
  Cutoff._≤²_ (Cutoff.squaredAction (cutoffUniformProgram C))
    (Cutoff.normSquared
      (Cutoff.squaredAction (cutoffUniformProgram C)) K N
      (Cutoff.applyKernel
        (Cutoff.squaredAction (cutoffUniformProgram C)) K N f))
    (Cutoff.multiplyScalar
      (Cutoff.squaredAction (cutoffUniformProgram C))
      (Cutoff.multiplyScalar
        (Cutoff.squaredAction (cutoffUniformProgram C))
        (Cutoff.rowBudget
          (Cutoff.cutoffUniformKernel (cutoffUniformProgram C)))
        (Cutoff.columnBudget
          (Cutoff.cutoffUniformKernel (cutoffUniformProgram C))))
      (Cutoff.normSquared
        (Cutoff.squaredAction (cutoffUniformProgram C)) K N f))
closureSquaredSchur C =
  Cutoff.uniformFullShellSchurSquared
    (Cutoff.cutoffUniformKernel (cutoffUniformProgram C))
    (Cutoff.squaredAction (cutoffUniformProgram C))
