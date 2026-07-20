module DASHI.Physics.Closure.NSCompactGammaFullShellSchur where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Nullary using (¬_)

open import DASHI.Analysis.FiniteWeightedKernelSums

------------------------------------------------------------------------
-- Exact full-shell Fourier carrier.
--
-- Unlike the earlier six-mode restriction, this owner makes the finite row and
-- column lists, the incidence relation, the actual local majorant, and the
-- weighted kernel entry part of one object.  Consequently the Schur sums below
-- are definitionally the sums over the declared full shell; an unrelated scalar
-- cannot be supplied as a "row bound".
------------------------------------------------------------------------

record FullShellFourierFamily
    {m s i : Level}
    (Mode : Set m)
    (Scalar : Set s) : Set (lsuc (m ⊔ s ⊔ i)) where
  field
    TargetShell : Nat → Nat → Mode → Set i
    SourceNearShell : Nat → Nat → Mode → Set i
    Resonant : Mode → Mode → Set i
    Incidence : Nat → Nat → Mode → Mode → Set i

    Occurs : List Mode → Mode → Set i
    NoDuplicates : List Mode → Set i

    targetModes : Nat → Nat → List Mode
    sourceModes : Nat → Nat → List Mode

    targetEnumerationSound :
      ∀ K N k → Occurs (targetModes K N) k → TargetShell K N k

    targetEnumerationComplete :
      ∀ K N k → TargetShell K N k → Occurs (targetModes K N) k

    sourceEnumerationSound :
      ∀ K N p → Occurs (sourceModes K N) p → SourceNearShell K N p

    sourceEnumerationComplete :
      ∀ K N p → SourceNearShell K N p → Occurs (sourceModes K N) p

    targetEnumerationNoDuplicates :
      ∀ K N → NoDuplicates (targetModes K N)

    sourceEnumerationNoDuplicates :
      ∀ K N → NoDuplicates (sourceModes K N)

    incidenceComplete :
      ∀ K N k p →
      TargetShell K N k →
      SourceNearShell K N p →
      Resonant k p →
      Incidence K N k p

    incidenceSound :
      ∀ K N k p →
      Incidence K N k p →
      TargetShell K N k

    incidenceSourceSound :
      ∀ K N k p →
      Incidence K N k p →
      SourceNearShell K N p

    incidenceResonant :
      ∀ K N k p →
      Incidence K N k p →
      Resonant k p

    incidenceProofUnique :
      ∀ K N k p →
      (left right : Incidence K N k p) →
      left ≡ right

    zero : Scalar
    add : Scalar → Scalar → Scalar
    multiply : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set s

    localFourierResponse : Nat → Nat → Mode → Mode → Scalar
    localFourierMajorant : Nat → Nat → Mode → Mode → Scalar

    everyLocalFourierMajorization :
      ∀ K N k p →
      Incidence K N k p →
      _≤_
        (localFourierResponse K N k p)
        (localFourierMajorant K N k p)

    rowWeight : Nat → Mode → Scalar
    columnWeight : Nat → Mode → Scalar

    kernelEntry : Nat → Nat → Mode → Mode → Scalar

    kernelEntryIsLocalMajorant :
      ∀ K N k p →
      Incidence K N k p →
      kernelEntry K N k p ≡ localFourierMajorant K N k p

    kernelZeroOffIncidence :
      ∀ K N k p →
      ¬ Incidence K N k p →
      kernelEntry K N k p ≡ zero

open FullShellFourierFamily public

fullShellKernelAt :
  ∀ {m s i}
    {Mode : Set m}
    {Scalar : Set s} →
  FullShellFourierFamily {i = i} Mode Scalar →
  Nat → Nat →
  FiniteWeightedKernel Mode Mode Scalar
fullShellKernelAt F K N = record
  { rows = targetModes F K N
  ; columns = sourceModes F K N
  ; zero = zero F
  ; add = add F
  ; multiply = multiply F
  ; _≤_ = _≤_ F
  ; kernel = kernelEntry F K N
  ; rowWeight = rowWeight F K
  ; colWeight = columnWeight F K
  }

------------------------------------------------------------------------
-- The row and column estimates are now certificates for the exact finite sums
-- computed by `rowWeightedSum` and `columnWeightedSum` on `fullShellKernelAt`.
------------------------------------------------------------------------

record FullShellUniformSchur
    {m s i : Level}
    {Mode : Set m}
    {Scalar : Set s}
    (F : FullShellFourierFamily {i = i} Mode Scalar) :
    Set (lsuc (m ⊔ s ⊔ i)) where
  field
    rowBudget : Scalar
    columnBudget : Scalar

    certificateAt :
      (K N : Nat) →
      FiniteWeightedSchurCertificate (fullShellKernelAt F K N)

    rowConstantUniform :
      ∀ K N →
      rowConstant (certificateAt K N) ≡ rowBudget

    columnConstantUniform :
      ∀ K N →
      columnConstant (certificateAt K N) ≡ columnBudget

open FullShellUniformSchur public

fullShellRowEstimate :
  ∀ {m s i}
    {Mode : Set m}
    {Scalar : Set s}
    {F : FullShellFourierFamily {i = i} Mode Scalar} →
  (S : FullShellUniformSchur F) →
  (K N : Nat) →
  (target : Mode) →
  _≤_ (fullShellKernelAt F K N)
    (rowWeightedSum (fullShellKernelAt F K N) target)
    (multiply (fullShellKernelAt F K N)
      (rowConstant (certificateAt S K N))
      (rowWeight (fullShellKernelAt F K N) target))
fullShellRowEstimate S K N = rowBound (certificateAt S K N)

fullShellColumnEstimate :
  ∀ {m s i}
    {Mode : Set m}
    {Scalar : Set s}
    {F : FullShellFourierFamily {i = i} Mode Scalar} →
  (S : FullShellUniformSchur F) →
  (K N : Nat) →
  (source : Mode) →
  _≤_ (fullShellKernelAt F K N)
    (columnWeightedSum (fullShellKernelAt F K N) source)
    (multiply (fullShellKernelAt F K N)
      (columnConstant (certificateAt S K N))
      (colWeight (fullShellKernelAt F K N) source))
fullShellColumnEstimate S K N = columnBound (certificateAt S K N)

------------------------------------------------------------------------
-- Named combinatorial/analytic leaves needed to construct the uniform
-- certificate for the integer Fourier shell.  These are intentionally separate
-- from the certificate itself so that enumeration, counting, radial summation,
-- angular control, zero-mode exclusion, and cutoff stability cannot be hidden in
-- one opaque premise.
------------------------------------------------------------------------

record FullShellCombinatorics
    {m s i : Level}
    {Mode : Set m}
    {Scalar : Set s}
    (F : FullShellFourierFamily {i = i} Mode Scalar) :
    Set (lsuc (m ⊔ s ⊔ i)) where
  field
    shellIntersectionCount : Nat → Nat → Nat → Mode → Nat
    shellCountingBudget : Nat → Nat → Nat → Nat

    ShellCountingBound : Nat → Nat → Nat → Mode → Set i
    shellCountingBound :
      ∀ K j ell k → ShellCountingBound K j ell k

    WeightedRadialSummability : Nat → Set i
    weightedRadialSummability :
      ∀ K → WeightedRadialSummability K

    AngularPolarizationBound : Nat → Nat → Mode → Mode → Set i
    angularPolarizationBound :
      ∀ K N k p →
      Incidence F K N k p →
      AngularPolarizationBound K N k p

    ZeroModeExcluded : Nat → Nat → Set i
    zeroModeExcluded :
      ∀ K N → ZeroModeExcluded K N

    CutoffMonotone : Nat → Nat → Nat → Set i
    cutoffMonotone :
      ∀ K N N′ → CutoffMonotone K N N′

    CutoffUniformConstants : Set i
    cutoffUniformConstants : CutoffUniformConstants

open FullShellCombinatorics public

record FullShellSchurProgram
    {m s i : Level}
    {Mode : Set m}
    {Scalar : Set s}
    (F : FullShellFourierFamily {i = i} Mode Scalar) :
    Set (lsuc (m ⊔ s ⊔ i)) where
  field
    combinatorics : FullShellCombinatorics F
    uniformSchur : FullShellUniformSchur F

open FullShellSchurProgram public
