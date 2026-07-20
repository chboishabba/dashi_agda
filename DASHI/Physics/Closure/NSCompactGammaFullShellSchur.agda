module DASHI.Physics.Closure.NSCompactGammaFullShellSchur where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)
open import Data.Nat using (_≤_)
open import Relation.Nullary using (¬_)

open import DASHI.Analysis.FiniteWeightedKernelSums public
import DASHI.Physics.Closure.NSPairIncidenceKernel as PairKernel

------------------------------------------------------------------------
-- Exact full-shell Fourier carrier.
--
-- `PairIncidenceData` owns the finite kernel assembled as the fold of every
-- resonant pair contribution.  This module lifts it to a shell/cutoff family,
-- makes enumeration and incidence completeness explicit, and requires local
-- Fourier majorization for every pair in the fold.
------------------------------------------------------------------------

record FullShellFourierFamily
    {p m s i : Level}
    (Pair : Set p)
    (Mode : Set m)
    (Scalar : Set s) : Set (lsuc (p ⊔ m ⊔ s ⊔ i)) where
  field
    TargetShell : Nat → Nat → Mode → Set i
    SourceNearShell : Nat → Nat → Mode → Set i

    OccursMode : List Mode → Mode → Set i
    OccursPair : List Pair → Pair → Set i
    NoModeDuplicates : List Mode → Set i
    NoPairDuplicates : List Pair → Set i

    pairDataAt :
      Nat → Nat → PairKernel.PairIncidenceData Pair Mode Mode Scalar

    targetEnumerationSound :
      ∀ K N k →
      OccursMode (PairKernel.rows (pairDataAt K N)) k →
      TargetShell K N k

    targetEnumerationComplete :
      ∀ K N k →
      TargetShell K N k →
      OccursMode (PairKernel.rows (pairDataAt K N)) k

    sourceEnumerationSound :
      ∀ K N source →
      OccursMode (PairKernel.columns (pairDataAt K N)) source →
      SourceNearShell K N source

    sourceEnumerationComplete :
      ∀ K N source →
      SourceNearShell K N source →
      OccursMode (PairKernel.columns (pairDataAt K N)) source

    targetEnumerationNoDuplicates :
      ∀ K N → NoModeDuplicates (PairKernel.rows (pairDataAt K N))

    sourceEnumerationNoDuplicates :
      ∀ K N → NoModeDuplicates (PairKernel.columns (pairDataAt K N))

    pairEnumerationNoDuplicates :
      ∀ K N → NoPairDuplicates (PairKernel.pairs (pairDataAt K N))

    Incidence : Nat → Nat → Pair → Mode → Mode → Set i

    incidenceComplete :
      ∀ K N pair →
      OccursPair (PairKernel.pairs (pairDataAt K N)) pair →
      Σ Mode (λ target →
        Σ Mode (λ source → Incidence K N pair target source))

    incidenceTargetSound :
      ∀ K N pair target source →
      Incidence K N pair target source →
      TargetShell K N target

    incidenceSourceSound :
      ∀ K N pair target source →
      Incidence K N pair target source →
      SourceNearShell K N source

    incidenceProofUnique :
      ∀ K N pair target source →
      (left right : Incidence K N pair target source) →
      left ≡ right

    localFourierResponse : Nat → Nat → Pair → Scalar
    localFourierMajorant : Nat → Nat → Pair → Scalar

    everyLocalFourierMajorization :
      ∀ K N pair →
      OccursPair (PairKernel.pairs (pairDataAt K N)) pair →
      PairKernel._≤_ (pairDataAt K N)
        (localFourierResponse K N pair)
        (localFourierMajorant K N pair)

    pairContributionIsLocalMajorant :
      ∀ K N pair target source →
      Incidence K N pair target source →
      PairKernel.pairContribution (pairDataAt K N) pair target source ≡
      localFourierMajorant K N pair

    pairContributionZeroOffIncidence :
      ∀ K N pair target source →
      ¬ Incidence K N pair target source →
      PairKernel.pairContribution (pairDataAt K N) pair target source ≡
      PairKernel.zero (pairDataAt K N)

open FullShellFourierFamily public

fullShellKernelAt :
  ∀ {p m s i}
    {Pair : Set p}
    {Mode : Set m}
    {Scalar : Set s} →
  FullShellFourierFamily {i = i} Pair Mode Scalar →
  Nat → Nat →
  FiniteWeightedKernel Mode Mode Scalar
fullShellKernelAt F K N =
  PairKernel.asFiniteWeightedKernel (pairDataAt F K N)

------------------------------------------------------------------------
-- Uniform Schur estimates for the exact pair-incidence fold.
------------------------------------------------------------------------

record FullShellUniformSchur
    {p m s i : Level}
    {Pair : Set p}
    {Mode : Set m}
    {Scalar : Set s}
    (F : FullShellFourierFamily {i = i} Pair Mode Scalar) :
    Set (lsuc (p ⊔ m ⊔ s ⊔ i)) where
  field
    rowBudget : Scalar
    columnBudget : Scalar

    certificateAt :
      (K N : Nat) →
      FiniteWeightedSchurCertificate (fullShellKernelAt F K N)

    rowConstantUniform :
      ∀ K N → rowConstant (certificateAt K N) ≡ rowBudget

    columnConstantUniform :
      ∀ K N → columnConstant (certificateAt K N) ≡ columnBudget

open FullShellUniformSchur public

fullShellRowEstimate :
  ∀ {p m s i}
    {Pair : Set p}
    {Mode : Set m}
    {Scalar : Set s}
    {F : FullShellFourierFamily {i = i} Pair Mode Scalar} →
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
  ∀ {p m s i}
    {Pair : Set p}
    {Mode : Set m}
    {Scalar : Set s}
    {F : FullShellFourierFamily {i = i} Pair Mode Scalar} →
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
-- Named combinatorial/analytic leaves used to construct the certificate.
------------------------------------------------------------------------

record FullShellCombinatorics
    {p m s i : Level}
    {Pair : Set p}
    {Mode : Set m}
    {Scalar : Set s}
    (F : FullShellFourierFamily {i = i} Pair Mode Scalar) :
    Set (lsuc (p ⊔ m ⊔ s ⊔ i)) where
  field
    shellIntersectionCount : Nat → Nat → Nat → Mode → Nat
    shellCountingBudget : Nat → Nat → Nat → Nat

    shellCountingBound :
      ∀ K j ell k →
      shellIntersectionCount K j ell k ≤ shellCountingBudget K j ell

    WeightedRadialSummability : Nat → Set i
    weightedRadialSummability :
      ∀ K → WeightedRadialSummability K

    AngularPolarizationBound : Nat → Nat → Pair → Set i
    angularPolarizationBound :
      ∀ K N pair →
      OccursPair F (PairKernel.pairs (pairDataAt F K N)) pair →
      AngularPolarizationBound K N pair

    zeroMode : Mode
    zeroModeExcluded :
      ∀ K N →
      ¬ OccursMode F (PairKernel.columns (pairDataAt F K N)) zeroMode

    CutoffExtension : Nat → Nat → Nat → Set i
    cutoffMonotone :
      ∀ K N N′ → N ≤ N′ → CutoffExtension K N N′

    CutoffUniformConstants : Set i
    cutoffUniformConstants : CutoffUniformConstants

open FullShellCombinatorics public

record FullShellSchurProgram
    {p m s i : Level}
    {Pair : Set p}
    {Mode : Set m}
    {Scalar : Set s}
    (F : FullShellFourierFamily {i = i} Pair Mode Scalar) :
    Set (lsuc (p ⊔ m ⊔ s ⊔ i)) where
  field
    combinatorics : FullShellCombinatorics F
    uniformSchur : FullShellUniformSchur F

open FullShellSchurProgram public
