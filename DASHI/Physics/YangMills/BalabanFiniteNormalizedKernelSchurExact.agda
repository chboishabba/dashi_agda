module DASHI.Physics.YangMills.BalabanFiniteNormalizedKernelSchurExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Issai Schur, classical matrix norm test (1911). No DOI applies to the
-- original result.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- A dense entrywise Schur count throws away the normalization built into a
-- block average and therefore scales spuriously with the number of fine sites.
-- The literal CMP109 equation-(0.12) average instead contains the normalized
-- finite sum
--
--       A = w sum_s K_s,       w |S| = 1.
--
-- This module proves the scale-safe finite theorem needed by the source-exact
-- route.  If every local kernel K_s has absolute row mass <= R and absolute
-- column mass <= C, then the normalized average has the *same* masses:
--
--       rowMass(A)    <= R,
--       columnMass(A) <= C,
--
-- and hence, by the repository's square-root-free Schur theorem,
--
--       ||A v||_2^2 <= R C ||v||_2^2.
--
-- The proof is literal finite analysis: absolute-value triangle inequality,
-- nonnegative scaling, Fubini, and the identity w |S| = 1.  There is no
-- asymptotic argument and no dimension-dependent hidden constant.  This is the
-- correct way to exploit the 1/28561 weight of the minimal L=13 CMP109 block.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur

RectMatrix : Set → Set → Set
RectMatrix Row Column = Row → Column → ℚ

KernelFamily : Set → Set → Set → Set
KernelFamily Sample Row Column = Sample → RectMatrix Row Column

normalizedKernel :
  ∀ {Sample Row Column : Set} →
  ℚ → List Sample → KernelFamily Sample Row Column → RectMatrix Row Column
normalizedKernel weight samples kernels row column =
  weight * Sums.sumRational samples (λ sample → kernels sample row column)

------------------------------------------------------------------------
-- Scalar normalized-average lemma.
------------------------------------------------------------------------

normalizedFiniteAverageBelowUniformBound :
  ∀ {Sample : Set}
    weight (samples : List Sample) (term : Sample → ℚ) bound →
  0ℚ ≤ weight →
  weight * Sums.natAsRational (length samples) ≡ 1ℚ →
  (∀ sample → term sample ≤ bound) →
  weight * Sums.sumRational samples term ≤ bound
normalizedFiniteAverageBelowUniformBound
    weight samples term bound weightNonnegative normalization pointwise =
  let
    summed :
      Sums.sumRational samples term
      ≤ Sums.sumRational samples (λ _ → bound)
    summed = Schur.sumPointwiseBelow samples term (λ _ → bound) pointwise

    constantExact :
      Sums.sumRational samples (λ _ → bound)
      ≡ Sums.natAsRational (length samples) * bound
    constantExact = Fibre.sumRationalConstant samples bound

    scaled :
      weight * Sums.sumRational samples term
      ≤ weight * Sums.sumRational samples (λ _ → bound)
    scaled = Norm.scaleNonnegative weight weightNonnegative summed

    scaledConstant :
      weight * Sums.sumRational samples (λ _ → bound)
      ≡ weight * (Sums.natAsRational (length samples) * bound)
    scaledConstant = cong (weight *_) constantExact

    normalizationExact :
      weight * (Sums.natAsRational (length samples) * bound)
      ≡ bound
    normalizationExact =
      trans
        (sym
          (ℚP.*-assoc
            weight (Sums.natAsRational (length samples)) bound))
        (trans
          (cong (_* bound) normalization)
          (ℚP.*-identityˡ bound))
  in
  subst
    (λ upper → weight * Sums.sumRational samples term ≤ upper)
    (trans scaledConstant normalizationExact)
    scaled

------------------------------------------------------------------------
-- Entrywise triangle inequality for the normalized kernel.
------------------------------------------------------------------------

normalizedKernelEntryAbsoluteUpper :
  ∀ {Sample Row Column : Set}
    weight (samples : List Sample)
    (kernels : KernelFamily Sample Row Column) row column →
  0ℚ ≤ weight →
  ∣ normalizedKernel weight samples kernels row column ∣
  ≤ weight * Sums.sumRational samples
      (λ sample → ∣ kernels sample row column ∣)
normalizedKernelEntryAbsoluteUpper
    weight samples kernels row column weightNonnegative =
  let
    selectedSum =
      Sums.sumRational samples (λ sample → kernels sample row column)

    absoluteProduct :
      ∣ weight * selectedSum ∣ ≡ ∣ weight ∣ * ∣ selectedSum ∣
    absoluteProduct = ℚP.∣p*q∣≡∣p∣*∣q∣ weight selectedSum

    weightAbsolute : ∣ weight ∣ ≡ weight
    weightAbsolute = ℚP.0≤p⇒∣p∣≡p weightNonnegative

    absoluteRewrite :
      ∣ normalizedKernel weight samples kernels row column ∣
      ≡ weight * ∣ selectedSum ∣
    absoluteRewrite =
      trans absoluteProduct
        (cong (_* ∣ selectedSum ∣) weightAbsolute)

    triangle :
      ∣ selectedSum ∣
      ≤ Sums.sumRational samples
          (λ sample → ∣ kernels sample row column ∣)
    triangle = Schur.sumAbsoluteTriangle samples
      (λ sample → kernels sample row column)

    scaled = Norm.scaleNonnegative weight weightNonnegative triangle
  in
  subst
    (λ lower →
      lower
      ≤ weight * Sums.sumRational samples
          (λ sample → ∣ kernels sample row column ∣))
    (sym absoluteRewrite)
    scaled

------------------------------------------------------------------------
-- Fubini preserves local row/column mass bounds under normalized averaging.
------------------------------------------------------------------------

normalizedKernelRowMassFubiniUpper :
  ∀ {Sample Row Column : Set}
    weight (samples : List Sample)
    (rows : List Row) (columns : List Column)
    (kernels : KernelFamily Sample Row Column) row →
  0ℚ ≤ weight →
  RectSchur.rectAbsoluteRowMass columns
      (normalizedKernel weight samples kernels) row
  ≤ weight * Sums.sumRational samples
      (λ sample → RectSchur.rectAbsoluteRowMass columns (kernels sample) row)
normalizedKernelRowMassFubiniUpper
    weight samples rows columns kernels row weightNonnegative =
  let
    first = Schur.sumPointwiseBelow columns
      (λ column →
        ∣ normalizedKernel weight samples kernels row column ∣)
      (λ column →
        weight * Sums.sumRational samples
          (λ sample → ∣ kernels sample row column ∣))
      (λ column →
        normalizedKernelEntryAbsoluteUpper
          weight samples kernels row column weightNonnegative)

    scaleExact :
      Sums.sumRational columns
        (λ column →
          weight * Sums.sumRational samples
            (λ sample → ∣ kernels sample row column ∣))
      ≡ weight * Sums.sumRational columns
          (λ column →
            Sums.sumRational samples
              (λ sample → ∣ kernels sample row column ∣))
    scaleExact = Sums.sumRationalScale weight columns
      (λ column →
        Sums.sumRational samples
          (λ sample → ∣ kernels sample row column ∣))

    swapExact :
      Sums.sumRational columns
        (λ column →
          Sums.sumRational samples
            (λ sample → ∣ kernels sample row column ∣))
      ≡ Sums.sumRational samples
          (λ sample →
            Sums.sumRational columns
              (λ column → ∣ kernels sample row column ∣))
    swapExact = Fubini.sumSwap columns samples
      (λ column sample → ∣ kernels sample row column ∣)

    targetExact :
      Sums.sumRational columns
        (λ column →
          weight * Sums.sumRational samples
            (λ sample → ∣ kernels sample row column ∣))
      ≡ weight * Sums.sumRational samples
          (λ sample → RectSchur.rectAbsoluteRowMass columns
            (kernels sample) row)
    targetExact = trans scaleExact (cong (weight *_) swapExact)
  in
  subst
    (λ upper →
      RectSchur.rectAbsoluteRowMass columns
        (normalizedKernel weight samples kernels) row ≤ upper)
    targetExact first

normalizedKernelColumnMassFubiniUpper :
  ∀ {Sample Row Column : Set}
    weight (samples : List Sample)
    (rows : List Row) (columns : List Column)
    (kernels : KernelFamily Sample Row Column) column →
  0ℚ ≤ weight →
  RectSchur.rectAbsoluteColumnMass rows
      (normalizedKernel weight samples kernels) column
  ≤ weight * Sums.sumRational samples
      (λ sample → RectSchur.rectAbsoluteColumnMass rows (kernels sample) column)
normalizedKernelColumnMassFubiniUpper
    weight samples rows columns kernels column weightNonnegative =
  let
    first = Schur.sumPointwiseBelow rows
      (λ row →
        ∣ normalizedKernel weight samples kernels row column ∣)
      (λ row →
        weight * Sums.sumRational samples
          (λ sample → ∣ kernels sample row column ∣))
      (λ row →
        normalizedKernelEntryAbsoluteUpper
          weight samples kernels row column weightNonnegative)

    scaleExact :
      Sums.sumRational rows
        (λ row →
          weight * Sums.sumRational samples
            (λ sample → ∣ kernels sample row column ∣))
      ≡ weight * Sums.sumRational rows
          (λ row →
            Sums.sumRational samples
              (λ sample → ∣ kernels sample row column ∣))
    scaleExact = Sums.sumRationalScale weight rows
      (λ row →
        Sums.sumRational samples
          (λ sample → ∣ kernels sample row column ∣))

    swapExact :
      Sums.sumRational rows
        (λ row →
          Sums.sumRational samples
            (λ sample → ∣ kernels sample row column ∣))
      ≡ Sums.sumRational samples
          (λ sample →
            Sums.sumRational rows
              (λ row → ∣ kernels sample row column ∣))
    swapExact = Fubini.sumSwap rows samples
      (λ row sample → ∣ kernels sample row column ∣)

    targetExact :
      Sums.sumRational rows
        (λ row →
          weight * Sums.sumRational samples
            (λ sample → ∣ kernels sample row column ∣))
      ≡ weight * Sums.sumRational samples
          (λ sample → RectSchur.rectAbsoluteColumnMass rows
            (kernels sample) column)
    targetExact = trans scaleExact (cong (weight *_) swapExact)
  in
  subst
    (λ upper →
      RectSchur.rectAbsoluteColumnMass rows
        (normalizedKernel weight samples kernels) column ≤ upper)
    targetExact first

normalizedKernelRowMassBound :
  ∀ {Sample Row Column : Set}
    weight (samples : List Sample)
    (rows : List Row) (columns : List Column)
    (kernels : KernelFamily Sample Row Column)
    rowBound row →
  0ℚ ≤ weight →
  weight * Sums.natAsRational (length samples) ≡ 1ℚ →
  (∀ sample → RectSchur.rectAbsoluteRowMass columns (kernels sample) row ≤ rowBound) →
  RectSchur.rectAbsoluteRowMass columns
      (normalizedKernel weight samples kernels) row
  ≤ rowBound
normalizedKernelRowMassBound
    weight samples rows columns kernels rowBound row
    weightNonnegative normalization localBound =
  ℚP.≤-trans
    (normalizedKernelRowMassFubiniUpper
      weight samples rows columns kernels row weightNonnegative)
    (normalizedFiniteAverageBelowUniformBound
      weight samples
      (λ sample → RectSchur.rectAbsoluteRowMass columns (kernels sample) row)
      rowBound weightNonnegative normalization localBound)

normalizedKernelColumnMassBound :
  ∀ {Sample Row Column : Set}
    weight (samples : List Sample)
    (rows : List Row) (columns : List Column)
    (kernels : KernelFamily Sample Row Column)
    columnBound column →
  0ℚ ≤ weight →
  weight * Sums.natAsRational (length samples) ≡ 1ℚ →
  (∀ sample → RectSchur.rectAbsoluteColumnMass rows (kernels sample) column ≤ columnBound) →
  RectSchur.rectAbsoluteColumnMass rows
      (normalizedKernel weight samples kernels) column
  ≤ columnBound
normalizedKernelColumnMassBound
    weight samples rows columns kernels columnBound column
    weightNonnegative normalization localBound =
  ℚP.≤-trans
    (normalizedKernelColumnMassFubiniUpper
      weight samples rows columns kernels column weightNonnegative)
    (normalizedFiniteAverageBelowUniformBound
      weight samples
      (λ sample → RectSchur.rectAbsoluteColumnMass rows (kernels sample) column)
      columnBound weightNonnegative normalization localBound)

------------------------------------------------------------------------
-- Scale-safe square-root-free Schur theorem.
------------------------------------------------------------------------

normalizedKernelSchurSquared :
  ∀ {Sample Row Column : Set}
    weight (samples : List Sample)
    (rows : List Row) (columns : List Column)
    (kernels : KernelFamily Sample Row Column)
    vector rowBound columnBound →
  0ℚ ≤ weight →
  weight * Sums.natAsRational (length samples) ≡ 1ℚ →
  0ℚ ≤ rowBound → 0ℚ ≤ columnBound →
  (∀ sample row →
    RectSchur.rectAbsoluteRowMass columns (kernels sample) row ≤ rowBound) →
  (∀ sample column →
    RectSchur.rectAbsoluteColumnMass rows (kernels sample) column ≤ columnBound) →
  RectSchur.rectVectorNormSq rows
    (RectSchur.rectApply columns
      (normalizedKernel weight samples kernels) vector)
  ≤ rowBound * columnBound * RectSchur.rectVectorNormSq columns vector
normalizedKernelSchurSquared
    weight samples rows columns kernels vector rowBound columnBound
    weightNonnegative normalization rowNonnegative columnNonnegative
    localRows localColumns =
  RectSchur.finiteRectangularSchurSquared
    rows columns (normalizedKernel weight samples kernels) vector
    rowBound columnBound rowNonnegative columnNonnegative
    (λ row → normalizedKernelRowMassBound
      weight samples rows columns kernels rowBound row
      weightNonnegative normalization (λ sample → localRows sample row))
    (λ column → normalizedKernelColumnMassBound
      weight samples rows columns kernels columnBound column
      weightNonnegative normalization (λ sample → localColumns sample column))

finiteNormalizedKernelEntryTriangleLevel : ProofLevel
finiteNormalizedKernelEntryTriangleLevel = machineChecked

finiteNormalizedKernelMassPreservationLevel : ProofLevel
finiteNormalizedKernelMassPreservationLevel = machineChecked

finiteNormalizedKernelSchurSquaredLevel : ProofLevel
finiteNormalizedKernelSchurSquaredLevel = machineChecked
