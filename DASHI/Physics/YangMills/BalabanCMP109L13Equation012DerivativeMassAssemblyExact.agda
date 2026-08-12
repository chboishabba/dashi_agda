module DASHI.Physics.YangMills.BalabanCMP109L13Equation012DerivativeMassAssemblyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
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
-- Join the two finite analyses introduced for the source-faithful L=13 route.
-- For every x in the literal equation-(0.12) block, the derivative difference
-- is split into outer/logarithm/transport/path matrices.  A proof of the four
-- allocated local mass bounds constructs the actual local kernel and proves
-- its row/column masses <= 1/4096.  The normalized 1/28561 block average then
-- gives the global squared operator estimate
--
--   ||Delta DQ h||^2 <= 1/16777216 ||h||^2
--                       < 3711/262144 ||h||^2.
--
-- This removes the old full-dense 342732-coordinate accumulation entirely.
-- The sole non-algebraic seam left by this theorem is identification of these
-- four local matrices with the Frechet derivative of the literal printed
-- equation-(0.12) map at the same background and discharge of their stage
-- bounds from the principal-log/transport calculus.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
import Data.List.Base as List
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _≤_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre
import DASHI.Physics.YangMills.BalabanFiniteNormalizedKernelSchurExact as Normalized
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanCMP109L13NormalizedDerivativeSchurBudgetExact as L13
import DASHI.Physics.YangMills.BalabanCMP109L13LocalFourStageMassExact as Local
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal
import DASHI.Physics.YangMills.BalabanSelectedGaugeDerivativeTwoBackgroundVariationExact as GaugeVariation

record Equation012FourStageKernelFamily
    (Sample Row Column : Set)
    (samples : List Sample)
    (rows : List Row)
    (columns : List Column) : Set₁ where
  field
    outer logarithm transport path :
      Sample → Local.Matrix Row Column

    localBudget : ∀ sample →
      Local.LocalFourStageMassBudget
        rows columns
        (outer sample) (logarithm sample)
        (transport sample) (path sample)

open Equation012FourStageKernelFamily public

localDerivativeDifferenceKernel :
  ∀ {Sample Row Column samples rows columns} →
  Equation012FourStageKernelFamily Sample Row Column samples rows columns →
  Normalized.KernelFamily Sample Row Column
localDerivativeDifferenceKernel family sample =
  Local.fourStageMatrix
    (outer family sample)
    (logarithm family sample)
    (transport family sample)
    (path family sample)

localDerivativeDifferenceRowMass :
  ∀ {Sample Row Column samples rows columns}
    (family : Equation012FourStageKernelFamily
      Sample Row Column samples rows columns)
    sample row →
  RectSchur.rectAbsoluteRowMass columns
    (localDerivativeDifferenceKernel family sample) row
  ≤ L13.localTwoBackgroundMass
localDerivativeDifferenceRowMass family sample =
  Local.localFourStageRowMass (localBudget family sample)

localDerivativeDifferenceColumnMass :
  ∀ {Sample Row Column samples rows columns}
    (family : Equation012FourStageKernelFamily
      Sample Row Column samples rows columns)
    sample column →
  RectSchur.rectAbsoluteColumnMass rows
    (localDerivativeDifferenceKernel family sample) column
  ≤ L13.localTwoBackgroundMass
localDerivativeDifferenceColumnMass family sample =
  Local.localFourStageColumnMass (localBudget family sample)

selectedCMP109Equation012L13DerivativeSchurMassBudget :
  ∀ {Sample Row Column : Set}
    (samples : List Sample)
    (rows : List Row) (columns : List Column)
    (family : Equation012FourStageKernelFamily
      Sample Row Column samples rows columns)
    vector →
  Minimal.siteWeightℚ * Fibre.natAsRational (List.length samples) ≡ 1ℚ →
  RectSchur.rectVectorNormSq rows
    (RectSchur.rectApply columns
      (Normalized.normalizedKernel Minimal.siteWeightℚ samples
        (localDerivativeDifferenceKernel family))
      vector)
  ≤ L13.l13NormalizedSchurCoefficient
      * RectSchur.rectVectorNormSq columns vector
selectedCMP109Equation012L13DerivativeSchurMassBudget
    samples rows columns family vector normalization =
  L13.selectedCMP109L13DerivativeSchurMassBudget
    samples rows columns
    (localDerivativeDifferenceKernel family)
    vector normalization
    (localDerivativeDifferenceRowMass family)
    (localDerivativeDifferenceColumnMass family)

selectedCMP109Equation012L13DerivativeVariationFitsIFTBudget :
  ∀ {Sample Row Column : Set}
    (samples : List Sample)
    (rows : List Row) (columns : List Column)
    (family : Equation012FourStageKernelFamily
      Sample Row Column samples rows columns)
    vector →
  Minimal.siteWeightℚ * Fibre.natAsRational (List.length samples) ≡ 1ℚ →
  RectSchur.rectVectorNormSq rows
    (RectSchur.rectApply columns
      (Normalized.normalizedKernel Minimal.siteWeightℚ samples
        (localDerivativeDifferenceKernel family))
      vector)
  ≤ GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
      * RectSchur.rectVectorNormSq columns vector
selectedCMP109Equation012L13DerivativeVariationFitsIFTBudget
    samples rows columns family vector normalization =
  L13.selectedCMP109L13DerivativeFitsRemainingIFTBudget
    samples rows columns
    (localDerivativeDifferenceKernel family)
    vector normalization
    (localDerivativeDifferenceRowMass family)
    (localDerivativeDifferenceColumnMass family)

cmp109L13Equation012FourStageMassAssemblyLevel : ProofLevel
cmp109L13Equation012FourStageMassAssemblyLevel = machineChecked

cmp109L13Equation012DerivativeSchurBudgetLevel : ProofLevel
cmp109L13Equation012DerivativeSchurBudgetLevel = machineChecked

-- This deliberately names the exact same-object seam instead of hiding it in
-- an operator primitive: prove that the matrix assembled above is DQ_U-DQ_A
-- for `Printed.printedEquation012Map` at the literal L=13 physical instance.
selectedCMP109Equation012DerivativeEntrySameObjectL13Level : ProofLevel
selectedCMP109Equation012DerivativeEntrySameObjectL13Level = conditional
