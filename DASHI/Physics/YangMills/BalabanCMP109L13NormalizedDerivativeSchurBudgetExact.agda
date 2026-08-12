module DASHI.Physics.YangMills.BalabanCMP109L13NormalizedDerivativeSchurBudgetExact where

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
-- Issai Schur, classical matrix norm test (1911).
-- Roger A. Horn and Charles R. Johnson, "Matrix Analysis", 2nd ed., 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Replace the invalid dense 342732-column accumulation at source scale L=13
-- by the normalized finite-kernel estimate that equation (0.12) actually asks
-- for.  The block derivative is represented as
--
--       Delta M = (1 / 13^4) sum_{x in B} Delta K_x.
--
-- If every local two-background kernel has absolute row and column mass at
-- most 1/4096, the normalized average inherits exactly the same masses.  Schur
-- therefore gives
--
--       ||Delta M h||^2 <= (1/4096)^2 ||h||^2
--                          = 1/16777216 ||h||^2
--                          < 3711/262144 ||h||^2.
--
-- The theorem is independent of the number of state coordinates.  The only
-- cardinality used is the literal equation-(0.12) normalization
-- (1/28561)*|B|=1.  This is the source-faithful replacement for the obsolete
-- per-entry 1/65536 blanket route.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
import Data.List.Base as List
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteNormalizedKernelSchurExact as Normalized
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanSelectedGaugeDerivativeTwoBackgroundVariationExact as GaugeVariation
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal

localTwoBackgroundMass : ℚ
localTwoBackgroundMass = + 1 / 4096

l13NormalizedSchurCoefficient : ℚ
l13NormalizedSchurCoefficient = + 1 / 16777216

l13NormalizedBudgetSlack : ℚ
l13NormalizedBudgetSlack = + 237503 / 16777216

localMassNonnegative : 0ℚ ≤ localTwoBackgroundMass
localMassNonnegative = toWitness {a? = 0ℚ ≤? localTwoBackgroundMass} _

minimalSiteWeightNonnegative : 0ℚ ≤ Minimal.siteWeightℚ
minimalSiteWeightNonnegative =
  toWitness {a? = 0ℚ ≤? Minimal.siteWeightℚ} _

l13NormalizedSchurCoefficientExact :
  localTwoBackgroundMass * localTwoBackgroundMass
  ≡ l13NormalizedSchurCoefficient
l13NormalizedSchurCoefficientExact = ℚRing.solve []

l13NormalizedCoefficientPlusSlackExact :
  l13NormalizedSchurCoefficient + l13NormalizedBudgetSlack
  ≡ GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
l13NormalizedCoefficientPlusSlackExact = ℚRing.solve []

l13NormalizedBudgetSlackNonnegative : 0ℚ ≤ l13NormalizedBudgetSlack
l13NormalizedBudgetSlackNonnegative =
  toWitness {a? = 0ℚ ≤? l13NormalizedBudgetSlack} _

l13NormalizedSchurFitsIFTBudget :
  l13NormalizedSchurCoefficient
  ≤ GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
l13NormalizedSchurFitsIFTBudget =
  subst
    (λ upper → l13NormalizedSchurCoefficient ≤ upper)
    l13NormalizedCoefficientPlusSlackExact
    (subst
      (λ lower → lower
        ≤ l13NormalizedSchurCoefficient + l13NormalizedBudgetSlack)
      (sym (ℚP.+-identityʳ l13NormalizedSchurCoefficient))
      (ℚP.+-mono-≤ ℚP.≤-refl l13NormalizedBudgetSlackNonnegative))

------------------------------------------------------------------------
-- Source-specific normalized Schur theorem.
--
-- `samples` is the literal L=13 block-site list.  `normalization` is discharged
-- by the equation-(0.12) instance from block cardinality 28561 together with
-- `Minimal.minimalSiteWeightIsReciprocal`; it is kept named here so this
-- reusable theorem does not normalize a 28561-step Nat cast by reduction.
------------------------------------------------------------------------

selectedCMP109L13DerivativeSchurMassBudget :
  ∀ {Sample Row Column : Set}
    (samples : List Sample)
    (rows : List Row) (columns : List Column)
    (localDifferenceKernel :
      Normalized.KernelFamily Sample Row Column)
    vector →
  Minimal.siteWeightℚ * Fibre.natAsRational (List.length samples) ≡ 1ℚ →
  (∀ sample row →
    RectSchur.rectAbsoluteRowMass columns
      (localDifferenceKernel sample) row
    ≤ localTwoBackgroundMass) →
  (∀ sample column →
    RectSchur.rectAbsoluteColumnMass rows
      (localDifferenceKernel sample) column
    ≤ localTwoBackgroundMass) →
  RectSchur.rectVectorNormSq rows
    (RectSchur.rectApply columns
      (Normalized.normalizedKernel
        Minimal.siteWeightℚ samples localDifferenceKernel)
      vector)
  ≤ l13NormalizedSchurCoefficient
      * RectSchur.rectVectorNormSq columns vector
selectedCMP109L13DerivativeSchurMassBudget
    samples rows columns localDifferenceKernel vector
    normalization localRows localColumns =
  subst
    (λ coefficient →
      RectSchur.rectVectorNormSq rows
        (RectSchur.rectApply columns
          (Normalized.normalizedKernel
            Minimal.siteWeightℚ samples localDifferenceKernel)
          vector)
      ≤ coefficient * RectSchur.rectVectorNormSq columns vector)
    l13NormalizedSchurCoefficientExact
    (Normalized.normalizedKernelSchurSquared
      Minimal.siteWeightℚ samples rows columns localDifferenceKernel vector
      localTwoBackgroundMass localTwoBackgroundMass
      minimalSiteWeightNonnegative
      normalization
      localMassNonnegative localMassNonnegative
      localRows localColumns)

selectedCMP109L13DerivativeFitsRemainingIFTBudget :
  ∀ {Sample Row Column : Set}
    (samples : List Sample)
    (rows : List Row) (columns : List Column)
    (localDifferenceKernel :
      Normalized.KernelFamily Sample Row Column)
    vector →
  Minimal.siteWeightℚ * Fibre.natAsRational (List.length samples) ≡ 1ℚ →
  (∀ sample row →
    RectSchur.rectAbsoluteRowMass columns
      (localDifferenceKernel sample) row
    ≤ localTwoBackgroundMass) →
  (∀ sample column →
    RectSchur.rectAbsoluteColumnMass rows
      (localDifferenceKernel sample) column
    ≤ localTwoBackgroundMass) →
  RectSchur.rectVectorNormSq rows
    (RectSchur.rectApply columns
      (Normalized.normalizedKernel
        Minimal.siteWeightℚ samples localDifferenceKernel)
      vector)
  ≤ GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
      * RectSchur.rectVectorNormSq columns vector
selectedCMP109L13DerivativeFitsRemainingIFTBudget
    samples rows columns localDifferenceKernel vector
    normalization localRows localColumns =
  let
    base = selectedCMP109L13DerivativeSchurMassBudget
      samples rows columns localDifferenceKernel vector
      normalization localRows localColumns
    norm = RectSchur.rectVectorNormSq columns vector
    normNonnegative = Schur.sumNonnegative columns _
      (λ column → FiniteL2.squareNonnegative (vector column))
    instance
      normNN : NonNegative norm
      normNN = ℚ.nonNegative normNonnegative
  in
  ℚP.≤-trans base
    (ℚP.*-monoʳ-≤-nonNeg norm l13NormalizedSchurFitsIFTBudget)

cmp109L13NormalizedSchurArithmeticLevel : ProofLevel
cmp109L13NormalizedSchurArithmeticLevel = machineChecked

cmp109L13NormalizedDerivativeSchurLevel : ProofLevel
cmp109L13NormalizedDerivativeSchurLevel = machineChecked

-- The remaining local producer is now deliberately small and physical:
-- show the local equation-(0.12) transported-log derivative difference kernel
-- has row/column mass <= 1/4096 at each fine block site.
physicalCMP109L13LocalDerivativeMassLevel : ProofLevel
physicalCMP109L13LocalDerivativeMassLevel = conditional
