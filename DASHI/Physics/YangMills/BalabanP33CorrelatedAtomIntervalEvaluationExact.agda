module DASHI.Physics.YangMills.BalabanP33CorrelatedAtomIntervalEvaluationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Ramon E. Moore, R. Baker Kearfott, Michael J. Cloud,
-- "Introduction to Interval Analysis", SIAM, 2009.
-- DOI: 10.1137/1.9780898717716.
--
-- DASHI CONTRIBUTION
--
-- Replace the previous G2 `jointUpper` shortcut by interval evaluation of the
-- ACTUAL atom formula
--
--       R_corr = sum raw_S - sum green_(S,T).
--
-- A caller now encloses each literal raw atom and each literal two-source
-- Green atom.  Finite monotonicity constructs the enclosure of the full signed
-- residual.  In particular, the upper residual uses the UPPER raw sum and the
-- LOWER Green sum, preserving cancellation/sign information exactly.
--
-- The final 55/18874368 comparison is therefore a check on a COMPUTED interval
-- endpoint, not a premise asserting R_corr itself is below the target.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as O

record RationalInterval : Set where
  constructor interval
  field
    lower upper : ℚ
    ordered : lower ≤ upper
open RationalInterval public

record LiesIn (value : ℚ) (box : RationalInterval) : Set where
  constructor liesIn
  field
    lowerSound : lower box ≤ value
    upperSound : value ≤ upper box
open LiesIn public

sumUpperMonotone :
  ∀ {A : Set} (indices : List A) (value upperValue : A → ℚ) →
  (∀ index → value index ≤ upperValue index) →
  Sums.sumRational indices value ≤ Sums.sumRational indices upperValue
sumUpperMonotone [] value upperValue pointwise = ℚP.≤-refl
sumUpperMonotone (index ∷ indices) value upperValue pointwise =
  ℚP.+-mono-≤
    (pointwise index)
    (sumUpperMonotone indices value upperValue pointwise)

sumLowerMonotone :
  ∀ {A : Set} (indices : List A) (lowerValue value : A → ℚ) →
  (∀ index → lowerValue index ≤ value index) →
  Sums.sumRational indices lowerValue ≤ Sums.sumRational indices value
sumLowerMonotone = sumUpperMonotone

record CorrelatedAtomIntervalEnvelope
    (family : O.CorrelatedResidualFamily) : Set₁ where
  field
    rawBox : Cube.Subset4 → RationalInterval
    greenBox : Cube.Subset4 → Cube.Subset4 → RationalInterval

    rawSound : ∀ subset →
      LiesIn (O.rawLocalizationAtom family subset) (rawBox subset)

    greenSound : ∀ left right →
      LiesIn (O.multiplierGreenAtom family left right)
        (greenBox left right)
open CorrelatedAtomIntervalEnvelope public

rawUpperSum :
  ∀ {family} → CorrelatedAtomIntervalEnvelope family → ℚ
rawUpperSum envelope =
  Sums.sumRational Cube.nonemptySubsets4
    (λ subset → upper (rawBox envelope subset))

greenLowerAt :
  ∀ {family} → CorrelatedAtomIntervalEnvelope family → Cube.Subset4 → ℚ
greenLowerAt envelope left =
  Sums.sumRational Cube.nonemptySubsets4
    (λ right → lower (greenBox envelope left right))

greenLowerSum :
  ∀ {family} → CorrelatedAtomIntervalEnvelope family → ℚ
greenLowerSum envelope =
  Sums.sumRational Cube.nonemptySubsets4 (greenLowerAt envelope)

atomIntervalResidualUpper :
  ∀ {family} → CorrelatedAtomIntervalEnvelope family → ℚ
atomIntervalResidualUpper envelope =
  rawUpperSum envelope - greenLowerSum envelope

rawTotalBelowIntervalUpper :
  ∀ {family} (envelope : CorrelatedAtomIntervalEnvelope family) →
  O.rawLocalizationTotal family ≤ rawUpperSum envelope
rawTotalBelowIntervalUpper envelope =
  sumUpperMonotone
    Cube.nonemptySubsets4
    (O.rawLocalizationAtom _)
    (λ subset → upper (rawBox envelope subset))
    (λ subset → upperSound (rawSound envelope subset))

greenLowerAtBelowActual :
  ∀ {family} (envelope : CorrelatedAtomIntervalEnvelope family) left →
  greenLowerAt envelope left
  ≤ Sums.sumRational Cube.nonemptySubsets4
      (O.multiplierGreenAtom family left)
greenLowerAtBelowActual envelope left =
  sumLowerMonotone
    Cube.nonemptySubsets4
    (λ right → lower (greenBox envelope left right))
    (O.multiplierGreenAtom _ left)
    (λ right → lowerSound (greenSound envelope left right))

greenLowerSumBelowActual :
  ∀ {family} (envelope : CorrelatedAtomIntervalEnvelope family) →
  greenLowerSum envelope ≤ O.greenPairTotal family
greenLowerSumBelowActual envelope =
  sumLowerMonotone
    Cube.nonemptySubsets4
    (greenLowerAt envelope)
    (λ left →
      Sums.sumRational Cube.nonemptySubsets4
        (O.multiplierGreenAtom _ left))
    (greenLowerAtBelowActual envelope)

correlatedResidualBelowAtomIntervalUpper :
  ∀ {family} (envelope : CorrelatedAtomIntervalEnvelope family) →
  O.correlatedResidualTotal family ≤ atomIntervalResidualUpper envelope
correlatedResidualBelowAtomIntervalUpper {family} envelope =
  ℚP.+-mono-≤
    (rawTotalBelowIntervalUpper envelope)
    (ℚP.neg-mono-≤ (greenLowerSumBelowActual envelope))

p33CorrelatedAtomIntervalEvaluationLevel : ProofLevel
p33CorrelatedAtomIntervalEvaluationLevel = machineChecked

-- Physical interval arithmetic still has to instantiate each literal atom from
-- the selected-background region.  The target residual inequality itself is no
-- longer accepted as an input by this module.
p33PhysicalCorrelatedAtomIntervalInstantiationLevel : ProofLevel
p33PhysicalCorrelatedAtomIntervalInstantiationLevel = conditional
