module DASHI.Physics.YangMills.BalabanPath13PreconditionedFlatCombinedFloorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- DASHI CONTRIBUTION
--
-- Assemble the two source-scale flat normal sectors on the same 342732-state
-- carrier.  The 169-preconditioned average adjoint is an exact isometry, the
-- L=13 flat gauge adjoint has the exact 1/18 reduced Poincare floor, and their
-- cross inner product is zero.  Therefore
--
--   ||(169 Q)^* alpha + L_g,0^* gamma||^2
--      = ||alpha||^2 + ||L_g,0^* gamma||^2
--      >= (1/18)(||alpha||^2 + ||gamma||^2).
--
-- This is the literal preconditioned flat combined Gram floor required before
-- any selected-background perturbation is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanCMP109L13BlockAverageAdjointFloorExact as Average
import DASHI.Physics.YangMills.BalabanCMP109L13ConstraintRowPreconditionerExact as Precondition
import DASHI.Physics.YangMills.BalabanPath13FlatGaugeAdjointMatrixExact as Flat
import DASHI.Physics.YangMills.BalabanPath13FlatGaugeAdjointPoincareFloorExact as GaugeFloor
import DASHI.Physics.YangMills.BalabanPath13PreconditionedAverageGaugeOrthogonalityExact as Orthogonal

record CombinedMultiplier13 : Set where
  field
    averageMultiplier : Average.RowVector
    gaugeMultiplier : Flat.GaugeMultiplier13

open CombinedMultiplier13 public

combinedRowNormSq13 : CombinedMultiplier13 → ℚ
combinedRowNormSq13 multiplier =
  Average.rowNormSq (averageMultiplier multiplier)
  + GaugeFloor.gaugeMultiplierNormSq13 (gaugeMultiplier multiplier)

combinedAdjoint13 : CombinedMultiplier13 → Average.StateVector
combinedAdjoint13 multiplier state =
  Precondition.preconditionedBlockAverageAdjoint
    (averageMultiplier multiplier) state
  + Flat.flatGaugeAdjoint13 (gaugeMultiplier multiplier) state

combinedAdjointNormSq13 : CombinedMultiplier13 → ℚ
combinedAdjointNormSq13 multiplier =
  Average.stateNormSq (combinedAdjoint13 multiplier)

stateDot13 : Average.StateVector → Average.StateVector → ℚ
stateDot13 = Physical.physicalCoordinateDot

stateDotSymmetric13 : ∀ left right →
  stateDot13 left right ≡ stateDot13 right left
stateDotSymmetric13 left right =
  sumRationalCong
    (Physical.physicalSU2Coordinates Side13.side13) _ _
    (λ state → ℚRing.solve-∀ (left state) (right state))

combinedNormPythagoras13 : ∀ multiplier →
  combinedAdjointNormSq13 multiplier
  ≡ Average.stateNormSq
      (Precondition.preconditionedBlockAverageAdjoint
        (averageMultiplier multiplier))
    + Flat.flatGaugeAdjointNormSq13 (gaugeMultiplier multiplier)
combinedNormPythagoras13 multiplier =
  let
    averageVector =
      Precondition.preconditionedBlockAverageAdjoint
        (averageMultiplier multiplier)
    gaugeVector = Flat.flatGaugeAdjoint13 (gaugeMultiplier multiplier)

    expand :
      combinedAdjointNormSq13 multiplier
      ≡ Average.stateNormSq averageVector
        + (stateDot13 averageVector gaugeVector
          + stateDot13 gaugeVector averageVector)
        + Flat.flatGaugeAdjointNormSq13 (gaugeMultiplier multiplier)
    expand =
      trans
        (sumRationalCong
          (Physical.physicalSU2Coordinates Side13.side13) _ _
          (λ state →
            ℚRing.solve-∀ (averageVector state) (gaugeVector state)))
        (sumFourTerms averageVector gaugeVector)

    firstCrossZero : stateDot13 averageVector gaugeVector ≡ Data.Rational.0ℚ
    firstCrossZero =
      Orthogonal.preconditionedAverageGaugeInnerExactZero
        (averageMultiplier multiplier) (gaugeMultiplier multiplier)

    secondCrossZero : stateDot13 gaugeVector averageVector ≡ Data.Rational.0ℚ
    secondCrossZero =
      trans
        (stateDotSymmetric13 gaugeVector averageVector)
        firstCrossZero
  in
  trans expand
    (subst
      (λ firstCross →
        Average.stateNormSq averageVector
        + (firstCross + stateDot13 gaugeVector averageVector)
        + Flat.flatGaugeAdjointNormSq13 (gaugeMultiplier multiplier)
        ≡ Average.stateNormSq averageVector
          + Flat.flatGaugeAdjointNormSq13 (gaugeMultiplier multiplier))
      (sym firstCrossZero)
      (subst
        (λ secondCross →
          Average.stateNormSq averageVector
          + (Data.Rational.0ℚ + secondCross)
          + Flat.flatGaugeAdjointNormSq13 (gaugeMultiplier multiplier)
          ≡ Average.stateNormSq averageVector
            + Flat.flatGaugeAdjointNormSq13 (gaugeMultiplier multiplier))
        (sym secondCrossZero)
        (ℚRing.solve-∀
          (Average.stateNormSq averageVector)
          (Flat.flatGaugeAdjointNormSq13 (gaugeMultiplier multiplier)))))
  where
  sumFourTerms : ∀ averageVector gaugeVector →
    sumRational (Physical.physicalSU2Coordinates Side13.side13)
      (λ state →
        sq (averageVector state)
        + (averageVector state * gaugeVector state
          + gaugeVector state * averageVector state)
        + sq (gaugeVector state))
    ≡ Average.stateNormSq averageVector
      + (stateDot13 averageVector gaugeVector
        + stateDot13 gaugeVector averageVector)
      + Average.stateNormSq gaugeVector
  sumFourTerms averageVector gaugeVector =
    finiteSumExpand
      (Physical.physicalSU2Coordinates Side13.side13)
      averageVector gaugeVector

  finiteSumExpand :
    ∀ {A : Set} (values : Agda.Builtin.List.List A)
      (left right : A → ℚ) →
    sumRational values
      (λ value →
        sq (left value)
        + (left value * right value + right value * left value)
        + sq (right value))
    ≡ sumRational values (λ value → sq (left value))
      + (sumRational values (λ value → left value * right value)
        + sumRational values (λ value → right value * left value))
      + sumRational values (λ value → sq (right value))
  finiteSumExpand Agda.Builtin.List.[] left right = ℚRing.solve []
  finiteSumExpand (Agda.Builtin.List._∷_ value values) left right
    rewrite finiteSumExpand values left right =
    ℚRing.solve-∀
      (left value) (right value)
      (sumRational values (λ current → sq (left current)))
      (sumRational values (λ current → left current * right current))
      (sumRational values (λ current → right current * left current))
      (sumRational values (λ current → sq (right current)))

record ReducedCombinedMultiplier13 (multiplier : CombinedMultiplier13) : Set where
  field
    gaugeReduced :
      GaugeFloor.FlatGaugeReducedMultiplier13 (gaugeMultiplier multiplier)

open ReducedCombinedMultiplier13 public

oneEighteenthBelowOne : ∀ value →
  0ℚ ≤ value → LDL.oneEighteenth * value ≤ value
oneEighteenthBelowOne value nonnegative =
  let
    differenceNonnegative :
      0ℚ ≤ value - LDL.oneEighteenth * value
    differenceNonnegative =
      subst
        (λ candidate → 0ℚ ≤ candidate)
        (ℚRing.solve-∀ value)
        (scaleNonnegative value nonnegative)
  in
  differenceImpliesBelow differenceNonnegative
  where
  scaleNonnegative : ∀ value → 0ℚ ≤ value →
    0ℚ ≤ (+ 17 / 18) * value
  scaleNonnegative current currentNonnegative =
    let
      instance
        coefficientNN : ℚ.NonNegative (+ 17 / 18)
        coefficientNN = ℚ.nonNegative (ℚP.nonNegative⁻¹ (+ 17 / 18))
    in
    ℚP.*-monoʳ-≤-nonNeg current currentNonnegative

  differenceImpliesBelow : ∀ {left right : ℚ} →
    0ℚ ≤ right - left → left ≤ right
  differenceImpliesBelow {left} {right} nonnegative =
    ℚP.≤-trans
      (subst (λ candidate → left ≤ candidate)
        (sym (ℚRing.solve-∀ left)) ℚP.≤-refl)
      (subst
        (λ candidate → left ≤ candidate)
        (ℚRing.solve-∀ left right)
        (ℚP.+-monoˡ-≤ left nonnegative))

preconditionedFlatCombinedFloor13 :
  ∀ multiplier → ReducedCombinedMultiplier13 multiplier →
  LDL.oneEighteenth * combinedRowNormSq13 multiplier
  ≤ combinedAdjointNormSq13 multiplier
preconditionedFlatCombinedFloor13 multiplier reduced =
  let
    alphaNorm = Average.rowNormSq (averageMultiplier multiplier)
    gammaNorm = GaugeFloor.gaugeMultiplierNormSq13 (gaugeMultiplier multiplier)
    averageExact =
      Precondition.preconditionedAverageAdjointNormExact
        (averageMultiplier multiplier)
    gaugeFloor =
      GaugeFloor.flatGaugeAdjointPoincareFloor13
        (gaugeMultiplier multiplier) (gaugeReduced reduced)
    alphaNonnegative =
      Average.Schur.sumNonnegative Average.BlockAverage.selectedBlockAverageRows
        (λ row → sq (averageMultiplier multiplier row))
        (λ row → Average.FiniteL2.squareNonnegative
          (averageMultiplier multiplier row))
  in
  subst
    (λ upper →
      LDL.oneEighteenth * combinedRowNormSq13 multiplier ≤ upper)
    (sym (combinedNormPythagoras13 multiplier))
    (subst
      (λ averageAdjointNorm →
        LDL.oneEighteenth * (alphaNorm + gammaNorm)
        ≤ averageAdjointNorm
          + Flat.flatGaugeAdjointNormSq13 (gaugeMultiplier multiplier))
      (sym averageExact)
      (subst
        (λ left →
          left
          ≤ alphaNorm
            + Flat.flatGaugeAdjointNormSq13 (gaugeMultiplier multiplier))
        (ℚRing.solve-∀ LDL.oneEighteenth alphaNorm gammaNorm)
        (ℚP.+-mono-≤
          (oneEighteenthBelowOne alphaNorm alphaNonnegative)
          gaugeFloor)))

path13PreconditionedFlatCombinedFloorLevel : ProofLevel
path13PreconditionedFlatCombinedFloorLevel = machineChecked
