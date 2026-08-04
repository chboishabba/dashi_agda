module DASHI.Physics.YangMills.BalabanP33FiniteSignedRemainderSummationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- PURPOSE AND DASHI CONTRIBUTION
--
-- Prove the finite local-to-global estimate that the existing five-Hessian
-- module previously accepted as a field.  Pointwise two-sided estimates are
-- summed by induction over the literal finite cell list.  Incidence control and
-- nonnegativity of the coefficient then yield the signed global estimate
--
--   -w ||v||^2 <= sum_c R_c(v) <= w ||v||^2.
--
-- The lower inequality is the side required by coercivity; an upper estimate
-- alone cannot control a potentially negative Hessian perturbation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanPath4DirectionalEnergyContractionExact as Finite
open import DASHI.Physics.YangMills.CompactLieProofLevel

sumNegativeScale :
  ∀ {Cell : Set}
    (weight : ℚ) (cells : List Cell) (charge : Cell → ℚ) →
  Sums.sumRational cells (λ cell → - (weight * charge cell))
  ≡ - (weight * Sums.sumRational cells charge)
sumNegativeScale weight [] charge = ℚRing.solve []
sumNegativeScale weight (cell ∷ cells) charge
  rewrite sumNegativeScale weight cells charge = ℚRing.solve-∀

finitePointwiseUpperBound :
  ∀ {Cell : Set}
    (cells : List Cell)
    (localRemainder localNormCharge : Cell → ℚ)
    (weight : ℚ) →
  (∀ cell → localRemainder cell ≤ weight * localNormCharge cell) →
  Sums.sumRational cells localRemainder
  ≤ weight * Sums.sumRational cells localNormCharge
finitePointwiseUpperBound cells localRemainder localNormCharge weight pointwise =
  subst
    (λ upper → Sums.sumRational cells localRemainder ≤ upper)
    (Sums.sumRationalScale weight cells localNormCharge)
    (Finite.sumRationalMonotone
      cells
      localRemainder
      (λ cell → weight * localNormCharge cell)
      pointwise)

finitePointwiseLowerBound :
  ∀ {Cell : Set}
    (cells : List Cell)
    (localRemainder localNormCharge : Cell → ℚ)
    (weight : ℚ) →
  (∀ cell → - (weight * localNormCharge cell) ≤ localRemainder cell) →
  - (weight * Sums.sumRational cells localNormCharge)
  ≤ Sums.sumRational cells localRemainder
finitePointwiseLowerBound cells localRemainder localNormCharge weight pointwise =
  subst
    (λ lower → lower ≤ Sums.sumRational cells localRemainder)
    (sumNegativeScale weight cells localNormCharge)
    (Finite.sumRationalMonotone
      cells
      (λ cell → - (weight * localNormCharge cell))
      localRemainder
      pointwise)

record FiniteSignedRemainderFamily
    (Background State Cell : Set) : Set₁ where
  field
    cells : Background → List Cell
    localRemainder localNormCharge :
      Background → State → Cell → ℚ

    weight globalNormSq : Background → State → ℚ

    weightNonnegative : ∀ background state →
      0ℚ ≤ weight background state

    pointwiseUpper : ∀ background state cell →
      localRemainder background state cell
      ≤ weight background state * localNormCharge background state cell

    pointwiseLower : ∀ background state cell →
      - (weight background state * localNormCharge background state cell)
      ≤ localRemainder background state cell

    incidenceNormBound : ∀ background state →
      Sums.sumRational (cells background)
        (localNormCharge background state)
      ≤ globalNormSq background state

open FiniteSignedRemainderFamily public

globalRemainder :
  ∀ {Background State Cell} →
  FiniteSignedRemainderFamily Background State Cell →
  Background → State → ℚ
globalRemainder dataSet background state =
  Sums.sumRational (cells dataSet background)
    (localRemainder dataSet background state)

globalRemainderUpperBound :
  ∀ {Background State Cell}
    (dataSet : FiniteSignedRemainderFamily Background State Cell)
    background state →
  globalRemainder dataSet background state
  ≤ weight dataSet background state * globalNormSq dataSet background state
globalRemainderUpperBound dataSet background state =
  let
    coefficient = weight dataSet background state

    instance
      coefficientNonnegative : NonNegative coefficient
      coefficientNonnegative =
        nonNegative (weightNonnegative dataSet background state)
  in
  ℚP.≤-trans
    (finitePointwiseUpperBound
      (cells dataSet background)
      (localRemainder dataSet background state)
      (localNormCharge dataSet background state)
      coefficient
      (pointwiseUpper dataSet background state))
    (ℚP.*-monoˡ-≤-nonNeg coefficient
      (incidenceNormBound dataSet background state))

globalRemainderLowerBound :
  ∀ {Background State Cell}
    (dataSet : FiniteSignedRemainderFamily Background State Cell)
    background state →
  - (weight dataSet background state * globalNormSq dataSet background state)
  ≤ globalRemainder dataSet background state
globalRemainderLowerBound dataSet background state =
  let
    coefficient = weight dataSet background state
    localChargeSum =
      Sums.sumRational (cells dataSet background)
        (localNormCharge dataSet background state)

    instance
      coefficientNonnegative : NonNegative coefficient
      coefficientNonnegative =
        nonNegative (weightNonnegative dataSet background state)

    scaledIncidence :
      coefficient * localChargeSum
      ≤ coefficient * globalNormSq dataSet background state
    scaledIncidence =
      ℚP.*-monoˡ-≤-nonNeg coefficient
        (incidenceNormBound dataSet background state)
  in
  ℚP.≤-trans
    (ℚP.neg-antimono-≤ scaledIncidence)
    (finitePointwiseLowerBound
      (cells dataSet background)
      (localRemainder dataSet background state)
      (localNormCharge dataSet background state)
      coefficient
      (pointwiseLower dataSet background state))

record FiniteTwoSidedRemainderBound
    {Background State Cell : Set}
    (dataSet : FiniteSignedRemainderFamily Background State Cell)
    (background : Background) (state : State) : Set where
  field
    lower :
      - (weight dataSet background state * globalNormSq dataSet background state)
      ≤ globalRemainder dataSet background state

    upper :
      globalRemainder dataSet background state
      ≤ weight dataSet background state * globalNormSq dataSet background state

open FiniteTwoSidedRemainderBound public

finiteTwoSidedRemainderBound :
  ∀ {Background State Cell}
    (dataSet : FiniteSignedRemainderFamily Background State Cell)
    background state →
  FiniteTwoSidedRemainderBound dataSet background state
finiteTwoSidedRemainderBound dataSet background state = record
  { lower = globalRemainderLowerBound dataSet background state
  ; upper = globalRemainderUpperBound dataSet background state
  }

finitePointwiseSummationLevel : ProofLevel
finitePointwiseSummationLevel = machineChecked

finiteSignedRemainderGlobalizationLevel : ProofLevel
finiteSignedRemainderGlobalizationLevel = machineChecked
