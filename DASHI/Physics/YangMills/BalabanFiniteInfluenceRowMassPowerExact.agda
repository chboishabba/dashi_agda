module DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact where

------------------------------------------------------------------------
-- ROUND70: LOCAL ROW MASS -> ALL DYSON POWER ROW MASSES
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- R. A. Horn and C. R. Johnson,
-- "Matrix Analysis", Cambridge University Press, 2nd ed. (2013).
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Let M be a nonnegative finite influence majorant.  If every row sum is at
-- most rho, then the row sum of M^n is at most rho^n.  This is the quantitative
-- partner of Round70's exact support theorem: support says orders below graph
-- distance vanish, while this theorem bounds every remaining order by powers
-- of ONE volume-uniform local constant rho.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record NonnegativeFiniteInfluenceMajorant (Site : Set) : Set₁ where
  field
    sites : List Site
    majorant : Site → Site → ℚ
    majorantNonnegative : ∀ x y → 0ℚ ≤ majorant x y

    rowMass : ℚ
    rowMassNonnegative : 0ℚ ≤ rowMass
    rowMassBound : ∀ x →
      Sums.sumRational sites (majorant x) ≤ rowMass

open NonnegativeFiniteInfluenceMajorant public

Matrix : Set → Set
Matrix Site = Site → Site → ℚ

matrixCompose :
  ∀ {Site} → NonnegativeFiniteInfluenceMajorant Site →
  Matrix Site → Matrix Site → Matrix Site
matrixCompose dataSet left right x y =
  Sums.sumRational (sites dataSet) (λ middle → left x middle * right middle y)

-- Index zero denotes the first positive matrix power M^1.  This avoids adding
-- a decidable-equality Kronecker delta only for the n=0 semigroup term.
majorantPowerPositive :
  ∀ {Site} → NonnegativeFiniteInfluenceMajorant Site → Nat → Matrix Site
majorantPowerPositive dataSet zero = majorant dataSet
majorantPowerPositive dataSet (suc n) =
  matrixCompose dataSet (majorantPowerPositive dataSet n) (majorant dataSet)

rationalPower : ℚ → Nat → ℚ
rationalPower base zero = 1ℚ
rationalPower base (suc n) = rationalPower base n * base

sumTimesRow :
  ∀ {Site} (dataSet : NonnegativeFiniteInfluenceMajorant Site)
    (weights : Site → ℚ) →
  (∀ middle → 0ℚ ≤ weights middle) →
  Sums.sumRational (sites dataSet)
    (λ middle →
      weights middle
      * Sums.sumRational (sites dataSet) (majorant dataSet middle))
  ≤ Sums.sumRational (sites dataSet)
      (λ middle → weights middle * rowMass dataSet)
sumTimesRow dataSet weights weightsNonnegative = go (sites dataSet)
  where
  go : (values : List _) →
    Sums.sumRational values
      (λ middle →
        weights middle
        * Sums.sumRational (sites dataSet) (majorant dataSet middle))
    ≤ Sums.sumRational values
        (λ middle → weights middle * rowMass dataSet)
  go [] = ℚP.≤-refl
  go (middle ∷ values) =
    ℚP.+-mono-≤
      (Norm.scaleNonnegative
        (weights middle)
        (weightsNonnegative middle)
        (rowMassBound dataSet middle))
      (go values)

record RowSumProductInterchange
    {Site : Set} (dataSet : NonnegativeFiniteInfluenceMajorant Site) : Set₁ where
  field
    powerEntriesNonnegative : ∀ n x y →
      0ℚ ≤ majorantPowerPositive dataSet n x y

    -- Finite Fubini/distributivity for matrix multiplication.
    rowSumProductExact : ∀ n x →
      Sums.sumRational (sites dataSet)
        (majorantPowerPositive dataSet (suc n) x)
      ≡ Sums.sumRational (sites dataSet)
          (λ middle →
            majorantPowerPositive dataSet n x middle
            * Sums.sumRational (sites dataSet) (majorant dataSet middle))

    -- Pull the constant row-mass factor to the LEFT so the existing
    -- nonnegative-scaling lemma applies directly.
    factorConstantRowMassExact : ∀ n x →
      Sums.sumRational (sites dataSet)
        (λ middle →
          majorantPowerPositive dataSet n x middle * rowMass dataSet)
      ≡ rowMass dataSet
          * Sums.sumRational (sites dataSet)
              (majorantPowerPositive dataSet n x)

open RowSumProductInterchange public

positivePowerRowMassBound :
  ∀ {Site} {dataSet : NonnegativeFiniteInfluenceMajorant Site} →
  RowSumProductInterchange dataSet →
  ∀ n x →
  Sums.sumRational (sites dataSet) (majorantPowerPositive dataSet n x)
  ≤ rationalPower (rowMass dataSet) (suc n)
positivePowerRowMassBound {dataSet = dataSet} interchange zero x =
  subst
    (λ upper →
      Sums.sumRational (sites dataSet) (majorant dataSet x) ≤ upper)
    (sym (ℚP.*-identityˡ (rowMass dataSet)))
    (rowMassBound dataSet x)
positivePowerRowMassBound {dataSet = dataSet} interchange (suc n) x =
  let
    expanded = rowSumProductExact interchange n x

    weighted = sumTimesRow dataSet
      (majorantPowerPositive dataSet n x)
      (powerEntriesNonnegative interchange n x)

    factored = factorConstantRowMassExact interchange n x

    weightedToScaledRow :
      Sums.sumRational (sites dataSet)
        (λ middle →
          majorantPowerPositive dataSet n x middle
          * Sums.sumRational (sites dataSet) (majorant dataSet middle))
      ≤ rowMass dataSet
          * Sums.sumRational (sites dataSet)
              (majorantPowerPositive dataSet n x)
    weightedToScaledRow =
      ℚP.≤-trans weighted
        (subst
          (λ right →
            Sums.sumRational (sites dataSet)
              (λ middle →
                majorantPowerPositive dataSet n x middle * rowMass dataSet)
            ≤ right)
          factored
          ℚP.≤-refl)

    induction = positivePowerRowMassBound interchange n x

    scaled = Norm.scaleNonnegative
      (rowMass dataSet)
      (rowMassNonnegative dataSet)
      induction

    scaledToNextPower :
      rowMass dataSet
        * Sums.sumRational (sites dataSet)
            (majorantPowerPositive dataSet n x)
      ≤ rationalPower (rowMass dataSet) (suc (suc n))
    scaledToNextPower =
      subst
        (λ upper →
          rowMass dataSet
            * Sums.sumRational (sites dataSet)
                (majorantPowerPositive dataSet n x)
          ≤ upper)
        (ℚP.*-comm
          (rowMass dataSet)
          (rationalPower (rowMass dataSet) (suc n)))
        scaled

    weightedToNext = ℚP.≤-trans weightedToScaledRow scaledToNextPower
  in
  subst
    (λ lower → lower ≤ rationalPower (rowMass dataSet) (suc (suc n)))
    (sym expanded)
    weightedToNext

finiteInfluenceRowMassPowerLevel : ProofLevel
finiteInfluenceRowMassPowerLevel = machineChecked

-- Physical same-object seam: the actual absolute derivative-generator entries
-- must be dominated by this nonnegative majorant, and the rooted KP/Hessian
-- estimate must supply rowMass uniformly in cutoff/volume.  The all-power row
-- growth is then downstream finite algebra.
physicalYMDerivativeInfluenceMajorantLevel : ProofLevel
physicalYMDerivativeInfluenceMajorantLevel = conditional
