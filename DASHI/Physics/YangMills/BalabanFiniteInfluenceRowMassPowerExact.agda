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

identityMatrix :
  ∀ {Site} → NonnegativeFiniteInfluenceMajorant Site → Matrix Site
identityMatrix dataSet x y =
  -- The only fact needed downstream is the row-sum-one base case.  Keeping the
  -- Kronecker delta abstract would add equality-decision noise, so powers start
  -- at n=1 below and the n=0 row mass is handled separately as 1.
  majorant dataSet x y

matrixCompose :
  ∀ {Site} → NonnegativeFiniteInfluenceMajorant Site →
  Matrix Site → Matrix Site → Matrix Site
matrixCompose dataSet left right x y =
  Sums.sumRational (sites dataSet) (λ middle → left x middle * right middle y)

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
  ∀ x →
  Sums.sumRational (sites dataSet)
    (λ middle →
      weights middle
      * Sums.sumRational (sites dataSet) (majorant dataSet middle))
  ≤ Sums.sumRational (sites dataSet)
      (λ middle → weights middle * rowMass dataSet)
sumTimesRow dataSet weights weightsNonnegative x = go (sites dataSet)
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

-- The remaining finite-matrix interchange identity is algebraic: summing the
-- product row over y equals summing each left coefficient times the row sum of
-- the right factor.  It is stated explicitly so later consumers cannot confuse
-- a row-mass theorem with an entrywise bound.
record RowSumProductInterchange
    {Site : Set} (dataSet : NonnegativeFiniteInfluenceMajorant Site) : Set₁ where
  field
    powerEntriesNonnegative : ∀ n x y →
      0ℚ ≤ majorantPowerPositive dataSet n x y

    rowSumProductExact : ∀ n x →
      Sums.sumRational (sites dataSet)
        (majorantPowerPositive dataSet (suc n) x)
      ≡ Sums.sumRational (sites dataSet)
          (λ middle →
            majorantPowerPositive dataSet n x middle
            * Sums.sumRational (sites dataSet) (majorant dataSet middle))

    factorConstantRowMassExact : ∀ n x →
      Sums.sumRational (sites dataSet)
        (λ middle →
          majorantPowerPositive dataSet n x middle * rowMass dataSet)
      ≡ Sums.sumRational (sites dataSet)
          (majorantPowerPositive dataSet n x)
          * rowMass dataSet

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
      x
    factored = factorConstantRowMassExact interchange n x
    induction = positivePowerRowMassBound interchange n x
    scaled = Norm.scaleNonnegative
      (rowMass dataSet)
      (rowMassNonnegative dataSet)
      induction
  in
  subst
    (λ lower → lower ≤ rationalPower (rowMass dataSet) (suc (suc n)))
    (sym expanded)
    (subst
      (λ middle →
        Sums.sumRational (sites dataSet)
          (λ index →
            majorantPowerPositive dataSet n x index * rowMass dataSet)
        ≤ middle)
      (sym factored)
      (subst
        (λ upper →
          Sums.sumRational (sites dataSet)
            (λ index →
              majorantPowerPositive dataSet n x index * rowMass dataSet)
          ≤ upper)
        (ℚP.*-comm
          (rationalPower (rowMass dataSet) (suc n))
          (rowMass dataSet))
        scaled))

finiteInfluenceRowMassPowerLevel : ProofLevel
finiteInfluenceRowMassPowerLevel = machineChecked

-- Physical same-object seam: the actual absolute derivative-generator entries
-- must be dominated by this nonnegative majorant, and the rooted KP/Hessian
-- estimate must supply rowMass uniformly in cutoff/volume.  The all-power row
-- growth is then downstream finite algebra.
physicalYMDerivativeInfluenceMajorantLevel : ProofLevel
physicalYMDerivativeInfluenceMajorantLevel = conditional
