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
--
-- The finite Fubini/distributivity and constant-row-factor identities are
-- proved below from the literal finite sum.  They are not supplied as receipts.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

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

-- Index zero denotes the first positive matrix power M^1.
majorantPowerPositive :
  ∀ {Site} → NonnegativeFiniteInfluenceMajorant Site → Nat → Matrix Site
majorantPowerPositive dataSet zero = majorant dataSet
majorantPowerPositive dataSet (suc n) =
  matrixCompose dataSet (majorantPowerPositive dataSet n) (majorant dataSet)

rationalPower : ℚ → Nat → ℚ
rationalPower base zero = 1ℚ
rationalPower base (suc n) = rationalPower base n * base

------------------------------------------------------------------------
-- Finite-sum algebra used by the row-mass induction.
------------------------------------------------------------------------

sumAdd :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  Sums.sumRational values (λ value → left value + right value)
  ≡ Sums.sumRational values left + Sums.sumRational values right
sumAdd [] left right = refl
sumAdd (value ∷ values) left right
  rewrite sumAdd values left right =
  reassociate (left value) (right value)
    (Sums.sumRational values left) (Sums.sumRational values right)
  where
  reassociate : ∀ a b c d →
    (a + b) + (c + d) ≡ (a + c) + (b + d)
  reassociate = Data.Rational.Tactic.RingSolver.solve-∀

sumSwap :
  ∀ {A B : Set} (xs : List A) (ys : List B) (term : A → B → ℚ) →
  Sums.sumRational ys (λ y → Sums.sumRational xs (λ x → term x y))
  ≡ Sums.sumRational xs (λ x → Sums.sumRational ys (term x))
sumSwap [] ys term =
  zeroOuter ys
  where
  zeroOuter : ∀ {B : Set} (values : List B) →
    Sums.sumRational values (λ _ → 0ℚ) ≡ 0ℚ
  zeroOuter [] = refl
  zeroOuter (_ ∷ values) rewrite zeroOuter values = refl
sumSwap (x ∷ xs) ys term =
  trans
    (sumAdd ys (term x) (λ y → Sums.sumRational xs (λ z → term z y)))
    (cong
      (Sums.sumRational ys (term x) +_)
      (sumSwap xs ys term))

rowSumProductExact :
  ∀ {Site} (dataSet : NonnegativeFiniteInfluenceMajorant Site)
    (left : Matrix Site) x →
  Sums.sumRational (sites dataSet)
    (matrixCompose dataSet left (majorant dataSet) x)
  ≡ Sums.sumRational (sites dataSet)
      (λ middle →
        left x middle
        * Sums.sumRational (sites dataSet) (majorant dataSet middle))
rowSumProductExact dataSet left x =
  trans
    (sumSwap
      (sites dataSet)
      (sites dataSet)
      (λ middle y → left x middle * majorant dataSet middle y))
    (Sums.sumRationalCong
      (sites dataSet)
      (λ middle →
        Sums.sumRational (sites dataSet)
          (λ y → left x middle * majorant dataSet middle y))
      (λ middle →
        left x middle
        * Sums.sumRational (sites dataSet) (majorant dataSet middle))
      (λ middle → Sums.sumRationalScale
        (left x middle) (sites dataSet) (majorant dataSet middle)))

factorConstantRowMassExact :
  ∀ {Site} (dataSet : NonnegativeFiniteInfluenceMajorant Site)
    (weights : Site → ℚ) →
  Sums.sumRational (sites dataSet)
    (λ middle → weights middle * rowMass dataSet)
  ≡ rowMass dataSet * Sums.sumRational (sites dataSet) weights
factorConstantRowMassExact dataSet weights =
  trans
    (Sums.sumRationalCong
      (sites dataSet)
      (λ middle → weights middle * rowMass dataSet)
      (λ middle → rowMass dataSet * weights middle)
      (λ middle → ℚP.*-comm (weights middle) (rowMass dataSet)))
    (Sums.sumRationalScale
      (rowMass dataSet) (sites dataSet) weights)

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

-- Nonnegativity of positive powers can itself be derived from nonnegative
-- products/sums, but the current rational-order library exposes that through
-- several carrier-specific instance APIs.  Keep only this standard order fact
-- as an input to avoid duplicating rational-order infrastructure; no row/Fubini
-- or growth estimate is assumed.
record NonnegativeInfluencePowers
    {Site : Set} (dataSet : NonnegativeFiniteInfluenceMajorant Site) : Set₁ where
  field
    powerEntriesNonnegative : ∀ n x y →
      0ℚ ≤ majorantPowerPositive dataSet n x y

open NonnegativeInfluencePowers public

positivePowerRowMassBound :
  ∀ {Site} {dataSet : NonnegativeFiniteInfluenceMajorant Site} →
  NonnegativeInfluencePowers dataSet →
  ∀ n x →
  Sums.sumRational (sites dataSet) (majorantPowerPositive dataSet n x)
  ≤ rationalPower (rowMass dataSet) (suc n)
positivePowerRowMassBound {dataSet = dataSet} positivity zero x =
  subst
    (λ upper →
      Sums.sumRational (sites dataSet) (majorant dataSet x) ≤ upper)
    (sym (ℚP.*-identityˡ (rowMass dataSet)))
    (rowMassBound dataSet x)
positivePowerRowMassBound {dataSet = dataSet} positivity (suc n) x =
  let
    expanded = rowSumProductExact dataSet
      (majorantPowerPositive dataSet n) x

    weighted = sumTimesRow dataSet
      (majorantPowerPositive dataSet n x)
      (powerEntriesNonnegative positivity n x)

    factored = factorConstantRowMassExact dataSet
      (majorantPowerPositive dataSet n x)

    weightedToScaledRow :
      Sums.sumRational (sites dataSet)
        (λ middle →
          majorantPowerPositive dataSet n x middle
          * Sums.sumRational (sites dataSet) (majorant dataSet middle))
      ≤ rowMass dataSet
          * Sums.sumRational (sites dataSet)
              (majorantPowerPositive dataSet n x)
    weightedToScaledRow =
      subst
        (λ upper →
          Sums.sumRational (sites dataSet)
            (λ middle →
              majorantPowerPositive dataSet n x middle
              * Sums.sumRational (sites dataSet) (majorant dataSet middle))
          ≤ upper)
        factored
        weighted

    induction = positivePowerRowMassBound positivity n x

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

finiteInfluenceFiniteFubiniLevel : ProofLevel
finiteInfluenceFiniteFubiniLevel = machineChecked

finiteInfluenceRowMassPowerLevel : ProofLevel
finiteInfluenceRowMassPowerLevel = machineChecked

-- Physical same-object seam: the actual absolute derivative-generator entries
-- must be dominated by this nonnegative majorant, and the rooted KP/Hessian
-- estimate must supply rowMass uniformly in cutoff/volume.  The all-power row
-- growth is then downstream finite algebra.
physicalYMDerivativeInfluenceMajorantLevel : ProofLevel
physicalYMDerivativeInfluenceMajorantLevel = conditional
