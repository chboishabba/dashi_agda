{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact where

------------------------------------------------------------------------
-- ROW C BIDI SPATIAL ENGINE: ONE WEIGHTED HESSIAN ROW -> ALL DYSON POWERS
--
-- The CMP116 forward lane naturally provides an EXPONENTIALLY WEIGHTED Hessian
-- row.  The stochastic finite-speed consumer needs propagation of that weight
-- through repeated derivative interactions.  Exact finite matrix algebra gives
-- the missing bridge.
--
-- Let w satisfy
--
--       1 <= w(x,y),
--       w(x,z) <= w(x,y) w(y,z),
--
-- and let M>=0 obey the uniform weighted row bound
--
--       sum_y w(x,y) M(x,y) <= rho.
--
-- Then for every positive matrix power
--
--       sum_y w(x,y) M^n(x,y) <= rho^n.
--
-- Thus exponential spatial weighting is stable under the entire finite Dyson
-- series.  The physical YM input is only same-object identification of M with
-- the absolute covariant derivative generator and the one weighted CMP116 row.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanFiniteInfluenceNonnegativePowersExact as Positive

sumMono :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  Sums.sumRational values left ≤ Sums.sumRational values right
sumMono [] left right pointwise = ℚP.≤-refl
sumMono (value ∷ values) left right pointwise =
  ℚP.+-mono-≤
    (pointwise value)
    (sumMono values left right pointwise)

mulNN : ∀ {left right : ℚ} → 0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
mulNN {left} {right} leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = ℚ.nonNegative leftNN
      rightNonnegative : NonNegative right
      rightNonnegative = ℚ.nonNegative rightNN
  in
  ℚP.nonNegative⁻¹ (left * right)

record WeightedFiniteInfluenceMajorant (Site : Set) : Set₁ where
  field
    sites : List Site
    influence weight : Site → Site → ℚ

    influenceNonnegative : ∀ x y → 0ℚ ≤ influence x y
    weightNonnegative : ∀ x y → 0ℚ ≤ weight x y
    weightAtLeastOne : ∀ x y → 1ℚ ≤ weight x y
    weightTriangle : ∀ x middle y →
      weight x y ≤ weight x middle * weight middle y

    weightedRowMass : ℚ
    weightedRowMassNonnegative : 0ℚ ≤ weightedRowMass
    weightedRowMassBound : ∀ x →
      Sums.sumRational sites (λ y → weight x y * influence x y)
      ≤ weightedRowMass

open WeightedFiniteInfluenceMajorant public

influenceBelowWeightedInfluence :
  ∀ {Site} (dataSet : WeightedFiniteInfluenceMajorant Site) x y →
  influence dataSet x y
  ≤ weight dataSet x y * influence dataSet x y
influenceBelowWeightedInfluence dataSet x y =
  let
    scaled = Norm.scaleʳ-nonNeg
      (influenceNonnegative dataSet x y)
      (weightAtLeastOne dataSet x y)
  in
  subst
    (λ left → left ≤ weight dataSet x y * influence dataSet x y)
    (ℚP.*-identityˡ (influence dataSet x y))
    scaled

unweightedRowBound :
  ∀ {Site} (dataSet : WeightedFiniteInfluenceMajorant Site) x →
  Sums.sumRational (sites dataSet) (influence dataSet x)
  ≤ weightedRowMass dataSet
unweightedRowBound dataSet x =
  ℚP.≤-trans
    (sumMono
      (sites dataSet)
      (influence dataSet x)
      (λ y → weight dataSet x y * influence dataSet x y)
      (influenceBelowWeightedInfluence dataSet x))
    (weightedRowMassBound dataSet x)

asUnweightedMajorant :
  ∀ {Site} → WeightedFiniteInfluenceMajorant Site →
  Power.NonnegativeFiniteInfluenceMajorant Site
asUnweightedMajorant dataSet = record
  { Power.NonnegativeFiniteInfluenceMajorant.sites = sites dataSet
  ; Power.NonnegativeFiniteInfluenceMajorant.majorant = influence dataSet
  ; Power.NonnegativeFiniteInfluenceMajorant.majorantNonnegative =
      influenceNonnegative dataSet
  ; Power.NonnegativeFiniteInfluenceMajorant.rowMass = weightedRowMass dataSet
  ; Power.NonnegativeFiniteInfluenceMajorant.rowMassNonnegative =
      weightedRowMassNonnegative dataSet
  ; Power.NonnegativeFiniteInfluenceMajorant.rowMassBound =
      unweightedRowBound dataSet
  }

influencePower :
  ∀ {Site} → WeightedFiniteInfluenceMajorant Site → Nat → Site → Site → ℚ
influencePower dataSet =
  Power.majorantPowerPositive (asUnweightedMajorant dataSet)

influencePowerNonnegative :
  ∀ {Site} (dataSet : WeightedFiniteInfluenceMajorant Site) n x y →
  0ℚ ≤ influencePower dataSet n x y
influencePowerNonnegative dataSet =
  Positive.powerEntriesNonnegative (asUnweightedMajorant dataSet)

weightedPowerRow :
  ∀ {Site} → WeightedFiniteInfluenceMajorant Site → Nat → Site → ℚ
weightedPowerRow dataSet n x =
  Sums.sumRational (sites dataSet)
    (λ y → weight dataSet x y * influencePower dataSet n x y)

weightedPowerRowZero :
  ∀ {Site} (dataSet : WeightedFiniteInfluenceMajorant Site) x →
  weightedPowerRow dataSet zero x
  ≤ weightedRowMass dataSet
weightedPowerRowZero dataSet = weightedRowMassBound dataSet

weightedProductPointwise :
  ∀ {Site} (dataSet : WeightedFiniteInfluenceMajorant Site)
    n x middle y →
  weight dataSet x y
    * (influencePower dataSet n x middle * influence dataSet middle y)
  ≤ (weight dataSet x middle * influencePower dataSet n x middle)
      * (weight dataSet middle y * influence dataSet middle y)
weightedProductPointwise dataSet n x middle y =
  let
    p = influencePower dataSet n x middle
    m = influence dataSet middle y

    pmNN = mulNN
      (influencePowerNonnegative dataSet n x middle)
      (influenceNonnegative dataSet middle y)

    weightedTriangle = Norm.scaleʳ-nonNeg pmNN
      (weightTriangle dataSet x middle y)
  in
  subst
    (λ left → left ≤
      (weight dataSet x middle * p)
        * (weight dataSet middle y * m))
    (ℚRing.solve-∀
      (weight dataSet x y) p m)
    (subst
      (λ right →
        weight dataSet x y * (p * m) ≤ right)
      (ℚRing.solve-∀
        (weight dataSet x middle)
        (weight dataSet middle y) p m)
      weightedTriangle)

weightedInnerProductBound :
  ∀ {Site} (dataSet : WeightedFiniteInfluenceMajorant Site)
    n x middle →
  Sums.sumRational (sites dataSet)
    (λ y →
      weight dataSet x y
        * (influencePower dataSet n x middle * influence dataSet middle y))
  ≤ (weight dataSet x middle * influencePower dataSet n x middle)
      * weightedRowMass dataSet
weightedInnerProductBound dataSet n x middle =
  let
    pointwise = sumMono
      (sites dataSet)
      (λ y →
        weight dataSet x y
          * (influencePower dataSet n x middle * influence dataSet middle y))
      (λ y →
        (weight dataSet x middle * influencePower dataSet n x middle)
          * (weight dataSet middle y * influence dataSet middle y))
      (weightedProductPointwise dataSet n x middle)

    scale = weight dataSet x middle * influencePower dataSet n x middle
    scaleNN = mulNN
      (weightNonnegative dataSet x middle)
      (influencePowerNonnegative dataSet n x middle)

    factored :
      Sums.sumRational (sites dataSet)
        (λ y → scale * (weight dataSet middle y * influence dataSet middle y))
      ≡ scale * Sums.sumRational (sites dataSet)
        (λ y → weight dataSet middle y * influence dataSet middle y)
    factored = Sums.sumRationalScale
      scale (sites dataSet)
      (λ y → weight dataSet middle y * influence dataSet middle y)

    scaledRow = Norm.scaleNonnegative scale scaleNN
      (weightedRowMassBound dataSet middle)
  in
  ℚP.≤-trans pointwise
    (subst
      (λ left → left ≤ scale * weightedRowMass dataSet)
      (sym factored)
      scaledRow)

weightedPowerSuccessorExpansion :
  ∀ {Site} (dataSet : WeightedFiniteInfluenceMajorant Site)
    n x →
  weightedPowerRow dataSet (suc n) x
  ≡ Sums.sumRational (sites dataSet)
      (λ middle →
        Sums.sumRational (sites dataSet)
          (λ y →
            weight dataSet x y
              * (influencePower dataSet n x middle
                * influence dataSet middle y)))
weightedPowerSuccessorExpansion dataSet n x =
  let
    base = asUnweightedMajorant dataSet

    distributeOuter :
      weightedPowerRow dataSet (suc n) x
      ≡ Sums.sumRational (sites dataSet)
          (λ y →
            Sums.sumRational (sites dataSet)
              (λ middle →
                weight dataSet x y
                  * (influencePower dataSet n x middle
                    * influence dataSet middle y)))
    distributeOuter =
      Sums.sumRationalCong
        (sites dataSet)
        (λ y →
          weight dataSet x y *
            Power.matrixCompose base
              (Power.majorantPowerPositive base n)
              (Power.majorant base) x y)
        (λ y →
          Sums.sumRational (sites dataSet)
            (λ middle →
              weight dataSet x y
                * (influencePower dataSet n x middle
                  * influence dataSet middle y)))
        (λ y →
          Sums.sumRationalScale
            (weight dataSet x y)
            (sites dataSet)
            (λ middle →
              influencePower dataSet n x middle * influence dataSet middle y))
  in
  trans distributeOuter
    (Power.sumSwap
      (sites dataSet)
      (sites dataSet)
      (λ middle y →
        weight dataSet x y
          * (influencePower dataSet n x middle * influence dataSet middle y)))

weightedPowerStep :
  ∀ {Site} (dataSet : WeightedFiniteInfluenceMajorant Site)
    n x →
  weightedPowerRow dataSet (suc n) x
  ≤ weightedRowMass dataSet * weightedPowerRow dataSet n x
weightedPowerStep dataSet n x =
  let
    expanded = weightedPowerSuccessorExpansion dataSet n x

    innerBound = sumMono
      (sites dataSet)
      (λ middle →
        Sums.sumRational (sites dataSet)
          (λ y →
            weight dataSet x y
              * (influencePower dataSet n x middle * influence dataSet middle y)))
      (λ middle →
        (weight dataSet x middle * influencePower dataSet n x middle)
          * weightedRowMass dataSet)
      (weightedInnerProductBound dataSet n x)

    factored :
      Sums.sumRational (sites dataSet)
        (λ middle →
          (weight dataSet x middle * influencePower dataSet n x middle)
            * weightedRowMass dataSet)
      ≡ weightedRowMass dataSet * weightedPowerRow dataSet n x
    factored =
      trans
        (Sums.sumRationalCong
          (sites dataSet)
          (λ middle →
            (weight dataSet x middle * influencePower dataSet n x middle)
              * weightedRowMass dataSet)
          (λ middle →
            weightedRowMass dataSet
              * (weight dataSet x middle * influencePower dataSet n x middle))
          (λ middle → ℚP.*-comm
            (weight dataSet x middle * influencePower dataSet n x middle)
            (weightedRowMass dataSet)))
        (Sums.sumRationalScale
          (weightedRowMass dataSet)
          (sites dataSet)
          (λ middle →
            weight dataSet x middle * influencePower dataSet n x middle))
  in
  subst
    (λ left → left ≤ weightedRowMass dataSet * weightedPowerRow dataSet n x)
    expanded
    (subst
      (λ right →
        Sums.sumRational (sites dataSet)
          (λ middle →
            Sums.sumRational (sites dataSet)
              (λ y →
                weight dataSet x y
                  * (influencePower dataSet n x middle
                    * influence dataSet middle y)))
        ≤ right)
      factored
      innerBound)

weightedPowerRowBound :
  ∀ {Site} (dataSet : WeightedFiniteInfluenceMajorant Site)
    n x →
  weightedPowerRow dataSet n x
  ≤ Power.rationalPower (weightedRowMass dataSet) (suc n)
weightedPowerRowBound dataSet zero x = weightedPowerRowZero dataSet x
weightedPowerRowBound dataSet (suc n) x =
  let
    step = weightedPowerStep dataSet n x
    scaled = Norm.scaleNonnegative
      (weightedRowMass dataSet)
      (weightedRowMassNonnegative dataSet)
      (weightedPowerRowBound dataSet n x)
  in
  ℚP.≤-trans step
    (subst
      (λ right →
        weightedRowMass dataSet * weightedPowerRow dataSet n x ≤ right)
      (ℚP.*-comm
        (weightedRowMass dataSet)
        (Power.rationalPower (weightedRowMass dataSet) (suc n)))
      scaled)

finiteWeightedInfluencePowerAlgebraLevel : ProofLevel
finiteWeightedInfluencePowerAlgebraLevel = machineChecked

finiteWeightedInfluenceAllPowerRowLevel : ProofLevel
finiteWeightedInfluenceAllPowerRowLevel = machineChecked

-- Physical Row-C spatial leaf after this theorem: instantiate the literal
-- derivative generator and an exponential/submultiplicative weight from the SAME
-- spatial metric used by the CMP116 Hessian mark.  The one weighted row estimate
-- then propagates through all finite Dyson powers automatically.
literalYMWeightedDerivativeGeneratorLevel : ProofLevel
literalYMWeightedDerivativeGeneratorLevel = conditional
