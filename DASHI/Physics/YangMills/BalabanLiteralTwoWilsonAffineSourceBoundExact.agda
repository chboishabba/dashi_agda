{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonAffineSourceBoundExact where

------------------------------------------------------------------------
-- LITERAL TWO-WILSON AFFINE SOURCE FACTOR
--
-- For the actual rational SU(2) path observable W with |W(U)| <= 1, use the
-- normalized two-source deformation
--
--   M_{s,t}(U) = (1 + s W_L(U)) (1 + t W_R(U)).
--
-- This has the same mixed derivative at (0,0) as the usual two-source
-- generating functional, but avoids importing an exponential source merely to
-- obtain a local analytic majorant.
--
-- On |s|,|t| <= 9/100,
--
--   |1+sW_L| <= 109/100,
--   |1+tW_R| <= 109/100,
--
-- hence
--
--   |M_{s,t}| <= (109/100)^2 = 11881/10000 < 6/5.
--
-- The final 6/5 is exactly the marked-inflation budget already used by
-- BalabanClayT5MarkedFernandezProcacciExact.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base
open import Data.Product.Base
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_; ∣_∣; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Wilson
import DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact as FP
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonCylinderBoundDataExact as Cylinder
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5

sourceRadius : ℚ
sourceRadius = + 9 / 100

onePlusSourceRadius : ℚ
onePlusSourceRadius = 1ℚ + sourceRadius

sourceRadiusNonnegative : 0ℚ ≤ sourceRadius
sourceRadiusNonnegative = ℚP.≤ᵇ⇒≤ tt

onePlusSourceRadiusNonnegative : 0ℚ ≤ onePlusSourceRadius
onePlusSourceRadiusNonnegative =
  ℚP.+-mono-≤ Wilson.oneNonnegative sourceRadiusNonnegative

twoMarkRadiusFitsSixFifths :
  onePlusSourceRadius * onePlusSourceRadius ≤ FP.markedInflation
twoMarkRadiusFitsSixFifths = ℚP.≤ᵇ⇒≤ tt

record SourceInsideRadius (source : ℚ) : Set where
  constructor source-inside-radius
  field
    absoluteSourceBelowRadius : ∣ source ∣ ≤ sourceRadius

open SourceInsideRadius public

affineSourceFactor : ℚ → ℚ → ℚ
affineSourceFactor source observableValue =
  1ℚ + source * observableValue

affineFactorAbsoluteBelowOnePlusRadius :
  ∀ source observableValue →
  SourceInsideRadius source →
  ∣ observableValue ∣ ≤ 1ℚ →
  ∣ affineSourceFactor source observableValue ∣ ≤ onePlusSourceRadius
affineFactorAbsoluteBelowOnePlusRadius source observableValue admissible observableBound =
  let
    productBound :
      ∣ source * observableValue ∣ ≤ sourceRadius
    productBound =
      subst
        (λ upper → ∣ source * observableValue ∣ ≤ upper)
        (ℚP.*-identityʳ sourceRadius)
        (Wilson.absoluteProductBound
          (absoluteSourceBelowRadius admissible)
          observableBound
          sourceRadiusNonnegative
          Wilson.oneNonnegative)

    triangle :
      ∣ 1ℚ + source * observableValue ∣
      ≤ ∣ 1ℚ ∣ + ∣ source * observableValue ∣
    triangle =
      ℚP.∣p+q∣≤∣p∣+∣q∣ 1ℚ (source * observableValue)

    summed :
      ∣ 1ℚ ∣ + ∣ source * observableValue ∣
      ≤ 1ℚ + sourceRadius
    summed =
      ℚP.+-mono-≤
        (subst (_≤ 1ℚ)
          (sym (ℚP.0≤p⇒∣p∣≡p Wilson.oneNonnegative))
          ℚP.≤-refl)
        productBound
  in
  ℚP.≤-trans triangle summed

twoWilsonAffineFactor :
  ℚ → ℚ → ℚ → ℚ → ℚ
twoWilsonAffineFactor leftSource rightSource leftValue rightValue =
  affineSourceFactor leftSource leftValue
  * affineSourceFactor rightSource rightValue

twoWilsonAffineFactorBelowSixFifths :
  ∀ leftSource rightSource leftValue rightValue →
  SourceInsideRadius leftSource →
  SourceInsideRadius rightSource →
  ∣ leftValue ∣ ≤ 1ℚ →
  ∣ rightValue ∣ ≤ 1ℚ →
  ∣ twoWilsonAffineFactor
      leftSource rightSource leftValue rightValue ∣
    ≤ FP.markedInflation
twoWilsonAffineFactorBelowSixFifths
    leftSource rightSource leftValue rightValue
    leftAdmissible rightAdmissible leftBound rightBound =
  let
    leftFactorBound =
      affineFactorAbsoluteBelowOnePlusRadius
        leftSource leftValue leftAdmissible leftBound

    rightFactorBound =
      affineFactorAbsoluteBelowOnePlusRadius
        rightSource rightValue rightAdmissible rightBound

    productBound =
      Wilson.absoluteProductBound
        leftFactorBound
        rightFactorBound
        onePlusSourceRadiusNonnegative
        onePlusSourceRadiusNonnegative
  in
  ℚP.≤-trans productBound twoMarkRadiusFitsSixFifths

literalTwoWilsonAffineFactorBelowSixFifths :
  ∀ {n : Nat}
    (leftPath rightPath : Wilson.RationalWilsonPath n)
    leftSource rightSource →
  SourceInsideRadius leftSource →
  SourceInsideRadius rightSource →
  ∀ configuration →
  ∣ twoWilsonAffineFactor
      leftSource rightSource
      (Wilson.literalWilsonPathObservable leftPath configuration)
      (Wilson.literalWilsonPathObservable rightPath configuration) ∣
    ≤ FP.markedInflation
literalTwoWilsonAffineFactorBelowSixFifths
    leftPath rightPath leftSource rightSource
    leftAdmissible rightAdmissible configuration =
  twoWilsonAffineFactorBelowSixFifths
    leftSource rightSource
    (Wilson.literalWilsonPathObservable leftPath configuration)
    (Wilson.literalWilsonPathObservable rightPath configuration)
    leftAdmissible
    rightAdmissible
    (Wilson.literalWilsonPathPointwiseUnitBounded leftPath configuration)
    (Wilson.literalWilsonPathPointwiseUnitBounded rightPath configuration)

literalTwoWilsonAffineSourceBoundLevel : ProofLevel
literalTwoWilsonAffineSourceBoundLevel = machineChecked


literalWilsonCylinderObservable :
  ∀ {n : Nat} →
  Data.List.Base.List (Wilson.RationalWilsonPath n) →
  Wilson.RationalWilsonObservable n
literalWilsonCylinderObservable {n} paths =
  T5.productLoopObservable
    (Cylinder.literalRationalSU2WilsonCylinderBounds {n})
    paths

literalWilsonCylinderPointwiseUnitBounded :
  ∀ {n : Nat}
    (paths : Data.List.Base.List (Wilson.RationalWilsonPath n)) →
  Wilson.PointwiseUnitBounded (literalWilsonCylinderObservable paths)
literalWilsonCylinderPointwiseUnitBounded {n} paths =
  Data.Product.Base.proj₂
    (Cylinder.finiteLiteralWilsonCylinderBound {n} paths)

literalTwoWilsonCylinderAffineFactorBelowSixFifths :
  ∀ {n : Nat}
    (leftPaths rightPaths :
      Data.List.Base.List (Wilson.RationalWilsonPath n))
    leftSource rightSource →
  SourceInsideRadius leftSource →
  SourceInsideRadius rightSource →
  ∀ configuration →
  ∣ twoWilsonAffineFactor
      leftSource rightSource
      (literalWilsonCylinderObservable leftPaths configuration)
      (literalWilsonCylinderObservable rightPaths configuration) ∣
    ≤ FP.markedInflation
literalTwoWilsonCylinderAffineFactorBelowSixFifths
    leftPaths rightPaths leftSource rightSource
    leftAdmissible rightAdmissible configuration =
  twoWilsonAffineFactorBelowSixFifths
    leftSource rightSource
    (literalWilsonCylinderObservable leftPaths configuration)
    (literalWilsonCylinderObservable rightPaths configuration)
    leftAdmissible
    rightAdmissible
    (literalWilsonCylinderPointwiseUnitBounded leftPaths configuration)
    (literalWilsonCylinderPointwiseUnitBounded rightPaths configuration)

literalTwoWilsonCylinderAffineSourceBoundLevel : ProofLevel
literalTwoWilsonCylinderAffineSourceBoundLevel = machineChecked
