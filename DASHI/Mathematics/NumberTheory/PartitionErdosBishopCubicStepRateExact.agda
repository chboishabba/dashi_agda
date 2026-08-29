module DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact where

------------------------------------------------------------------------
-- SHARED ERDOS CUBIC STEP RATE
--
-- For positive n define
--
--   x_n = c / (2 sqrt(n))
--
-- using the actual Bishop Erdos/Machin constant c and the constructive root.
-- The divided tangent theorem gives, for r<=n,
--
--   sqrt(n-r) + r/(2 sqrt(n)) <= sqrt(n).
--
-- After multiplication by c and normalization of repeated addition, this is
-- exactly
--
--   shiftedBase(c sqrt(n-r), x_n, r) <= c sqrt(n).
--
-- This owner packages the n-dependent rate once; residual consumers indexed by
-- r do not rebuild the inverse/root/constant receipts.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_; _∸_)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as Constant
import DASHI.Foundations.BishopErdosMachinConstantPositiveExact as ConstantPositive
import DASHI.Foundations.BishopNatSquareRootDividedTangentExact as Tangent
import DASHI.Foundations.BishopNatSquareRootNonnegativeExact as RootNN
import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Foundations.BishopCubicTranslationGeometricRatioExact as Ratio
open import DASHI.Physics.YangMills.CompactLieProofLevel

erdosConstant : BishopReal.ℝ
erdosConstant = Constant.erdosMachinConstant

rootNat : Nat → BishopReal.ℝ
rootNat = Tangent.rootNat

record ErdosStepRate (n : Nat) (nPositive : suc 0 ≤ n) : Set₁ where
  field
    step : BishopReal.ℝ
    stepPositive : BishopReal._<_ BishopReal.0ℝ step

open ErdosStepRate public

canonicalErdosStepRate :
  (n : Nat) → (nPositive : suc 0 ≤ n) → ErdosStepRate n nPositive
canonicalErdosStepRate n nPositive = record
  { step =
      BishopReal._*_
        erdosConstant
        (Tangent.inverseDenominator n nPositive)
  ; stepPositive =
      BishopP.posx⇒0<x
        (BishopP.posx,y⇒posx*y
          ConstantPositive.erdosMachinConstantPositive
          inversePositive)
  }
  where
  inversePositive :
    BishopReal.Positive (Tangent.inverseDenominator n nPositive)
  inversePositive =
    BishopP.0<x⇒posx
      (BishopInverse.0<x⇒0<x⁻¹
        (Tangent.denominatorNonzero nPositive)
        (BishopP.posx⇒0<x
          (Tangent.denominatorPositive nPositive)))

stepRatio :
  ∀ {n} {nPositive : suc 0 ≤ n} →
  ErdosStepRate n nPositive → BishopReal.ℝ
stepRatio rate = Ratio.q (step rate) (stepPositive rate)

residualExponent : Nat → Nat → BishopReal.ℝ
residualExponent n r =
  BishopReal._*_ erdosConstant (rootNat (n ∸ r))

targetExponent : Nat → BishopReal.ℝ
targetExponent n =
  BishopReal._*_ erdosConstant (rootNat n)

residualExponentNonnegative :
  ∀ n r → BishopReal.NonNegative (residualExponent n r)
residualExponentNonnegative n r =
  BishopP.nonNegx,y⇒nonNegx*y
    (BishopP.pos⇒nonNeg ConstantPositive.erdosMachinConstantPositive)
    (RootNN.canonicalFloorSquareRootNonnegative (n ∸ r))

shiftedResidualExponent :
  ∀ {n} {nPositive : suc 0 ≤ n} →
  ErdosStepRate n nPositive → Nat → BishopReal.ℝ
shiftedResidualExponent {n} rate r =
  Iterated.shiftedBase
    (residualExponent n r)
    (step rate)
    r

shiftedResidualBelowTarget :
  ∀ {n r : Nat} →
  (nPositive : suc 0 ≤ n) →
  r ≤ n →
  let rate = canonicalErdosStepRate n nPositive in
  BishopReal._≤_
    (shiftedResidualExponent rate r)
    (targetExponent n)
shiftedResidualBelowTarget {n} {r} nPositive r≤n =
  let
    rate = canonicalErdosStepRate n nPositive
    c = erdosConstant
    inv = Tangent.inverseDenominator n nPositive
    B = rootNat (n ∸ r)
    embeddedR = Tangent.embedNat r

    tangent = Tangent.dividedTangentAdditive nPositive r≤n
    scaled =
      BishopP.*-monoˡ-≤-nonNeg
        tangent
        (BishopP.pos⇒nonNeg
          ConstantPositive.erdosMachinConstantPositive)

    normalize :
      BishopReal._≃_
        (shiftedResidualExponent rate r)
        (BishopReal._*_
          c
          (BishopReal._+_ B
            (BishopReal._*_ inv embeddedR)))
    normalize =
      BishopP.≃-trans
        (Iterated.shiftedBaseAsNatScale
          (residualExponent n r) (step rate) r)
        (BishopP.≃-trans
          (BishopP.+-cong
            BishopP.≃-refl
            (Iterated.natScaleAsEmbeddedNatMul r (step rate)))
          (let open BishopP.ℝ-Solver
           in solve 4
             (λ c′ B′ inv′ r′ →
               (c′ ⊗ B′) ⊕ (r′ ⊗ (c′ ⊗ inv′))
               ⊜ c′ ⊗ (B′ ⊕ (inv′ ⊗ r′)))
             BishopP.≃-refl c B inv embeddedR))
  in
  BishopP.≤-respˡ-≃ normalize scaled

partitionErdosBishopCubicStepRateLevel : ProofLevel
partitionErdosBishopCubicStepRateLevel = machineChecked
