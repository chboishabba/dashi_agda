module DASHI.Physics.Closure.NSTriadKNBishopRealUniformCriticalBarrierLiftExact where

------------------------------------------------------------------------
-- PERIODIC B / EXACT RATIONAL -> BISHOP-REAL CRITICAL BARRIER LIFT
--
-- The finite periodic machinery computes exact rational observables, but the
-- literal Clay semantic carrier uses constructive real time/fields.  Rational
-- certificates may be embedded into the Bishop-real scalar carrier only
-- through a genuine ordered-ring embedding.
--
-- This owner proves that every existing Round104 cutoff-uniform barrier lifts
-- losslessly:
--
--   X_N(T) + (nu-a) D_N <= C
--
-- becomes
--
--   embed X_N(T) + embed(nu-a) * embed D_N <= embed C.
--
-- This does NOT claim that a time-varying Q-valued Galerkin trajectory is
-- already the literal continuous-time trajectory.  It closes only the scalar
-- certificate transport that is actually valid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as Rational using (ℚ; toℚᵘ)
import Data.Rational.Properties as RationalP

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Embed
import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as R104

embed : ℚ → BishopReal.ℝ
embed = Embed.bishopRationalEmbed

embedAdd :
  (left right : ℚ) →
  BishopReal._≃_
    (embed (Rational._+_ left right))
    (BishopReal._+_ (embed left) (embed right))
embedAdd = Embed.bishopEmbedAdd

embedMul :
  (left right : ℚ) →
  BishopReal._≃_
    (embed (Rational._*_ left right))
    (BishopReal._*_ (embed left) (embed right))
embedMul left right =
  BishopP.≃-trans
    (BishopP.⋆-cong
      (RationalP.toℚᵘ-homo-* left right))
    (BishopP.⋆-distrib-*
      (toℚᵘ left)
      (toℚᵘ right))

embeddedSliceBarrierLeft :
  R104.IntegratedSignedCriticalSlice →
  BishopReal.ℝ
embeddedSliceBarrierLeft S =
  BishopReal._+_
    (embed (R104.terminalCritical S))
    (BishopReal._*_
      (embed (R104.retainedViscosity S))
      (embed (R104.criticalDissipation S)))

embeddedSliceCeilingRight :
  R104.IntegratedSignedCriticalSlice →
  BishopReal.ℝ
embeddedSliceCeilingRight S =
  BishopReal._+_
    (embed (R104.initialCritical S))
    (embed (R104.integrableRemainder S))

embeddedBarrierLeftMeaning :
  (S : R104.IntegratedSignedCriticalSlice) →
  BishopReal._≃_
    (embed
      (Rational._+_
        (R104.terminalCritical S)
        (Rational._*_
          (R104.retainedViscosity S)
          (R104.criticalDissipation S))))
    (embeddedSliceBarrierLeft S)
embeddedBarrierLeftMeaning S =
  BishopP.≃-trans
    (embedAdd
      (R104.terminalCritical S)
      (Rational._*_
        (R104.retainedViscosity S)
        (R104.criticalDissipation S)))
    (BishopP.+-congˡ
      (embed (R104.terminalCritical S))
      (embedMul
        (R104.retainedViscosity S)
        (R104.criticalDissipation S)))

embeddedCeilingRightMeaning :
  (S : R104.IntegratedSignedCriticalSlice) →
  BishopReal._≃_
    (embed
      (Rational._+_
        (R104.initialCritical S)
        (R104.integrableRemainder S)))
    (embeddedSliceCeilingRight S)
embeddedCeilingRightMeaning S =
  embedAdd
    (R104.initialCritical S)
    (R104.integrableRemainder S)

embeddedSignedCriticalSliceBarrier :
  (S : R104.IntegratedSignedCriticalSlice) →
  BishopReal._≤_
    (embeddedSliceBarrierLeft S)
    (embeddedSliceCeilingRight S)
embeddedSignedCriticalSliceBarrier S =
  let
    rational =
      R104.signedCriticalProductionAbsorbsIntoViscosity S
    embedded =
      Embed.bishopEmbedOrder rational
  in
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm (embeddedBarrierLeftMeaning S))
    (BishopP.≤-respʳ-≃
      (embeddedCeilingRightMeaning S)
      embedded)

embeddedUniformCriticalBarrier :
  (F : R104.UniformSignedCriticalProductionFamily) →
  (N : R104.Cutoff F) →
  BishopReal._≤_
    (embeddedSliceBarrierLeft (R104.slice F N))
    (embed (R104.uniformCriticalCeiling F))
embeddedUniformCriticalBarrier F N =
  let
    rational = R104.uniformGalerkinSignedCriticalProduction F N
    embedded = Embed.bishopEmbedOrder rational
  in
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm
      (embeddedBarrierLeftMeaning (R104.slice F N)))
    embedded

rationalCriticalBarrierLiftsToBishopReal : Bool
rationalCriticalBarrierLiftsToBishopReal = true

embeddingIntroducesConstantLoss : Bool
embeddingIntroducesConstantLoss = false

rationalTrajectoryIdentifiedWithLiteralRealTimeTrajectory : Bool
rationalTrajectoryIdentifiedWithLiteralRealTimeTrajectory = false

clayPromotion : Bool
clayPromotion = false

rationalCriticalBarrierLiftsToBishopRealIsTrue :
  rationalCriticalBarrierLiftsToBishopReal ≡ true
rationalCriticalBarrierLiftsToBishopRealIsTrue = refl

embeddingIntroducesConstantLossIsFalse :
  embeddingIntroducesConstantLoss ≡ false
embeddingIntroducesConstantLossIsFalse = refl

rationalTrajectoryIdentifiedWithLiteralRealTimeTrajectoryIsFalse :
  rationalTrajectoryIdentifiedWithLiteralRealTimeTrajectory ≡ false
rationalTrajectoryIdentifiedWithLiteralRealTimeTrajectoryIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
