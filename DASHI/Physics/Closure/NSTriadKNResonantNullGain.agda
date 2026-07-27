module DASHI.Physics.Closure.NSTriadKNResonantNullGain where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality
  using (sym; cong; cong₂; module ≡-Reasoning)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical

------------------------------------------------------------------------
-- Exact resonant null identity.
--
-- If p + q = k and u_p is transverse to p, then
--
--     u_p · q = u_p · k.
--
-- Likewise, transversality of u_q gives u_q · p = u_q · k.
-- These are the literal high-high-to-low derivative gains: the derivative
-- can be measured at the low output k rather than at a high input.
------------------------------------------------------------------------

record ResonantDotLaws {v s : Level}
    (Vector : Set v) (Scalar : Set s) : Set (lsuc (v ⊔ s)) where
  field
    scalarZero : Scalar
    scalarAdd : Scalar → Scalar → Scalar
    scalarAddZeroLeft : ∀ x → scalarAdd scalarZero x ≡ x
    scalarAddZeroRight : ∀ x → scalarAdd x scalarZero ≡ x

    vectorAdd : Vector → Vector → Vector
    waveVector : Z3.FourierMode → Vector
    bilinearDot : Vector → Vector → Scalar

    waveVectorAdd : ∀ p q →
      waveVector (Z3.addMode p q)
      ≡ vectorAdd (waveVector p) (waveVector q)

    dotAddRight : ∀ u v w →
      bilinearDot u (vectorAdd v w)
      ≡ scalarAdd (bilinearDot u v) (bilinearDot u w)

open ResonantDotLaws public

TransverseAt :
  ∀ {v s} {Vector : Set v} {Scalar : Set s} →
  ResonantDotLaws Vector Scalar →
  Z3.FourierMode → Vector → Set s
TransverseAt L mode velocity =
  bilinearDot L velocity (waveVector L mode) ≡ scalarZero L

resonantNullIdentityP :
  ∀ {v s} {Vector : Set v} {Scalar : Set s}
    (L : ResonantDotLaws Vector Scalar)
    (τ : Physical.PhysicalTriadIncidence)
    (uP : Vector) →
  TransverseAt L (Physical.p τ) uP →
  bilinearDot L uP (waveVector L (Physical.q τ))
  ≡
  bilinearDot L uP (waveVector L (Physical.k τ))
resonantNullIdentityP L τ uP transverse =
  begin
    bilinearDot L uP (waveVector L (Physical.q τ))
  ≡⟨ sym (scalarAddZeroLeft L _) ⟩
    scalarAdd L
      (scalarZero L)
      (bilinearDot L uP (waveVector L (Physical.q τ)))
  ≡⟨ cong₂ (scalarAdd L) (sym transverse) refl ⟩
    scalarAdd L
      (bilinearDot L uP (waveVector L (Physical.p τ)))
      (bilinearDot L uP (waveVector L (Physical.q τ)))
  ≡⟨ sym (dotAddRight L uP
        (waveVector L (Physical.p τ))
        (waveVector L (Physical.q τ))) ⟩
    bilinearDot L uP
      (vectorAdd L
        (waveVector L (Physical.p τ))
        (waveVector L (Physical.q τ)))
  ≡⟨ cong (bilinearDot L uP)
        (sym (waveVectorAdd L (Physical.p τ) (Physical.q τ))) ⟩
    bilinearDot L uP
      (waveVector L
        (Z3.addMode (Physical.p τ) (Physical.q τ)))
  ≡⟨ cong (λ mode → bilinearDot L uP (waveVector L mode))
        (Physical.resonance τ) ⟩
    bilinearDot L uP (waveVector L (Physical.k τ))
  ∎
  where open ≡-Reasoning

resonantNullIdentityQ :
  ∀ {v s} {Vector : Set v} {Scalar : Set s}
    (L : ResonantDotLaws Vector Scalar)
    (τ : Physical.PhysicalTriadIncidence)
    (uQ : Vector) →
  TransverseAt L (Physical.q τ) uQ →
  bilinearDot L uQ (waveVector L (Physical.p τ))
  ≡
  bilinearDot L uQ (waveVector L (Physical.k τ))
resonantNullIdentityQ L τ uQ transverse =
  begin
    bilinearDot L uQ (waveVector L (Physical.p τ))
  ≡⟨ sym (scalarAddZeroRight L _) ⟩
    scalarAdd L
      (bilinearDot L uQ (waveVector L (Physical.p τ)))
      (scalarZero L)
  ≡⟨ cong₂ (scalarAdd L) refl (sym transverse) ⟩
    scalarAdd L
      (bilinearDot L uQ (waveVector L (Physical.p τ)))
      (bilinearDot L uQ (waveVector L (Physical.q τ)))
  ≡⟨ sym (dotAddRight L uQ
        (waveVector L (Physical.p τ))
        (waveVector L (Physical.q τ))) ⟩
    bilinearDot L uQ
      (vectorAdd L
        (waveVector L (Physical.p τ))
        (waveVector L (Physical.q τ)))
  ≡⟨ cong (bilinearDot L uQ)
        (sym (waveVectorAdd L (Physical.p τ) (Physical.q τ))) ⟩
    bilinearDot L uQ
      (waveVector L
        (Z3.addMode (Physical.p τ) (Physical.q τ)))
  ≡⟨ cong (λ mode → bilinearDot L uQ (waveVector L mode))
        (Physical.resonance τ) ⟩
    bilinearDot L uQ (waveVector L (Physical.k τ))
  ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Quantitative consequence.
------------------------------------------------------------------------

record ResonantCoefficientMagnitudeLaws
    {v s : Level}
    (Vector : Set v) (Scalar : Set s)
    (dotLaws : ResonantDotLaws Vector Scalar) :
    Set (lsuc (v ⊔ s)) where
  field
    vectorSize : Vector → Nat
    modeSize : Z3.FourierMode → Nat
    scalarSize : Scalar → Nat

    coefficientMagnitude :
      Physical.PhysicalTriadIncidence →
      Vector → Vector → Vector → Nat

    coefficientBoundByDot :
      (τ : Physical.PhysicalTriadIncidence)
      (uP uQ uK : Vector) →
      coefficientMagnitude τ uP uQ uK
      ≤
      scalarSize
        (bilinearDot dotLaws uP
          (waveVector dotLaws (Physical.q τ)))
      * (vectorSize uQ * vectorSize uK)

    dotMagnitudeBound :
      (u : Vector) (mode : Z3.FourierMode) →
      scalarSize
        (bilinearDot dotLaws u (waveVector dotLaws mode))
      ≤ vectorSize u * modeSize mode

open ResonantCoefficientMagnitudeLaws public

nullDotMagnitudeBoundP :
  ∀ {v s} {Vector : Set v} {Scalar : Set s}
    {L : ResonantDotLaws Vector Scalar}
    (M : ResonantCoefficientMagnitudeLaws Vector Scalar L)
    (τ : Physical.PhysicalTriadIncidence)
    (uP : Vector) →
  TransverseAt L (Physical.p τ) uP →
  scalarSize M
    (bilinearDot L uP (waveVector L (Physical.q τ)))
  ≤
  vectorSize M uP * modeSize M (Physical.k τ)
nullDotMagnitudeBoundP M τ uP transverse
  rewrite resonantNullIdentityP _ τ uP transverse =
  dotMagnitudeBound M uP (Physical.k τ)

highHighLowCoefficientBound :
  ∀ {v s} {Vector : Set v} {Scalar : Set s}
    {L : ResonantDotLaws Vector Scalar}
    (M : ResonantCoefficientMagnitudeLaws Vector Scalar L)
    (τ : Physical.PhysicalTriadIncidence)
    (uP uQ uK : Vector) →
  TransverseAt L (Physical.p τ) uP →
  coefficientMagnitude M τ uP uQ uK
  ≤
  (vectorSize M uP * modeSize M (Physical.k τ))
  * (vectorSize M uQ * vectorSize M uK)
highHighLowCoefficientBound M τ uP uQ uK transverse =
  Nat.≤-trans
    (coefficientBoundByDot M τ uP uQ uK)
    (Nat.*-mono-≤
      (nullDotMagnitudeBoundP M τ uP transverse)
      Nat.≤-refl)

resonantNullGainClosed : Bool
resonantNullGainClosed = true

resonantNullGainClosedIsTrue : resonantNullGainClosed ≡ true
resonantNullGainClosedIsTrue = refl
