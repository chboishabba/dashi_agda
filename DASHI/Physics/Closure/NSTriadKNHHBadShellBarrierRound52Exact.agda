module DASHI.Physics.Closure.NSTriadKNHHBadShellBarrierRound52Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 51 used the exact weighted Green response under the convenient
-- nonexpansive hypothesis alpha_q <= 1.  The recurrence algebra itself does not
-- require that hypothesis.  For
--
--   C_(q+1) <= alpha_q C_q + beta_q,
--   alpha_q,beta_q >= 0,
--
-- define the canonical response
--
--   R_0 = C_0,
--   R_(q+1) = alpha_q R_q + beta_q.
--
-- Then C_q <= R_q with NO assumption alpha_q <= 1.  More generally, every
-- nonnegative supersolution M with
--
--   C_0 <= M_0,
--   alpha_q M_q + beta_q <= M_(q+1)
--
-- dominates R and hence C.  Conversely R itself is the minimal supersolution.
-- Thus, constructively and without introducing a supremum object,
--
--   (forall q, R_q < T)
--
-- is equivalent to existence of a shell barrier M with forall q, M_q < T.
-- Transient alpha_q > 1 is therefore allowed whenever the barrier has room.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record GeneralHHBadRecurrence : Set where
  field
    profile alpha forcing : Nat → ℚ
    profileNonnegative : ∀ q → 0ℚ ≤ profile q
    alphaNonnegative : ∀ q → 0ℚ ≤ alpha q
    forcingNonnegative : ∀ q → 0ℚ ≤ forcing q
    recurrence : ∀ q →
      profile (suc q) ≤ alpha q * profile q + forcing q

open GeneralHHBadRecurrence public

canonicalResponse : GeneralHHBadRecurrence → Nat → ℚ
canonicalResponse input zero = profile input zero
canonicalResponse input (suc q) =
  alpha input q * canonicalResponse input q + forcing input q

canonicalResponseNonnegative :
  (input : GeneralHHBadRecurrence) →
  ∀ q → 0ℚ ≤ canonicalResponse input q
canonicalResponseNonnegative input zero = profileNonnegative input zero
canonicalResponseNonnegative input (suc q) =
  let instance
    alphaNNI = nonNegative (alphaNonnegative input q)
    responseNNI = nonNegative (canonicalResponseNonnegative input q)
    productNNI =
      ℚP.nonNeg*nonNeg⇒nonNeg
        (alpha input q) (canonicalResponse input q)
  in
  ℚP.+-mono-≤
    (ℚP.nonNegative⁻¹
      (alpha input q * canonicalResponse input q))
    (forcingNonnegative input q)

profileBelowCanonicalResponse :
  (input : GeneralHHBadRecurrence) →
  ∀ q → profile input q ≤ canonicalResponse input q
profileBelowCanonicalResponse input zero = ℚP.≤-refl
profileBelowCanonicalResponse input (suc q) =
  let
    inherited :
      alpha input q * profile input q
      ≤ alpha input q * canonicalResponse input q
    inherited =
      let instance alphaNNI = nonNegative (alphaNonnegative input q)
      in ℚP.*-monoˡ-≤-nonNeg
        (alpha input q)
        (profileBelowCanonicalResponse input q)

    step :
      alpha input q * profile input q + forcing input q
      ≤ alpha input q * canonicalResponse input q + forcing input q
    step = ℚP.+-mono-≤ inherited ℚP.≤-refl
  in
  ℚP.≤-trans (recurrence input q) step

record ShellSupersolution (input : GeneralHHBadRecurrence) : Set where
  field
    barrier : Nat → ℚ
    barrierNonnegative : ∀ q → 0ℚ ≤ barrier q
    baseBelowBarrier : profile input zero ≤ barrier zero
    barrierSupersolution : ∀ q →
      alpha input q * barrier q + forcing input q ≤ barrier (suc q)

open ShellSupersolution public

canonicalShellSupersolution :
  (input : GeneralHHBadRecurrence) → ShellSupersolution input
canonicalShellSupersolution input = record
  { barrier = canonicalResponse input
  ; barrierNonnegative = canonicalResponseNonnegative input
  ; baseBelowBarrier = ℚP.≤-refl
  ; barrierSupersolution = λ q → ℚP.≤-refl
  }

canonicalResponseIsMinimalBarrier :
  (input : GeneralHHBadRecurrence) →
  (supersolution : ShellSupersolution input) →
  ∀ q → canonicalResponse input q ≤ barrier supersolution q
canonicalResponseIsMinimalBarrier input supersolution zero =
  baseBelowBarrier supersolution
canonicalResponseIsMinimalBarrier input supersolution (suc q) =
  let
    inherited :
      alpha input q * canonicalResponse input q
      ≤ alpha input q * barrier supersolution q
    inherited =
      let instance alphaNNI = nonNegative (alphaNonnegative input q)
      in ℚP.*-monoˡ-≤-nonNeg
        (alpha input q)
        (canonicalResponseIsMinimalBarrier input supersolution q)

    withForcing :
      alpha input q * canonicalResponse input q + forcing input q
      ≤ alpha input q * barrier supersolution q + forcing input q
    withForcing = ℚP.+-mono-≤ inherited ℚP.≤-refl
  in
  ℚP.≤-trans withForcing (barrierSupersolution supersolution q)

profileBelowAnyShellBarrier :
  (input : GeneralHHBadRecurrence) →
  (supersolution : ShellSupersolution input) →
  ∀ q → profile input q ≤ barrier supersolution q
profileBelowAnyShellBarrier input supersolution q =
  ℚP.≤-trans
    (profileBelowCanonicalResponse input q)
    (canonicalResponseIsMinimalBarrier input supersolution q)

record BoundedShellBarrierBelowTarget
    (input : GeneralHHBadRecurrence) : Set where
  field
    supersolution : ShellSupersolution input
    target : ℚ
    barrierStrictlyBelowTarget : ∀ q →
      barrier supersolution q < target

open BoundedShellBarrierBelowTarget public

record CanonicalResponseBelowTarget
    (input : GeneralHHBadRecurrence) : Set where
  field
    target : ℚ
    canonicalStrictlyBelowTarget : ∀ q →
      canonicalResponse input q < target

open CanonicalResponseBelowTarget public

canonicalResponseTargetToBarrier :
  (input : GeneralHHBadRecurrence) →
  CanonicalResponseBelowTarget input →
  BoundedShellBarrierBelowTarget input
canonicalResponseTargetToBarrier input live = record
  { supersolution = canonicalShellSupersolution input
  ; target = CanonicalResponseBelowTarget.target live
  ; barrierStrictlyBelowTarget = canonicalStrictlyBelowTarget live
  }

barrierTargetToCanonicalResponse :
  (input : GeneralHHBadRecurrence) →
  BoundedShellBarrierBelowTarget input →
  CanonicalResponseBelowTarget input
barrierTargetToCanonicalResponse input live = record
  { target = BoundedShellBarrierBelowTarget.target live
  ; canonicalStrictlyBelowTarget = λ q →
      ℚP.≤-<-trans
        (canonicalResponseIsMinimalBarrier input
          (supersolution live) q)
        (barrierStrictlyBelowTarget live q)
  }

profileStrictlyBelowBarrierTarget :
  (input : GeneralHHBadRecurrence) →
  (live : BoundedShellBarrierBelowTarget input) →
  ∀ q → profile input q < BoundedShellBarrierBelowTarget.target live
profileStrictlyBelowBarrierTarget input live q =
  ℚP.≤-<-trans
    (profileBelowAnyShellBarrier input (supersolution live) q)
    (barrierStrictlyBelowTarget live q)

record DiscountedPotential (input : GeneralHHBadRecurrence) : Set where
  field
    potential : Nat → ℚ
    potentialNonnegative : ∀ q → 0ℚ ≤ potential q
    baseBelowPotential : profile input zero ≤ potential zero
    forcingBelowDiscountedCapacity : ∀ q →
      forcing input q
      ≤ potential (suc q) - alpha input q * potential q

open DiscountedPotential public

discountedPotentialAsSupersolution :
  (input : GeneralHHBadRecurrence) →
  DiscountedPotential input → ShellSupersolution input
discountedPotentialAsSupersolution input physical = record
  { barrier = potential physical
  ; barrierNonnegative = potentialNonnegative physical
  ; baseBelowBarrier = baseBelowPotential physical
  ; barrierSupersolution = λ q →
      let
        shifted :
          alpha input q * potential physical q + forcing input q
          ≤ alpha input q * potential physical q
            + (potential physical (suc q)
              - alpha input q * potential physical q)
        shifted =
          ℚP.+-mono-≤ ℚP.≤-refl
            (forcingBelowDiscountedCapacity physical q)
      in
      subst
        (alpha input q * potential physical q + forcing input q ≤_)
        (solve
          ( alpha input q
          ∷ potential physical q
          ∷ potential physical (suc q)
          ∷ []))
        shifted
  }

discountedPotentialPropagatesProfile :
  (input : GeneralHHBadRecurrence) →
  (physical : DiscountedPotential input) →
  ∀ q → profile input q ≤ potential physical q
discountedPotentialPropagatesProfile input physical =
  profileBelowAnyShellBarrier input
    (discountedPotentialAsSupersolution input physical)

barrierConsumerAllowsTransientAmplification : Bool
barrierConsumerAllowsTransientAmplification = true

alphaAtMostOneNotRequiredByBarrierAlgebra : Bool
alphaAtMostOneNotRequiredByBarrierAlgebra = true

canonicalResponseIsMinimalBarrierIsTrue :
  alphaAtMostOneNotRequiredByBarrierAlgebra ≡ true
canonicalResponseIsMinimalBarrierIsTrue = refl
