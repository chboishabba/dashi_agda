module DASHI.Analysis.RiemannQuarticTriadicCodecKernelBridgeExact where

------------------------------------------------------------------------
-- RH / X6 / TRIADIC CODEC KERNEL BRIDGE
--
-- DASHI CONTRIBUTION
--
-- Reuse the canonical codec carrier directly:
--
--   Kernel d = Vec Trit d.
--
-- The finite-Heisenberg X6 carrier is literally six Trit coordinates, so this
-- module constructs an exact two-sided chart
--
--   X6 <-> Kernel 6.
--
-- It also exposes Kernel 4 as the canonical four-trit codec object and defines
-- its support-based puncture/reopen operation.  The arithmetic owner separately
-- proves 3^4-1=80; this module does NOT claim a cardinality theorem for the
-- dependent punctured subtype until that finite enumeration is paid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ; _,_; proj₁)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Analysis.RiemannQuarticBalancedTernaryStencilExact as Stencil

open Codec using ([]ᵥ; _∷ᵥ_; support)

------------------------------------------------------------------------
-- 1. Exact X6 <-> codec Kernel 6 chart.
------------------------------------------------------------------------

Kernel6 : Set
Kernel6 = Codec.Kernel 6

x6ToKernel6 : H.X6 → Kernel6
x6ToKernel6 (H.x6 a0 a1 a2 a3 a4 a5) =
  a0 ∷ᵥ
  a1 ∷ᵥ
  a2 ∷ᵥ
  a3 ∷ᵥ
  a4 ∷ᵥ
  a5 ∷ᵥ
  []ᵥ

kernel6ToX6 : Kernel6 → H.X6
kernel6ToX6
  (a0 ∷ᵥ
   a1 ∷ᵥ
   a2 ∷ᵥ
   a3 ∷ᵥ
   a4 ∷ᵥ
   a5 ∷ᵥ
   []ᵥ) =
  H.x6 a0 a1 a2 a3 a4 a5

x6Kernel6RoundTrip :
  (x : H.X6) →
  kernel6ToX6 (x6ToKernel6 x) ≡ x
x6Kernel6RoundTrip (H.x6 a0 a1 a2 a3 a4 a5) = refl

kernel6X6RoundTrip :
  (kernel : Kernel6) →
  x6ToKernel6 (kernel6ToX6 kernel) ≡ kernel
kernel6X6RoundTrip
  (a0 ∷ᵥ
   a1 ∷ᵥ
   a2 ∷ᵥ
   a3 ∷ᵥ
   a4 ∷ᵥ
   a5 ∷ᵥ
   []ᵥ) = refl

------------------------------------------------------------------------
-- 2. Canonical codec Kernel 4 and its origin.
------------------------------------------------------------------------

Kernel4 : Set
Kernel4 = Codec.Kernel 4

zeroKernel4 : Kernel4
zeroKernel4 =
  zer ∷ᵥ
  zer ∷ᵥ
  zer ∷ᵥ
  zer ∷ᵥ
  []ᵥ

------------------------------------------------------------------------
-- 3. Support-based puncture.
------------------------------------------------------------------------

infixr 4 _orBool_

_orBool_ : Bool → Bool → Bool
false orBool b = b
true orBool b = true

kernel4Support : Kernel4 → Bool
kernel4Support
  (a ∷ᵥ
   b ∷ᵥ
   c ∷ᵥ
   d ∷ᵥ
   []ᵥ) =
  support a
  orBool support b
  orBool support c
  orBool support d

zeroKernel4HasNoSupport :
  kernel4Support zeroKernel4 ≡ false
zeroKernel4HasNoSupport = refl

PuncturedKernel4 : Set
PuncturedKernel4 =
  Σ Kernel4 (λ kernel → kernel4Support kernel ≡ true)

punctureKernel4 : Kernel4 → Maybe PuncturedKernel4
punctureKernel4 kernel with kernel4Support kernel
... | false = nothing
... | true = just (kernel , refl)

reopenPuncturedKernel4 :
  PuncturedKernel4 → Kernel4
reopenPuncturedKernel4 = proj₁

reopenPuncturedKernel4IsUnderlying :
  (state : PuncturedKernel4) →
  reopenPuncturedKernel4 state ≡ proj₁ state
reopenPuncturedKernel4IsUnderlying state = refl

punctureOriginIsNothing :
  punctureKernel4 zeroKernel4 ≡ nothing
punctureOriginIsNothing = refl

------------------------------------------------------------------------
-- 4. Arithmetic cross-reference only.
------------------------------------------------------------------------

fullKernel4ArithmeticCount : Nat
fullKernel4ArithmeticCount = Stencil.pow3 4

fullKernel4ArithmeticCountIs81 :
  fullKernel4ArithmeticCount ≡ 81
fullKernel4ArithmeticCountIs81 =
  Stencil.pow3FourIs81

puncturedKernel4ArithmeticTarget : Nat
puncturedKernel4ArithmeticTarget =
  Stencil.poleCoefficient

puncturedKernel4ArithmeticTargetIs80 :
  puncturedKernel4ArithmeticTarget ≡ 80
puncturedKernel4ArithmeticTargetIs80 = refl

fullCountIsPuncturedTargetPlusOrigin :
  fullKernel4ArithmeticCount
  ≡ puncturedKernel4ArithmeticTarget + 1
fullCountIsPuncturedTargetPlusOrigin =
  Stencil.eightyIsPuncturedThreePowerFour

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

record RiemannQuarticTriadicCodecKernelBridgeBoundary : Set where
  constructor riemann-quartic-triadic-codec-kernel-bridge-boundary
  field
    x6Kernel6ExactTwoSidedChart : Bool
    canonicalKernel4Reused : Bool
    kernel4OriginExplicit : Bool
    supportPunctureOperationConstructed : Bool
    arithmeticFullCount81Paid : Bool
    arithmeticPuncturedTarget80Paid : Bool
    concretePuncturedKernel4Cardinality80ProvedHere : Bool
    rhSemanticIdentityClaimed : Bool

canonicalRiemannQuarticTriadicCodecKernelBridgeBoundary :
  RiemannQuarticTriadicCodecKernelBridgeBoundary
canonicalRiemannQuarticTriadicCodecKernelBridgeBoundary =
  riemann-quartic-triadic-codec-kernel-bridge-boundary
    true true true true true true false false
