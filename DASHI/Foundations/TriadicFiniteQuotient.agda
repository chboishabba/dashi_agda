module DASHI.Foundations.TriadicFiniteQuotient where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using
    ( Trit; neg; zer; pos
    ; Stream; tail
    ; TritPrefix; []; _∷_; take
    ; PrefixAgreement
    ; prefixAgreement→takeEquality
    )

------------------------------------------------------------------------
-- Exact finite carrier for Z / 3^n Z in balanced-ternary coordinates.
--
-- The carrier is represented canonically by the first n balanced trits.
-- This avoids choosing a non-canonical Nat representative while still
-- exposing a numeric representative and the exact reduction maps.

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

_+ⁿ_ : Nat → Nat → Nat
zero +ⁿ y = y
suc x +ⁿ y = suc (x +ⁿ y)

_*ⁿ_ : Nat → Nat → Nat
zero *ⁿ y = zero
suc x *ⁿ y = y +ⁿ (x *ⁿ y)

pow3 : Nat → Nat
pow3 zero = one
pow3 (suc n) = three *ⁿ pow3 n

Residue3Pow : Nat → Set
Residue3Pow = TritPrefix

tritResidueDigit : Trit → Nat
tritResidueDigit neg = two
tritResidueDigit zer = zero
tritResidueDigit pos = one

numericRepresentative : ∀ {n : Nat} → Residue3Pow n → Nat
numericRepresentative [] = zero
numericRepresentative (t ∷ ts) =
  tritResidueDigit t +ⁿ (three *ⁿ numericRepresentative ts)

projection : (n : Nat) → Stream → Residue3Pow n
projection = take

------------------------------------------------------------------------
-- Reduction modulo 3^n and the canonical zero-section lift.

reduce : ∀ {n : Nat} → Residue3Pow (suc n) → Residue3Pow n
reduce {zero} (t ∷ []) = []
reduce {suc n} (t ∷ ts) = t ∷ reduce ts

zeroLift : ∀ {n : Nat} → Residue3Pow n → Residue3Pow (suc n)
zeroLift [] = zer ∷ []
zeroLift (t ∷ ts) = t ∷ zeroLift ts

reduce-zeroLift :
  ∀ {n : Nat} (x : Residue3Pow n) →
  reduce (zeroLift x) ≡ x
reduce-zeroLift [] = refl
reduce-zeroLift (t ∷ ts) rewrite reduce-zeroLift ts = refl

reduce-projection :
  (n : Nat) →
  (d : Stream) →
  reduce (projection (suc n) d) ≡ projection n d
reduce-projection zero d = refl
reduce-projection (suc n) d
  rewrite reduce-projection n (tail d) = refl

------------------------------------------------------------------------
-- Cylinder equality and residue equality are the same finite information.

cylinderAgreement→residueEquality :
  ∀ {n : Nat} {x y : Stream} →
  PrefixAgreement n x y →
  projection n x ≡ projection n y
cylinderAgreement→residueEquality = prefixAgreement→takeEquality

SameResidueAtDepth : Nat → Stream → Stream → Set
SameResidueAtDepth = PrefixAgreement

sameResidueAtDepth→projectionEquality :
  ∀ {n : Nat} {x y : Stream} →
  SameResidueAtDepth n x y →
  projection n x ≡ projection n y
sameResidueAtDepth→projectionEquality =
  cylinderAgreement→residueEquality

------------------------------------------------------------------------
-- Inverse-limit carrier.

record TriadicInverseLimitPoint : Set where
  constructor triadic-limit-point
  field
    coordinate : (n : Nat) → Residue3Pow n
    compatible :
      (n : Nat) →
      reduce (coordinate (suc n)) ≡ coordinate n

open TriadicInverseLimitPoint public

streamToInverseLimit : Stream → TriadicInverseLimitPoint
streamToInverseLimit d =
  triadic-limit-point
    (λ n → projection n d)
    (λ n → reduce-projection n d)

------------------------------------------------------------------------
-- Compatible finite kernels induce an exact inverse-limit operator.

record CompatibleKernelFamily : Set₁ where
  field
    kernel :
      (n : Nat) →
      Residue3Pow n →
      Residue3Pow n

    reductionCommutes :
      (n : Nat) →
      (x : Residue3Pow (suc n)) →
      reduce (kernel (suc n) x)
      ≡ kernel n (reduce x)

open CompatibleKernelFamily public

applyCompatibleKernel :
  CompatibleKernelFamily →
  TriadicInverseLimitPoint →
  TriadicInverseLimitPoint
applyCompatibleKernel K x =
  triadic-limit-point
    (λ n → kernel K n (coordinate x n))
    (λ n →
      reductionCommutes K n (coordinate x (suc n)))

------------------------------------------------------------------------
-- Explicit claim boundary.

finiteQuotientStatement : String
finiteQuotientStatement =
  "Depth n is represented by the exact balanced-ternary carrier T^n, canonically modelling Z/3^nZ; reduction drops the highest retained trit and compatible kernels descend to the inverse limit."

numericBoundary : String
numericBoundary =
  "numericRepresentative supplies the ordinary residue digits neg->2, zer->0, pos->1; no theorem here promotes this finite presentation into a completed analytic p-adic field."
