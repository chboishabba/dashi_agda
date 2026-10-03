module DASHI.ComputerScience.TekumTriadicScaleExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc; _*_)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; +<+)
open import Data.Nat.Base using (_>_; z<s)
import Data.Nat.Properties as NatP
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Unnormalised.Base as ℚᵘ
  using (ℚᵘ; 0ℚᵘ; _≃_; _*_; _/_; _<_)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.ComputerScience.TekumExactTriadicSemanticsExact as Exact
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source

------------------------------------------------------------------------
-- Exact signed power-of-three scale 3^e on an integer exponent.
--
-- We work first in unnormalised rationals, where the negative branch is the
-- literal reciprocal 1 / 3^k, and transport to canonical ℚ only afterwards.
------------------------------------------------------------------------

integerSucc : ℤ → ℤ
integerSucc (+ n) = + (suc n)
integerSucc -[1+ zero ] = + zero
integerSucc -[1+ suc n ] = -[1+ n ]

rawThree : ℚᵘ
rawThree = (+ 3) ℚᵘ./ 1

rawTriadicScale : ℤ → ℚᵘ
rawTriadicScale (+ n) =
  let instance d = Exact.pow3NonZero zero
  in (+ (BT.pow3 n)) ℚᵘ./ 1
rawTriadicScale -[1+ n ] =
  let instance d = Exact.pow3NonZero (suc n)
  in (+ 1) ℚᵘ./ BT.pow3 (suc n)

triadicScale : ℤ → ℚ
triadicScale z = ℚ.fromℚᵘ (rawTriadicScale z)

canonicalThree : ℚ
canonicalThree = ℚ.fromℚᵘ rawThree

rawTriadicScalePositive :
  (z : ℤ) → 0ℚᵘ ℚᵘ.< rawTriadicScale z
rawTriadicScalePositive (+ n) =
  ℚᵘ.*<* (+<+ (NatP.>-nonZero⁻¹ (BT.pow3 n) {{Exact.pow3NonZero n}}))
rawTriadicScalePositive -[1+ n ] =
  ℚᵘ.*<* (+<+ z<s)

triadicScalePositive :
  (z : ℤ) → 0ℚ ℚ.< triadicScale z
triadicScalePositive z =
  ℚP.toℚᵘ-cancel-< transported
  where
  zeroEquivalent : ℚP.toℚᵘ 0ℚ ≃ 0ℚᵘ
  zeroEquivalent = ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ 0ℚᵘ)

  scaleEquivalent : ℚP.toℚᵘ (triadicScale z) ≃ rawTriadicScale z
  scaleEquivalent = ℚP.toℚᵘ-fromℚᵘ (rawTriadicScale z)

  leftTransport : ℚP.toℚᵘ 0ℚ ℚᵘ.< rawTriadicScale z
  leftTransport =
    ℚᵘP.<-respˡ-≃ zeroEquivalent (rawTriadicScalePositive z)

  transported :
    ℚP.toℚᵘ 0ℚ ℚᵘ.< ℚP.toℚᵘ (triadicScale z)
  transported =
    ℚᵘP.<-respʳ-≃ (ℚᵘP.≃-sym scaleEquivalent) leftTransport

------------------------------------------------------------------------
-- One integer step multiplies the scale by three.
------------------------------------------------------------------------

rawTriadicScaleSucc :
  (z : ℤ) →
  rawTriadicScale (integerSucc z)
  ≃ rawThree ℚᵘ.* rawTriadicScale z
rawTriadicScaleSucc (+ n) = ℚᵘ.*≡* refl
rawTriadicScaleSucc -[1+ zero ] = ℚᵘ.*≡* refl
rawTriadicScaleSucc -[1+ suc n ] = ℚᵘ.*≡* refl

triadicScaleSucc :
  (z : ℤ) →
  triadicScale (integerSucc z)
  ≡ canonicalThree ℚ.* triadicScale z
triadicScaleSucc z =
  ℚP.toℚᵘ-injective proof
  where
  leftToRaw :
    ℚP.toℚᵘ (triadicScale (integerSucc z))
    ≃ rawTriadicScale (integerSucc z)
  leftToRaw = ℚP.toℚᵘ-fromℚᵘ (rawTriadicScale (integerSucc z))

  threeToRaw : ℚP.toℚᵘ canonicalThree ≃ rawThree
  threeToRaw = ℚP.toℚᵘ-fromℚᵘ rawThree

  scaleToRaw : ℚP.toℚᵘ (triadicScale z) ≃ rawTriadicScale z
  scaleToRaw = ℚP.toℚᵘ-fromℚᵘ (rawTriadicScale z)

  rawProductToCanonicalFactors :
    rawThree ℚᵘ.* rawTriadicScale z
    ≃ ℚP.toℚᵘ canonicalThree ℚᵘ.* ℚP.toℚᵘ (triadicScale z)
  rawProductToCanonicalFactors =
    ℚᵘP.*-cong
      (ℚᵘP.≃-sym threeToRaw)
      (ℚᵘP.≃-sym scaleToRaw)

  factorsToCanonicalProduct :
    ℚP.toℚᵘ canonicalThree ℚᵘ.* ℚP.toℚᵘ (triadicScale z)
    ≃ ℚP.toℚᵘ (canonicalThree ℚ.* triadicScale z)
  factorsToCanonicalProduct =
    ℚᵘP.≃-sym (ℚP.toℚᵘ-homo-* canonicalThree (triadicScale z))

  proof :
    ℚP.toℚᵘ (triadicScale (integerSucc z))
    ≃ ℚP.toℚᵘ (canonicalThree ℚ.* triadicScale z)
  proof =
    ℚᵘP.≃-trans leftToRaw
      (ℚᵘP.≃-trans (rawTriadicScaleSucc z)
        (ℚᵘP.≃-trans rawProductToCanonicalFactors factorsToCanonicalProduct))

intCodeTriadicScale : Sem.IntCode → ℚ
intCodeTriadicScale code = triadicScale (Exact.intCodeToInteger code)

intCodeTriadicScaleCanonical :
  (z : ℤ) →
  intCodeTriadicScale (Source.integerToIntCode z) ≡ triadicScale z
intCodeTriadicScaleCanonical z =
  cong triadicScale (Source.integerToIntCodeRoundTrip z)
