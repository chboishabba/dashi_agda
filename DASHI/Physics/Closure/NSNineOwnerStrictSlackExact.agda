module DASHI.Physics.Closure.NSNineOwnerStrictSlackExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Xiaoyutao Luo,
-- "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization", Journal of Mathematical Fluid Mechanics 21 (2019), 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin,
-- "Fourier Analysis and Nonlinear Partial Differential Equations",
-- Grundlehren der mathematischen Wissenschaften 343, Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- State and prove the exact nine-owner absorption arithmetic with explicit
-- robustness slack
--
--   Delta_NS = 1 - sum_i eta_i > 0.
--
-- The theorem does not manufacture any owner estimate.  It consumes nine
-- concrete inequalities on the same dissipation object and proves that the
-- total owner contribution plus Delta_NS times dissipation is at most the
-- full dissipation.  This keeps cutoff/approximation losses visible instead
-- of accepting a fragile equality at total viscosity charge one.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

sumNine : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
sumNine a b c d e f g h i =
  a + b + c + d + e + f + g + h + i

record NineOwnerViscosityPacket : Set where
  field
    dissipation : ℚ

    lowHighOwner highLowOwner highHighGoodOwner highHighBadOwner : ℚ
    commutatorOwner tailOwner timeCutoffOwner pressureOwner
      transportOwner : ℚ

    lowHighCoefficient highLowCoefficient highHighGoodCoefficient
      highHighBadCoefficient commutatorCoefficient tailCoefficient
      timeCutoffCoefficient pressureCoefficient transportCoefficient : ℚ

    lowHighUpper :
      lowHighOwner ≤ lowHighCoefficient * dissipation
    highLowUpper :
      highLowOwner ≤ highLowCoefficient * dissipation
    highHighGoodUpper :
      highHighGoodOwner ≤ highHighGoodCoefficient * dissipation
    highHighBadUpper :
      highHighBadOwner ≤ highHighBadCoefficient * dissipation
    commutatorUpper :
      commutatorOwner ≤ commutatorCoefficient * dissipation
    tailUpper :
      tailOwner ≤ tailCoefficient * dissipation
    timeCutoffUpper :
      timeCutoffOwner ≤ timeCutoffCoefficient * dissipation
    pressureUpper :
      pressureOwner ≤ pressureCoefficient * dissipation
    transportUpper :
      transportOwner ≤ transportCoefficient * dissipation

    strictSlackPositive :
      0ℚ < 1ℚ - sumNine
        lowHighCoefficient highLowCoefficient
        highHighGoodCoefficient highHighBadCoefficient
        commutatorCoefficient tailCoefficient timeCutoffCoefficient
        pressureCoefficient transportCoefficient
open NineOwnerViscosityPacket public

ownerTotal : NineOwnerViscosityPacket → ℚ
ownerTotal packet =
  sumNine
    (lowHighOwner packet) (highLowOwner packet)
    (highHighGoodOwner packet) (highHighBadOwner packet)
    (commutatorOwner packet) (tailOwner packet)
    (timeCutoffOwner packet) (pressureOwner packet)
    (transportOwner packet)

coefficientTotal : NineOwnerViscosityPacket → ℚ
coefficientTotal packet =
  sumNine
    (lowHighCoefficient packet) (highLowCoefficient packet)
    (highHighGoodCoefficient packet) (highHighBadCoefficient packet)
    (commutatorCoefficient packet) (tailCoefficient packet)
    (timeCutoffCoefficient packet) (pressureCoefficient packet)
    (transportCoefficient packet)

viscositySlack : NineOwnerViscosityPacket → ℚ
viscositySlack packet = 1ℚ - coefficientTotal packet

viscositySlackPositive :
  ∀ packet → 0ℚ < viscositySlack packet
viscositySlackPositive packet = strictSlackPositive packet

ownerTotalBelowCoefficientTotal :
  ∀ packet →
  ownerTotal packet ≤ coefficientTotal packet * dissipation packet
ownerTotalBelowCoefficientTotal packet =
  let
    first = ℚP.+-mono-≤
      (lowHighUpper packet) (highLowUpper packet)
    second = ℚP.+-mono-≤
      (highHighGoodUpper packet) (highHighBadUpper packet)
    third = ℚP.+-mono-≤
      (commutatorUpper packet) (tailUpper packet)
    fourth = ℚP.+-mono-≤
      (timeCutoffUpper packet) (pressureUpper packet)
    firstFour = ℚP.+-mono-≤ first second
    secondFour = ℚP.+-mono-≤ third fourth
    firstEight = ℚP.+-mono-≤ firstFour secondFour
    allNine = ℚP.+-mono-≤ firstEight (transportUpper packet)
  in
  subst
    (λ upper → ownerTotal packet ≤ upper)
    (ℚRing.solve-∀
      (lowHighCoefficient packet) (highLowCoefficient packet)
      (highHighGoodCoefficient packet) (highHighBadCoefficient packet)
      (commutatorCoefficient packet) (tailCoefficient packet)
      (timeCutoffCoefficient packet) (pressureCoefficient packet)
      (transportCoefficient packet) (dissipation packet))
    allNine

coefficientTotalPlusSlackExact :
  ∀ packet → coefficientTotal packet + viscositySlack packet ≡ 1ℚ
coefficientTotalPlusSlackExact packet =
  ℚRing.solve-∀ (coefficientTotal packet)

nineOwnerAbsorptionWithSlack :
  ∀ packet →
  ownerTotal packet + viscositySlack packet * dissipation packet
  ≤ dissipation packet
nineOwnerAbsorptionWithSlack packet =
  let
    summed = ℚP.+-mono-≤
      (ownerTotalBelowCoefficientTotal packet)
      (ℚP.≤-refl {x = viscositySlack packet * dissipation packet})
    upperExact :
      coefficientTotal packet * dissipation packet
        + viscositySlack packet * dissipation packet
      ≡ dissipation packet
    upperExact =
      trans
        (ℚRing.solve-∀
          (coefficientTotal packet)
          (viscositySlack packet)
          (dissipation packet))
        (trans
          (cong
            (λ total → total * dissipation packet)
            (coefficientTotalPlusSlackExact packet))
          (ℚRing.solve-∀ (dissipation packet)))
  in
  subst
    (λ upper →
      ownerTotal packet + viscositySlack packet * dissipation packet
      ≤ upper)
    upperExact
    summed
