module DASHI.Moonshine.JInvariantEisensteinBishopSetoidFiniteQSeriesExact where

------------------------------------------------------------------------
-- EISENSTEIN FINITE q-SERIES ON THE VENDORED BISHOP SETOID COMPLEX CARRIER
--
-- This is the carrier-correct route-B sibling of
-- JInvariantEisensteinFiniteQSeriesExact.
--
-- It reuses exactly the same executable divisor-power kernel and the same
-- recurrence:
--
--   q(tau)   = exp(2*pi*i*tau)
--   E4_0     = 1
--   E4_(n+1) = E4_n + 240 sigma_3(n+1) q^(n+1)
--   E6_0     = 1
--   E6_(n+1) = E6_n - 504 sigma_5(n+1) q^(n+1)
--
-- but the scalar/complex carrier is now the actual vendored Bishop setoid
-- package, not the legacy propositional-equality ConstructedOrderedCompleteReal.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)

import Real as BishopReal
import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Legacy

------------------------------------------------------------------------
-- The divisor kernel is arithmetic-only and can be reused without a carrier
-- identification.
------------------------------------------------------------------------

DivisorPowerKernel : Set
DivisorPowerKernel = Legacy.DivisorPowerKernel

canonicalDivisorPowerKernel : DivisorPowerKernel
canonicalDivisorPowerKernel = Legacy.canonicalDivisorPowerKernel

sigma3 : DivisorPowerKernel → Nat → Nat
sigma3 = Legacy.sigma3

sigma5 : DivisorPowerKernel → Nat → Nat
sigma5 = Legacy.sigma5

------------------------------------------------------------------------
-- Literal q and finite recurrences.
------------------------------------------------------------------------

qOf :
  C.BishopSetoidComplexTranscendentals →
  C.BishopComplex →
  C.BishopComplex
qOf T tau =
  C.expC T
    (C._*C_
      (C.scaleNatC 2
        (C._*C_
          C.imaginaryUnit
          (C.piC T)))
      tau)

e4Truncated :
  C.BishopSetoidComplexTranscendentals →
  DivisorPowerKernel →
  Nat →
  C.BishopComplex →
  C.BishopComplex
e4Truncated T kernel zero tau = C.oneC
e4Truncated T kernel (suc n) tau =
  C._+C_
    (e4Truncated T kernel n tau)
    (C.scaleNatC
      (240 * sigma3 kernel (suc n))
      (C.powC (qOf T tau) (suc n)))

e6Truncated :
  C.BishopSetoidComplexTranscendentals →
  DivisorPowerKernel →
  Nat →
  C.BishopComplex →
  C.BishopComplex
e6Truncated T kernel zero tau = C.oneC
e6Truncated T kernel (suc n) tau =
  C._-C_
    (e6Truncated T kernel n tau)
    (C.scaleNatC
      (504 * sigma5 kernel (suc n))
      (C.powC (qOf T tau) (suc n)))

squareC : C.BishopComplex → C.BishopComplex
squareC z = C._*C_ z z

cubeC : C.BishopComplex → C.BishopComplex
cubeC z = C._*C_ (squareC z) z

discriminantNumeratorTruncated :
  C.BishopSetoidComplexTranscendentals →
  DivisorPowerKernel →
  Nat →
  C.BishopComplex →
  C.BishopComplex
discriminantNumeratorTruncated T kernel terms tau =
  C._-C_
    (cubeC (e4Truncated T kernel terms tau))
    (squareC (e6Truncated T kernel terms tau))

------------------------------------------------------------------------
-- Normalized finite Delta on the actual Bishop carrier.
------------------------------------------------------------------------

oneOver1728Rational : ℚᵘ
oneOver1728Rational = + 1 / 1728

oneOver1728Bishop : BishopReal.ℝ
oneOver1728Bishop =
  BishopReal._⋆ oneOver1728Rational

oneOver1728Complex : C.BishopComplex
oneOver1728Complex =
  C.complex oneOver1728Bishop BishopReal.0ℝ

normalizedDeltaTruncated :
  C.BishopSetoidComplexTranscendentals →
  DivisorPowerKernel →
  Nat →
  C.BishopComplex →
  C.BishopComplex
normalizedDeltaTruncated T kernel terms tau =
  C._*C_
    oneOver1728Complex
    (discriminantNumeratorTruncated
      T kernel terms tau)

------------------------------------------------------------------------
-- The actual finite objects respect Bishop setoid equality.
------------------------------------------------------------------------

qOfCongruent :
  (T : C.BishopSetoidComplexTranscendentals) →
  ∀ {left right} →
  C._≈C_ left right →
  C._≈C_ (qOf T left) (qOf T right)
qOfCongruent T equivalent =
  C.expCongruent T
    (C.mulCongruent
      (C.≈C-refl
        (C.scaleNatC 2
          (C._*C_ C.imaginaryUnit (C.piC T))))
      equivalent)

e4TruncatedCongruent :
  (T : C.BishopSetoidComplexTranscendentals) →
  (kernel : DivisorPowerKernel) →
  (terms : Nat) →
  ∀ {left right} →
  C._≈C_ left right →
  C._≈C_
    (e4Truncated T kernel terms left)
    (e4Truncated T kernel terms right)
e4TruncatedCongruent T kernel zero equivalent =
  C.≈C-refl C.oneC
e4TruncatedCongruent T kernel (suc n) equivalent =
  C.addCongruent
    (e4TruncatedCongruent T kernel n equivalent)
    (C.scaleNatCongruent
      (240 * sigma3 kernel (suc n))
      (C.powCongruent
        (suc n)
        (qOfCongruent T equivalent)))

e6TruncatedCongruent :
  (T : C.BishopSetoidComplexTranscendentals) →
  (kernel : DivisorPowerKernel) →
  (terms : Nat) →
  ∀ {left right} →
  C._≈C_ left right →
  C._≈C_
    (e6Truncated T kernel terms left)
    (e6Truncated T kernel terms right)
e6TruncatedCongruent T kernel zero equivalent =
  C.≈C-refl C.oneC
e6TruncatedCongruent T kernel (suc n) equivalent =
  C.subCongruent
    (e6TruncatedCongruent T kernel n equivalent)
    (C.scaleNatCongruent
      (504 * sigma5 kernel (suc n))
      (C.powCongruent
        (suc n)
        (qOfCongruent T equivalent)))

squareCongruent :
  ∀ {left right} →
  C._≈C_ left right →
  C._≈C_ (squareC left) (squareC right)
squareCongruent equivalent =
  C.mulCongruent equivalent equivalent

cubeCongruent :
  ∀ {left right} →
  C._≈C_ left right →
  C._≈C_ (cubeC left) (cubeC right)
cubeCongruent equivalent =
  C.mulCongruent
    (squareCongruent equivalent)
    equivalent

discriminantNumeratorTruncatedCongruent :
  (T : C.BishopSetoidComplexTranscendentals) →
  (kernel : DivisorPowerKernel) →
  (terms : Nat) →
  ∀ {left right} →
  C._≈C_ left right →
  C._≈C_
    (discriminantNumeratorTruncated T kernel terms left)
    (discriminantNumeratorTruncated T kernel terms right)
discriminantNumeratorTruncatedCongruent T kernel terms equivalent =
  C.subCongruent
    (cubeCongruent
      (e4TruncatedCongruent T kernel terms equivalent))
    (squareCongruent
      (e6TruncatedCongruent T kernel terms equivalent))

normalizedDeltaTruncatedCongruent :
  (T : C.BishopSetoidComplexTranscendentals) →
  (kernel : DivisorPowerKernel) →
  (terms : Nat) →
  ∀ {left right} →
  C._≈C_ left right →
  C._≈C_
    (normalizedDeltaTruncated T kernel terms left)
    (normalizedDeltaTruncated T kernel terms right)
normalizedDeltaTruncatedCongruent T kernel terms equivalent =
  C.mulCongruent
    (C.≈C-refl oneOver1728Complex)
    (discriminantNumeratorTruncatedCongruent
      T kernel terms equivalent)

------------------------------------------------------------------------
-- Exact recurrence receipt.
------------------------------------------------------------------------

record BishopSetoidEisensteinFiniteBoundary : Set where
  constructor bishop-setoid-eisenstein-finite-boundary
  field
    canonicalDivisorKernelReused : Bool
    literalQFormulaOwned : Bool
    literalE4RecurrenceOwned : Bool
    literalE6RecurrenceOwned : Bool
    finiteDiscriminantNumeratorOwned : Bool
    finiteNormalizedDeltaOwned : Bool

    qSetoidCongruenceOwned : Bool
    e4SetoidCongruenceOwned : Bool
    e6SetoidCongruenceOwned : Bool
    discriminantSetoidCongruenceOwned : Bool
    normalizedDeltaSetoidCongruenceOwned : Bool

    legacyPropositionalRealQuotientUsed : Bool
    bishopPiIdentifiedWithClassicalPi : Bool

canonicalBishopSetoidEisensteinFiniteBoundary :
  BishopSetoidEisensteinFiniteBoundary
canonicalBishopSetoidEisensteinFiniteBoundary =
  bishop-setoid-eisenstein-finite-boundary
    true true true true true true
    true true true true true
    false false
