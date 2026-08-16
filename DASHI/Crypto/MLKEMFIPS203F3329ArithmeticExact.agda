module DASHI.Crypto.MLKEMFIPS203F3329ArithmeticExact where

------------------------------------------------------------------------
-- FIPS 203: CONCRETE F_3329 ARITHMETIC PRODUCER
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- PURPOSE
-- -------
-- Pin the concrete modular arithmetic shared by the compact pair-(0,3)
-- injectivity proof and the gamma nonsquare-orbit reduction.  These are closed
-- computations over the canonical residue representatives; they are not
-- replacement axioms for field theory.
--
-- In particular we compute:
--
--   gamma_0 = 17,
--   gamma_3 = 568,
--   17^4 = 568^4 = 296 mod 3329,
--   17 + 568 = 585,
--   17 * 568 = 2998 = -331 mod 3329,
--   568 - 17 = 551,
--   551 * 3184 = 1 mod 3329,
--   2 * 1665 = 1 mod 3329,
--   17^128 = -1 mod 3329,
--   17^256 = 1 mod 3329,
--   17^1664 = -1 mod 3329.
--
-- The inverse facts close the concrete arithmetic needed for zero reflection
-- once the canonical prime-field carrier is connected to these Nat residues.
-- The half-power fact is the exact Euler-criterion endpoint for proving that 17
-- is a nonsquare; the remaining semantic step is the finite-field/Fermat
-- theorem, not another 128-gamma computation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import DASHI.Foundations.Base369Nat using (_%_)

q : Nat
q = 3329

zeta : Nat
zeta = 17

gamma0 : Nat
gamma0 = 17

gamma3 : Nat
gamma3 = 568

modPow : Nat → Nat → Nat
modPow base zero = 1
modPow base (suc exponent) = (base * modPow base exponent) % q

gamma0Is17 : gamma0 ≡ 17
gamma0Is17 = refl

gamma3Is568 : gamma3 ≡ 568
gamma3Is568 = refl

gamma0FourthPower : modPow gamma0 4 ≡ 296
gamma0FourthPower = refl

gamma3FourthPower : modPow gamma3 4 ≡ 296
gamma3FourthPower = refl

pair03Sum : (gamma0 + gamma3) % q ≡ 585
pair03Sum = refl

pair03Product : (gamma0 * gamma3) % q ≡ 2998
pair03Product = refl

minus331Representative : (331 + 2998) % q ≡ 0
minus331Representative = refl

minus585Representative : (585 + 2744) % q ≡ 0
minus585Representative = refl

pair03Difference : (568 + 3329 - 17) % q ≡ 551
pair03Difference = refl

pair03DifferenceInverse : (551 * 3184) % q ≡ 1
pair03DifferenceInverse = refl

twoInverse : (2 * 1665) % q ≡ 1
twoInverse = refl

zetaPower128 : modPow zeta 128 ≡ 3328
zetaPower128 = refl

zetaPower256 : modPow zeta 256 ≡ 1
zetaPower256 = refl

zetaEulerHalfPower : modPow zeta 1664 ≡ 3328
zetaEulerHalfPower = refl

minusOneIs3328 : (1 + 3328) % q ≡ 0
minusOneIs3328 = refl

------------------------------------------------------------------------
-- Compact source-arithmetic package consumed by later bridges.
------------------------------------------------------------------------

record Pair03ArithmeticFacts : Set where
  constructor pair03-arithmetic-facts
  field
    fourth0 fourth3 : Nat
    sum03 product03 difference03 differenceInverse : Nat
    fourth0Is296 : fourth0 ≡ 296
    fourth3Is296 : fourth3 ≡ 296
    sum03Is585 : sum03 ≡ 585
    product03Is2998 : product03 ≡ 2998
    difference03Is551 : difference03 ≡ 551
    differenceInverseIs3184 : differenceInverse ≡ 3184

open Pair03ArithmeticFacts public

canonicalPair03ArithmeticFacts : Pair03ArithmeticFacts
canonicalPair03ArithmeticFacts =
  pair03-arithmetic-facts
    (modPow gamma0 4)
    (modPow gamma3 4)
    ((gamma0 + gamma3) % q)
    ((gamma0 * gamma3) % q)
    ((568 + 3329 - 17) % q)
    3184
    refl refl refl refl refl refl

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- This file deliberately distinguishes closed residue arithmetic from the
-- semantic prime-field theorem.  To finish the `Nonsquare 17` producer used by
-- `MLKEMFIPS203GammaNonsquareTransportExact`, connect these computations to the
-- canonical F_3329 field and use Fermat/Euler: a square y^2 would satisfy
-- (y^2)^1664 = y^3328 = 1, contradicting 17^1664 = -1.
--
-- Thus the old "prove 128 independent gamma nonsquare facts" obligation is
-- gone; the remaining theorem-sized leaf is one standard prime-field bridge.
------------------------------------------------------------------------
