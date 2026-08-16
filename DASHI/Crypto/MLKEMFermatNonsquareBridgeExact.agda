module DASHI.Crypto.MLKEMFermatNonsquareBridgeExact where

------------------------------------------------------------------------
-- GENERIC FERMAT / EULER NONSQUARE BRIDGE
--
-- Mathematical source / provenance:
-- Leonhard Euler,
-- "Theoremata circa divisores numerorum in hac forma paa ± qbb contentorum",
-- Novi Commentarii Academiae Scientiarum Petropolitanae 14 (1770), 151--181.
-- Historical source; no DOI assigned.
--
-- Modern finite-field use here is elementary Euler-criterion algebra.  The
-- cryptographic instantiation is NIST FIPS 203, DOI: 10.6028/NIST.FIPS.203.
--
-- PURPOSE
-- -------
-- Round 17 has already computed for the actual ML-KEM modulus q=3329 that
--
--   17^1664 = -1 mod 3329.
--
-- Rather than proving 128 independent gamma nonsquare facts, the existing
-- square-orbit theorem reduces everything to `17` being a nonsquare.  This file
-- isolates the remaining standard field argument in reusable form:
--
--   if every nonzero x obeys x^(2h)=1,
--   and zeta^h=-1 != 1,
--   then zeta cannot be a square.
--
-- The proof includes the exponent algebra
--
--   (x*x)^h = x^(h+h)
--
-- over an arbitrary commutative ring.  A concrete prime-field instance only
-- has to provide the Fermat law and the already-computed half-power endpoint.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (nothing)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
import Tactic.RingSolver.Core.AlmostCommutativeRing as RingCore
import Tactic.RingSolver.NonReflective as RingSolver

module _ {c ℓ : Level} (R : CommutativeRing c ℓ) where

  open CommutativeRing R
    renaming
      ( Carrier to F
      ; _*_ to _⊗_
      ; -_ to neg
      ; 0# to 0F
      ; 1# to 1F
      )

  private
    solverRing : RingCore.AlmostCommutativeRing c ℓ
    solverRing = RingCore.fromCommutativeRing R (λ _ → nothing)

    module S = RingSolver solverRing

  pow : F → Nat → F
  pow x zero = 1F
  pow x (suc exponent) = x ⊗ pow x exponent

  powCong :
    (x y : F) →
    x ≡ y →
    (n : Nat) →
    pow x n ≡ pow y n
  powCong x y refl n = refl

  powAdd :
    (x : F) →
    (m n : Nat) →
    pow x (m + n) ≡ pow x m ⊗ pow x n
  powAdd x zero n =
    S.solve 1
      (λ y → y S.⊜ (S.con 1 S.⊗ y))
      refl
      (pow x n)
  powAdd x (suc m) n =
    S.solve 3
      (λ x leftM rightN →
        x S.⊗ (leftM S.⊗ rightN)
          S.⊜
        (x S.⊗ leftM) S.⊗ rightN)
      (powAdd x m n)
      x (pow x m) (pow x n)

  powProduct :
    (x y : F) →
    (n : Nat) →
    pow (x ⊗ y) n ≡ pow x n ⊗ pow y n
  powProduct x y zero =
    S.solve 0
      (λ → S.con 1 S.⊜ (S.con 1 S.⊗ S.con 1))
      refl
  powProduct x y (suc n) =
    S.solve 4
      (λ x y px py →
        (x S.⊗ y) S.⊗ (px S.⊗ py)
          S.⊜
        (x S.⊗ px) S.⊗ (y S.⊗ py))
      (powProduct x y n)
      x y (pow x n) (pow y n)

  squareHalfPowerIsDoublePower :
    (x : F) →
    (halfExponent : Nat) →
    pow (x ⊗ x) halfExponent ≡
    pow x (halfExponent + halfExponent)
  squareHalfPowerIsDoublePower x halfExponent =
    trans
      (powProduct x x halfExponent)
      (sym (powAdd x halfExponent halfExponent))

  Nonsquare : F → Set c
  Nonsquare zeta = (x : F) → x ⊗ x ≡ zeta → ⊥

  record FermatHalfPowerCertificate
      (halfExponent : Nat)
      (zeta : F) : Set c where
    constructor fermat-half-power-certificate
    field
      zetaNonzero : zeta ≡ 0F → ⊥
      oneNotMinusOne : 1F ≡ neg 1F → ⊥
      halfPowerIsMinusOne : pow zeta halfExponent ≡ neg 1F
      fermatAtDoubleExponent :
        (x : F) →
        (x ≡ 0F → ⊥) →
        pow x (halfExponent + halfExponent) ≡ 1F

  open FermatHalfPowerCertificate public

  squareRootOfNonzeroIsNonzero :
    (zeta x : F) →
    (zeta ≡ 0F → ⊥) →
    x ⊗ x ≡ zeta →
    (x ≡ 0F → ⊥)
  squareRootOfNonzeroIsNonzero zeta x zetaNonzero squareWitness xZero =
    zetaNonzero zetaZero
    where
    squareAtZero : 0F ⊗ 0F ≡ zeta
    squareAtZero =
      subst
        (λ y → y ⊗ y ≡ zeta)
        xZero
        squareWitness

    zetaZero : zeta ≡ 0F
    zetaZero =
      S.solve 1
        (λ z → z S.⊜ S.con 0)
        squareAtZero
        zeta

  fermatHalfPowerRefutesSquare :
    (halfExponent : Nat) →
    (zeta : F) →
    FermatHalfPowerCertificate halfExponent zeta →
    Nonsquare zeta
  fermatHalfPowerRefutesSquare halfExponent zeta certificate x squareWitness =
    oneNotMinusOne certificate contradiction
    where
    xNonzero : x ≡ 0F → ⊥
    xNonzero =
      squareRootOfNonzeroIsNonzero
        zeta x (zetaNonzero certificate) squareWitness

    squarePower :
      pow zeta halfExponent ≡
      pow x (halfExponent + halfExponent)
    squarePower =
      trans
        (sym (powCong (x ⊗ x) zeta squareWitness halfExponent))
        (squareHalfPowerIsDoublePower x halfExponent)

    minusOneIsOne : neg 1F ≡ 1F
    minusOneIsOne =
      trans
        (sym (halfPowerIsMinusOne certificate))
        (trans
          squarePower
          (fermatAtDoubleExponent certificate x xNonzero))

    contradiction : 1F ≡ neg 1F
    contradiction = sym minusOneIsOne

------------------------------------------------------------------------
-- FIPS-203 COMPLETION TARGET
--
-- For q=3329 set h=1664. `MLKEMFIPS203F3329ArithmeticExact` already pins
--
--   17^1664 = 3328 = -1 mod 3329.
--
-- The only substantive producer still missing for this certificate is the
-- standard prime-field Fermat law x^3328=1 for nonzero x, plus the canonical
-- identification of residue 3328 with -1 and 17 with the F_3329 element.
-- Once supplied, `fermatHalfPowerRefutesSquare` proves `Nonsquare 17`, and
-- `MLKEMFIPS203GammaNonsquareTransportExact` transports that one fact to all
-- 128 FIPS quadratic constants through their square-orbit factorisation.
------------------------------------------------------------------------
