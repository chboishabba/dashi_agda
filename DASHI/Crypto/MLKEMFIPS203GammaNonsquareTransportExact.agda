module DASHI.Crypto.MLKEMFIPS203GammaNonsquareTransportExact where

------------------------------------------------------------------------
-- FIPS 203 GAMMA NONSQUARE TRANSPORT
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- FIPS quadratic constants have the form
--
--   gamma_i = zeta^(2 * BitRev7(i) + 1)
--           = zeta * (zeta^BitRev7(i))^2.
--
-- Hence it is wasteful to prove 128 unrelated nonsquare facts.  Over a
-- field-like commutative ring, multiplication of a nonsquare by a nonzero
-- square preserves nonsquareness.  Therefore all 128 gamma_i reduce to:
--
--   (1) zeta is nonsquare;
--   (2) the square-twist factor zeta^BitRev7(i) is nonzero;
--   (3) the source-faithful odd-power factorisation above.
--
-- This is the symmetry reduction suggested by the SSP lane work: the family of
-- 128 quadratic factors is one nonsquare orbit under multiplication by squares,
-- not 128 independent arithmetic obligations.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (nothing)
import Tactic.RingSolver.Core.AlmostCommutativeRing as RingCore
import Tactic.RingSolver.NonReflective as RingSolver

import DASHI.Crypto.MLKEMBaseCaseNormInverseBridgeExact as NormBridge

module _ {c ℓ : Level}
  (R : CommutativeRing c ℓ)
  (inverseSupplier : NormBridge.NonzeroInverseSupplier R)
  where

  open CommutativeRing R
    renaming
      ( Carrier to F
      ; _*_ to _⊗_
      ; 0# to 0F
      ; 1# to 1F
      )

  private
    solverRing : RingCore.AlmostCommutativeRing c ℓ
    solverRing = RingCore.fromCommutativeRing R (λ _ → nothing)

    module S = RingSolver solverRing

    inverseOf : F → F
    inverseOf = NormBridge.inverseOf inverseSupplier

    inverseLaw :
      (x : F) →
      (x ≡ 0F → ⊥) →
      inverseOf x ⊗ x ≡ 1F
    inverseLaw = NormBridge.inverseLaw inverseSupplier

  Nonsquare : F → Set c
  Nonsquare zeta = (x : F) → x ⊗ x ≡ zeta → ⊥

  squareTwist : F → F → F
  squareTwist zeta r = zeta ⊗ (r ⊗ r)

  quotientSquareFromSquareTwist :
    (zeta r x : F) →
    (r ≡ 0F → ⊥) →
    x ⊗ x ≡ squareTwist zeta r →
    (x ⊗ inverseOf r) ⊗ (x ⊗ inverseOf r) ≡ zeta
  quotientSquareFromSquareTwist zeta r x rNonzero squareWitness =
    S.solve 5
      (λ zeta r x inv one →
        (x S.⊗ inv) S.⊗ (x S.⊗ inv) S.⊜ zeta)
      squareWitness
      (inverseLaw r rNonzero)
      zeta r x (inverseOf r) 1F

  nonsquareTimesNonzeroSquare :
    (zeta r : F) →
    Nonsquare zeta →
    (r ≡ 0F → ⊥) →
    Nonsquare (squareTwist zeta r)
  nonsquareTimesNonzeroSquare zeta r zetaNonsquare rNonzero x squareWitness =
    zetaNonsquare
      (x ⊗ inverseOf r)
      (quotientSquareFromSquareTwist zeta r x rNonzero squareWitness)

  record GammaSquareOrbitCertificate (zeta gamma : F) : Set c where
    constructor gamma-square-orbit-certificate
    field
      twistRoot : F
      twistRootNonzero : twistRoot ≡ 0F → ⊥
      gammaFactorisation : gamma ≡ squareTwist zeta twistRoot

  open GammaSquareOrbitCertificate public

  orbitCertificateTransportsNonsquare :
    (zeta gamma : F) →
    Nonsquare zeta →
    GammaSquareOrbitCertificate zeta gamma →
    Nonsquare gamma
  orbitCertificateTransportsNonsquare zeta gamma zetaNonsquare certificate x gammaSquare =
    nonsquareTimesNonzeroSquare
      zeta
      (twistRoot certificate)
      zetaNonsquare
      (twistRootNonzero certificate)
      x
      (S.solve 4
        (λ gamma zeta r square → square S.⊜ zeta S.⊗ (r S.⊗ r))
        gammaSquare
        (gammaFactorisation certificate)
        gamma zeta (twistRoot certificate)
        (x S.⊗ x))

------------------------------------------------------------------------
-- SOURCE-SPECIFIC REMAINDER
--
-- For actual FIPS 203 instantiate:
--
--   zeta = 17 mod 3329,
--   gamma_i = zeta^(2*BitRev7(i)+1),
--   twistRoot_i = zeta^BitRev7(i).
--
-- Then the 128 local nonsquare obligations collapse to one arithmetic theorem
-- that zeta=17 is nonsquare, plus routine nonzeroness/factorisation of powers.
------------------------------------------------------------------------
