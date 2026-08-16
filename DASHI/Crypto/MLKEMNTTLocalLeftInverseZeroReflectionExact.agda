module DASHI.Crypto.MLKEMNTTLocalLeftInverseZeroReflectionExact where

------------------------------------------------------------------------
-- ML-KEM NTT: LOCAL LEFT-INVERSE -> ZERO-REFLECTION
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- PURPOSE
--
-- The support-budget theorem only needs the local implication
--
--     map x = 0  ->  x = 0.
--
-- Rather than taking that implication as a primitive certificate, this module
-- derives it from the standard linear-algebra witness we ultimately want for
-- each regular FIPS local matrix: an explicit left inverse.
--
-- The theorem is carrier-generic and does not assume commutativity, a field,
-- or matrix syntax.  The only zero-specific compatibility needed is that the
-- left inverse maps the output zero to the input zero.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong; trans; sym)

open import DASHI.Crypto.MLKEMNTTLocalMatrixOutcomeClassifierExact using
  ( ZeroReflectingMap
  ; zero-reflecting-map
  ; LocalMatrixStatus
  ; regularStatusFromZeroReflectingMap
  )

record LeftInverseAtZero (X Y : Set) : Set where
  constructor left-inverse-at-zero
  field
    zeroX : X
    zeroY : Y
    forward : X → Y
    backward : Y → X
    leftInverse : (x : X) → backward (forward x) ≡ x
    backwardZero : backward zeroY ≡ zeroX

open LeftInverseAtZero public

leftInverseReflectsZero :
  ∀ {X Y : Set} →
  (witness : LeftInverseAtZero X Y) →
  (x : X) →
  forward witness x ≡ zeroY witness →
  x ≡ zeroX witness
leftInverseReflectsZero witness x forwardZero =
  trans
    (sym (leftInverse witness x))
    (trans
      (cong (backward witness) forwardZero)
      (backwardZero witness))

leftInverseToZeroReflectingMap :
  ∀ {X Y : Set} →
  LeftInverseAtZero X Y →
  ZeroReflectingMap X Y
leftInverseToZeroReflectingMap witness =
  zero-reflecting-map
    (zeroX witness)
    (zeroY witness)
    (forward witness)
    (leftInverseReflectsZero witness)

leftInverseToRegularStatus :
  ∀ {X Y : Set} →
  (witness : LeftInverseAtZero X Y) →
  LocalMatrixStatus
    (zeroX witness)
    (zeroY witness)
    (forward witness)
leftInverseToRegularStatus witness =
  regularStatusFromZeroReflectingMap
    (leftInverseToZeroReflectingMap witness)

------------------------------------------------------------------------
-- Equality sanity theorem: a left-invertible map is injective.  This is not
-- needed by the support budget, but records the familiar stronger fact and
-- gives the FIPS matrix layer the standard theorem surface it expects.
------------------------------------------------------------------------

leftInverseInjective :
  ∀ {X Y : Set} →
  (witness : LeftInverseAtZero X Y) →
  (x y : X) →
  forward witness x ≡ forward witness y →
  x ≡ y
leftInverseInjective witness x y forwardEqual =
  trans
    (sym (leftInverse witness x))
    (trans
      (cong (backward witness) forwardEqual)
      (leftInverse witness y))

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- The remaining FIPS-specific work is algebraic, not logical:
--
--   1. for a nonzero BaseCase multiplier, construct the explicit inverse in
--      F_q[u]/(u^2-gamma_i) using the norm
--          a0^2 - gamma_i a1^2;
--   2. for a full local k x k module matrix, provide an inverse whenever its
--      determinant/rank certificate says regular;
--   3. feed the resulting LeftInverseAtZero witness into the classifier.
--
-- No claim that an actual FIPS local matrix is invertible is made here.
------------------------------------------------------------------------
