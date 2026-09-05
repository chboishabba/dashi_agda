{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Lithography.RayleighCriterionExact where

open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_)

-- Exact finite carrier for the ideal Rayleigh relation
--
--   CD = k₁ λ / NA
--
-- represented without division as
--
--   CD · NA = k₁ · λ.
--
-- The carrier is deliberately arithmetic only.  It does not assert that a
-- physical scanner, resist stack, mask, process window, or manufactured wafer
-- is completely described by the Rayleigh model.

record RayleighCoordinates : Set where
  constructor rayleighCoordinates
  field
    cd         : Nat
    k1         : Nat
    wavelength : Nat
    na         : Nat

open RayleighCoordinates public

RayleighLaw : RayleighCoordinates → Set
RayleighLaw x = cd x * na x ≡ k1 x * wavelength x

-- Constructive strict-gap witness over naturals.  This is useful for finite
-- cross-product comparisons without importing a larger ordered-field layer.
record StrictGap (a b : Nat) : Set where
  constructor strictGap
  field
    delta    : Nat
    equation : a + suc delta ≡ b

open StrictGap public

-- For positive denominators, a witness of this shape is the finite arithmetic
-- seam used later to justify a comparison of λ₁ / NA₁ and λ₂ / NA₂.
-- This file intentionally stores only the exact cross-product proposition;
-- the ordered-rational interpretation belongs to a later bridge.
RayleighProxyCrossGap : Nat → Nat → Nat → Nat → Set
RayleighProxyCrossGap λ₁ na₁ λ₂ na₂ =
  StrictGap (λ₁ * na₂) (λ₂ * na₁)
