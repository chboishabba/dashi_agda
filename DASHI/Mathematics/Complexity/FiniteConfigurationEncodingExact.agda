module DASHI.Mathematics.Complexity.FiniteConfigurationEncodingExact where

------------------------------------------------------------------------
-- FINITE CONFIGURATION CODEC FOR COOK--LEVIN
--
-- GenericFiniteRunTableauExact intentionally allows arbitrary Configuration :
-- Set.  Boolean tableau clauses need more: each configuration must have a
-- finite-width Boolean representation with a decoder and an explicit width
-- envelope controlled by input length/time.
--
-- This owner states that missing representation theorem as a typed object.
-- It is reusable for tape/state/head encodings and prevents an arbitrary Set
-- from being silently treated as a bit string.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)

import DASHI.Core.EfficientRecoverableQuotientExact as ERQ

record FiniteConfigurationCodec (Configuration : Set) : Set₁ where
  field
    encode : Configuration → List Bool
    decode : List Bool → Configuration

    bitLength : List Bool → Nat
    encodedWidth : Configuration → Nat

    encodedWidthExact :
      (configuration : Configuration) →
      bitLength (encode configuration) ≡ encodedWidth configuration

    decodeEncode :
      (configuration : Configuration) →
      decode (encode configuration) ≡ configuration

open FiniteConfigurationCodec public

record CookLevinEncodingFoundation
    (Configuration : Set) : Set₁ where
  field
    codec : FiniteConfigurationCodec Configuration

    widthAtInputSize : Nat → Nat
    widthPolynomial :
      ERQ.PolynomialBound widthAtInputSize

    configurationWidthBound :
      Configuration → Nat → Set

    widthBoundMeans :
      ∀ configuration inputSize →
      configurationWidthBound configuration inputSize →
      encodedWidth codec configuration ≤ widthAtInputSize inputSize

open CookLevinEncodingFoundation public
