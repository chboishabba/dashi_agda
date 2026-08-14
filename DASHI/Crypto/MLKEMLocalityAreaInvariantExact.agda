module DASHI.Crypto.MLKEMLocalityAreaInvariantExact where

------------------------------------------------------------------------
-- FIPS-203 REPRESENTATION LOCALITY-AREA INVARIANT
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Cross-pollination from the representation-geometry programme suggests asking
-- whether prior locality and verifier/update locality can be simultaneously
-- small.  For the two canonical primitive move notions already formalized:
--
-- coefficient-local move:
--   source/prior support = 1 coefficient,
--   public residual structural fanout = 256*k scalar coordinates;
--
-- scalar-NTT-local move:
--   source/prior support = 128 coefficients,
--   public residual structural fanout = 2*k scalar coordinates.
--
-- Their structural locality areas are therefore exactly equal:
--   1*(256*k) = 128*(2*k) = 256*k.
--
-- This is a finite dataflow identity, not a Fourier uncertainty theorem and not
-- a lower bound over every possible representation.  It nevertheless turns the
-- observed locality tradeoff into an exact same-parameter invariant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Crypto.MLKEMFIPS203SourceExact as FIPS
import DASHI.Crypto.MLKEMCandidateMoveFanoutExact as Fanout

coefficientPriorSupport : Nat
coefficientPriorSupport = 1

nttScalarPriorSupport : Nat
nttScalarPriorSupport = 128

coefficientPublicFanout : FIPS.MLKEMParameters → Nat
coefficientPublicFanout = Fanout.publicResidualScalarFanout

nttScalarPublicFanout : FIPS.MLKEMParameters → Nat
nttScalarPublicFanout p = 2 * FIPS.k p

coefficientLocalityArea : FIPS.MLKEMParameters → Nat
coefficientLocalityArea p =
  coefficientPriorSupport * coefficientPublicFanout p

nttScalarLocalityArea : FIPS.MLKEMParameters → Nat
nttScalarLocalityArea p =
  nttScalarPriorSupport * nttScalarPublicFanout p

mlKem512CoefficientArea : coefficientLocalityArea FIPS.params512 ≡ 512
mlKem512CoefficientArea = refl

mlKem512NTTArea : nttScalarLocalityArea FIPS.params512 ≡ 512
mlKem512NTTArea = refl

mlKem512AreasEqual :
  coefficientLocalityArea FIPS.params512 ≡
  nttScalarLocalityArea FIPS.params512
mlKem512AreasEqual = refl

mlKem768CoefficientArea : coefficientLocalityArea FIPS.params768 ≡ 768
mlKem768CoefficientArea = refl

mlKem768NTTArea : nttScalarLocalityArea FIPS.params768 ≡ 768
mlKem768NTTArea = refl

mlKem768AreasEqual :
  coefficientLocalityArea FIPS.params768 ≡
  nttScalarLocalityArea FIPS.params768
mlKem768AreasEqual = refl

mlKem1024CoefficientArea : coefficientLocalityArea FIPS.params1024 ≡ 1024
mlKem1024CoefficientArea = refl

mlKem1024NTTArea : nttScalarLocalityArea FIPS.params1024 ≡ 1024
mlKem1024NTTArea = refl

mlKem1024AreasEqual :
  coefficientLocalityArea FIPS.params1024 ≡
  nttScalarLocalityArea FIPS.params1024
mlKem1024AreasEqual = refl

record LocalityTradeoffBoundary : Set where
  constructor localityTradeoffBoundary
  field
    equalLocalityAreaProvesUniversalUncertaintyPrinciple : Bool
    equalLocalityAreaProvesUniversalUncertaintyPrincipleIsFalse :
      equalLocalityAreaProvesUniversalUncertaintyPrinciple ≡ false
    coefficientCoordinatesSimultaneouslyMinimizeBothLocalities : Bool
    coefficientCoordinatesSimultaneouslyMinimizeBothLocalitiesIsFalse :
      coefficientCoordinatesSimultaneouslyMinimizeBothLocalities ≡ false
    nttCoordinatesSimultaneouslyMinimizeBothLocalities : Bool
    nttCoordinatesSimultaneouslyMinimizeBothLocalitiesIsFalse :
      nttCoordinatesSimultaneouslyMinimizeBothLocalities ≡ false

open LocalityTradeoffBoundary public

canonicalLocalityTradeoffBoundary : LocalityTradeoffBoundary
canonicalLocalityTradeoffBoundary =
  localityTradeoffBoundary false refl false refl false refl
