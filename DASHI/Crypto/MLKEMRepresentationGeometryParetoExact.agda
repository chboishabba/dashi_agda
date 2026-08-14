module DASHI.Crypto.MLKEMRepresentationGeometryParetoExact where

------------------------------------------------------------------------
-- COEFFICIENT VS NTT SEARCH GEOMETRY: STRUCTURAL PARETO TRADEOFF
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Coefficient space is local for the CBD prior: one primitive candidate move can
-- change one independently sampled source coefficient.  But when the maintained
-- public residual is represented in the FIPS NTT/BaseCase form, that one source
-- coefficient has broad structural fanout.
--
-- NTT space is the opposite tradeoff.  One local secret scalar at one residue
-- participates only in the corresponding BaseCase residue across k public rows,
-- so its direct public-output fanout is 2*k scalar components.  But one NTT
-- scalar secret coordinate depends on 128 source coefficients of one parity
-- class, so the transported CBD prior is not local in that coordinate.
--
-- Therefore neither representation structurally dominates the other on both
-- prior locality and public-residual update locality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Product using (_×_; _,_)

import DASHI.Crypto.MLKEMFIPS203SourceExact as FIPS
import DASHI.Crypto.MLKEMNTTDataflowCouplingExact as NTT
import DASHI.Crypto.MLKEMCandidateMoveFanoutExact as Fanout

record StructuralSearchGeometry : Set where
  constructor structuralSearchGeometry
  field
    priorSourceWidth : Nat
    publicResidualFanout : Nat

open StructuralSearchGeometry public

coefficientGeometry : FIPS.MLKEMParameters → StructuralSearchGeometry
coefficientGeometry p =
  structuralSearchGeometry 1 (Fanout.publicResidualScalarFanout p)

nttScalarGeometry : FIPS.MLKEMParameters → StructuralSearchGeometry
nttScalarGeometry p =
  structuralSearchGeometry
    NTT.sourceCoefficientsPerScalarNTTCoordinate
    (2 * FIPS.k p)

------------------------------------------------------------------------
-- Exact approved-parameter profiles.
------------------------------------------------------------------------

coefficient512Profile :
  priorSourceWidth (coefficientGeometry FIPS.params512) ≡ 1
  × publicResidualFanout (coefficientGeometry FIPS.params512) ≡ 512
coefficient512Profile = refl , refl

ntt512Profile :
  priorSourceWidth (nttScalarGeometry FIPS.params512) ≡ 128
  × publicResidualFanout (nttScalarGeometry FIPS.params512) ≡ 4
ntt512Profile = refl , refl

coefficient768Profile :
  priorSourceWidth (coefficientGeometry FIPS.params768) ≡ 1
  × publicResidualFanout (coefficientGeometry FIPS.params768) ≡ 768
coefficient768Profile = refl , refl

ntt768Profile :
  priorSourceWidth (nttScalarGeometry FIPS.params768) ≡ 128
  × publicResidualFanout (nttScalarGeometry FIPS.params768) ≡ 6
ntt768Profile = refl , refl

coefficient1024Profile :
  priorSourceWidth (coefficientGeometry FIPS.params1024) ≡ 1
  × publicResidualFanout (coefficientGeometry FIPS.params1024) ≡ 1024
coefficient1024Profile = refl , refl

ntt1024Profile :
  priorSourceWidth (nttScalarGeometry FIPS.params1024) ≡ 128
  × publicResidualFanout (nttScalarGeometry FIPS.params1024) ≡ 8
ntt1024Profile = refl , refl

------------------------------------------------------------------------
-- Pareto interpretation is explicit rather than hidden in one scalar.
------------------------------------------------------------------------

record RepresentationTradeoff : Set where
  constructor representationTradeoff
  field
    coefficientPriorLocal : Bool
    coefficientPriorLocalIsTrue : coefficientPriorLocal ≡ true
    coefficientVerifierLocal : Bool
    coefficientVerifierLocalIsFalse : coefficientVerifierLocal ≡ false
    nttVerifierLocal : Bool
    nttVerifierLocalIsTrue : nttVerifierLocal ≡ true
    nttPriorLocal : Bool
    nttPriorLocalIsFalse : nttPriorLocal ≡ false
    eitherRepresentationUniversallyDominates : Bool
    eitherRepresentationUniversallyDominatesIsFalse :
      eitherRepresentationUniversallyDominates ≡ false

open RepresentationTradeoff public

canonicalRepresentationTradeoff : RepresentationTradeoff
canonicalRepresentationTradeoff =
  representationTradeoff true refl false refl true refl false refl false refl
