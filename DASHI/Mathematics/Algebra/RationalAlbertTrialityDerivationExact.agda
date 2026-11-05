module DASHI.Mathematics.Algebra.RationalAlbertTrialityDerivationExact where

------------------------------------------------------------------------
-- EXACT TRIALITY-SHAPED DECOMPOSITION OF THE ALBERT DERIVATION ALGEBRA
--
-- Companion producer:
--   scripts/albert_inner_derivation_rank.py
--
-- The exact 52-dimensional span of inner derivations admits the following
-- coordinate-adapted independent basis:
--
--   so8 : [L_xi,L_xj] for 0 <= i < j < 8                = 28
--   V1  : one diagonal idempotent against the x slot     =  8
--   V2  : one diagonal idempotent against the y slot     =  8
--   V3  : one diagonal idempotent against the z slot     =  8
--
-- Thus 52 = 28+8+8+8.  The exact executable additionally verifies:
--
--   [so8,so8] <= so8
--   [so8,Vi]  <= Vi
--   [Vi,Vi]   <= so8
--   [V1,V2]   <= V3, [V2,V3] <= V1, [V3,V1] <= V2.
--
-- The 28-sector is block diagonal on the three octonion coordinate slots; on
-- each slot it consists of skew 8x8 matrices of exact span rank 28.  This is
-- precisely the standard triality-shaped decomposition associated with F4.
-- The present file records the exact executable theorem surface while keeping
-- the final algebraic-group classification sourced separately.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationF4ReceiptExact as D

------------------------------------------------------------------------
-- Typed sectors and dimensions.
------------------------------------------------------------------------

data TrialitySector : Set where
  so8 V1 V2 V3 : TrialitySector

sectorDimension : TrialitySector → Nat
sectorDimension so8 = 28
sectorDimension V1 = 8
sectorDimension V2 = 8
sectorDimension V3 = 8

trialityDimensionTotal : Nat
trialityDimensionTotal =
  sectorDimension so8 + sectorDimension V1 +
  sectorDimension V2 + sectorDimension V3

record TrialityExecutableReceipt : Set where
  constructor triality-executable-receipt
  field
    scriptPath : String
    derivationSpanDimension : Nat
    so8SectorDimension : Nat
    vectorSectorDimension : Nat
    spinPlusSectorDimension : Nat
    spinMinusSectorDimension : Nat
    selectedBasisIndependent : Bool
    selectedBasisSpansAllInnerDerivations : Bool
    so8RestrictionsSkew : Bool
    so8RestrictionRankEachSlot : Nat
    so8ClosedUnderBracket : Bool
    so8PreservesEachEightSector : Bool
    eachEightSelfBracketLandsInSo8 : Bool
    cyclicCrossBracketsPaid : Bool
    arithmeticExactNotFloating : Bool
open TrialityExecutableReceipt public

canonicalTrialityExecutableReceipt : TrialityExecutableReceipt
canonicalTrialityExecutableReceipt =
  triality-executable-receipt
    "scripts/albert_inner_derivation_rank.py"
    52
    28
    8
    8
    8
    true
    true
    true
    28
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- Attribution firewall.
------------------------------------------------------------------------

record TrialityClassificationBoundary : Set where
  constructor triality-classification-boundary
  field
    exactTwentyEightPlusEightPlusEightPlusEightPaid : Bool
    exactTrialityBracketPatternPaid : Bool
    exactSo8SkewRestrictionPaid : Bool
    standardF4TrialityShapeMatched : Bool
    externalClassificationStillUsedForDynkinNameF4 : Bool
    independentSpin8GroupActionConstructedHere : Bool
    fullF4AutomorphismGroupSchemeConstructedHere : Bool
open TrialityClassificationBoundary public

canonicalTrialityClassificationBoundary : TrialityClassificationBoundary
canonicalTrialityClassificationBoundary =
  triality-classification-boundary
    true true true true true false false
