module DASHI.Moonshine.OggSSPSmallCharacteristicAntipodalHierarchyExact where

------------------------------------------------------------------------
-- OGG/SSP SMALL-CHARACTERISTIC TARGETS AS ONE ANTIPODAL 369 HIERARCHY
--
-- ATTRIBUTION BOUNDARY
--
-- External arithmetic residual values remain owned by the attributed
-- Duncan--Swisher reconstruction upstream.
--
-- DASHI contribution:
--   * rechart the p=3 residual orbit carrier as rank-1 antipodal geometry;
--   * rechart the p=2 five-orbit quotient as rank-2 antipodal geometry;
--   * retain the p=2 binary orientation/provenance sheet over that rank-2
--     quotient;
--   * factor the F9 extension-coordinate quotient through rank-1 geometry.
--
-- These are finite same-presentation statements.  They do not identify the
-- missing marked arithmetic supersingular source.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Foundations.BalancedTernaryAntipodal369OrbitHierarchyExact as Hierarchy
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Antipodal
import DASHI.Biology.TriadicKernelLiftQuotientExact as Kernel
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Residual
import DASHI.Moonshine.OggSSPMonstrousExponent369GluingExact as Exponent
import DASHI.Moonshine.OggSSPP3F9FrobeniusCandidateNoGoExact as F9
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source

------------------------------------------------------------------------
-- 1. p=3 orbit carrier <-> rank-1 antipodal quotient.
------------------------------------------------------------------------

p3OrbitToRank1 :
  Residual.ConstantTernaryOrbit ->
  Hierarchy.AntipodalClass3
p3OrbitToRank1 Residual.zeroConstantOrbit = Hierarchy.centre3
p3OrbitToRank1 Residual.nonzeroConstantOrbit = Hierarchy.nonzero3

rank1ToP3Orbit :
  Hierarchy.AntipodalClass3 ->
  Residual.ConstantTernaryOrbit
rank1ToP3Orbit Hierarchy.centre3 = Residual.zeroConstantOrbit
rank1ToP3Orbit Hierarchy.nonzero3 = Residual.nonzeroConstantOrbit

p3Rank1RoundTrip :
  (orbit : Residual.ConstantTernaryOrbit) ->
  rank1ToP3Orbit (p3OrbitToRank1 orbit) ≡ orbit
p3Rank1RoundTrip Residual.zeroConstantOrbit = refl
p3Rank1RoundTrip Residual.nonzeroConstantOrbit = refl

rank1P3RoundTrip :
  (orbit : Hierarchy.AntipodalClass3) ->
  p3OrbitToRank1 (rank1ToP3Orbit orbit) ≡ orbit
rank1P3RoundTrip Hierarchy.centre3 = refl
rank1P3RoundTrip Hierarchy.nonzero3 = refl

p3ResidualCountIsRank1OrbitCount :
  Exponent.p3ExceptionalResidual
  ≡ Hierarchy.quotientOrbitCount Hierarchy.rank1
p3ResidualCountIsRank1OrbitCount = refl

------------------------------------------------------------------------
-- 2. p=2 quotient carrier <-> rank-2 antipodal quotient.
------------------------------------------------------------------------

p2OrbitToRank2 :
  Kernel.NineOrbit ->
  Antipodal.AntipodalClass9
p2OrbitToRank2 = Hierarchy.kernelNineOrbitToAntipodal9

rank2ToP2Orbit :
  Antipodal.AntipodalClass9 ->
  Kernel.NineOrbit
rank2ToP2Orbit = Hierarchy.antipodal9ToKernelNineOrbit

p2Rank2RoundTrip :
  (orbit : Kernel.NineOrbit) ->
  rank2ToP2Orbit (p2OrbitToRank2 orbit) ≡ orbit
p2Rank2RoundTrip = Hierarchy.kernelNineOrbitRoundTrip

rank2P2RoundTrip :
  (orbit : Antipodal.AntipodalClass9) ->
  p2OrbitToRank2 (rank2ToP2Orbit orbit) ≡ orbit
rank2P2RoundTrip = Hierarchy.antipodal9RoundTrip

------------------------------------------------------------------------
-- 3. Retained p=2 fine carrier = binary provenance x rank-2 quotient.
------------------------------------------------------------------------

P2Rank2RetainedState : Set
P2Rank2RetainedState =
  Compression.StrictSignedSide × Antipodal.AntipodalClass9

p2FineToRank2Retained :
  Residual.P2ResidualObject ->
  P2Rank2RetainedState
p2FineToRank2Retained (side , orbit) =
  side , p2OrbitToRank2 orbit

rank2RetainedToP2Fine :
  P2Rank2RetainedState ->
  Residual.P2ResidualObject
rank2RetainedToP2Fine (side , orbit) =
  side , rank2ToP2Orbit orbit

p2FineRank2RoundTrip :
  (state : Residual.P2ResidualObject) ->
  rank2RetainedToP2Fine (p2FineToRank2Retained state) ≡ state
p2FineRank2RoundTrip (side , orbit)
  rewrite p2Rank2RoundTrip orbit = refl

rank2P2FineRoundTrip :
  (state : P2Rank2RetainedState) ->
  p2FineToRank2Retained (rank2RetainedToP2Fine state) ≡ state
rank2P2FineRoundTrip (side , orbit)
  rewrite rank2P2RoundTrip orbit = refl

p2ResidualCountIsBinaryTimesRank2OrbitCount :
  Exponent.p2ExceptionalResidual
  ≡
  Hierarchy.binaryRetainedSheetCount
  * Hierarchy.quotientOrbitCount Hierarchy.rank2
p2ResidualCountIsBinaryTimesRank2OrbitCount = refl

------------------------------------------------------------------------
-- 4. F9 extension-coordinate quotient factors through rank-1 orbit geometry.
--
-- Whole F9 has six Frobenius components.  The extension-coordinate quotient
-- merges the three fixed components to centre3 and the three paired components
-- to nonzero3.  This is quotient recognition, not pi0 embedding.
------------------------------------------------------------------------

f9OrbitToRank1 :
  F9.F9FrobeniusOrbit ->
  Hierarchy.AntipodalClass3
f9OrbitToRank1 orbit =
  p3OrbitToRank1 (F9.f9OrbitToP3Orbit orbit)

f9FixedComponentsLandAtCentre :
  (f9OrbitToRank1 F9.fixed0 ≡ Hierarchy.centre3)
  ×
  (f9OrbitToRank1 F9.fixed1 ≡ Hierarchy.centre3)
  ×
  (f9OrbitToRank1 F9.fixed2 ≡ Hierarchy.centre3)
f9FixedComponentsLandAtCentre = refl , refl , refl

f9PairedComponentsLandAtNonzero :
  (f9OrbitToRank1 F9.pair0 ≡ Hierarchy.nonzero3)
  ×
  (f9OrbitToRank1 F9.pair1 ≡ Hierarchy.nonzero3)
  ×
  (f9OrbitToRank1 F9.pair2 ≡ Hierarchy.nonzero3)
f9PairedComponentsLandAtNonzero = refl , refl , refl

data F9Rank1QuotientCreatesArithmeticSameObject : Set where

f9Rank1QuotientDoesNotCreateArithmeticSameObject :
  F9Rank1QuotientCreatesArithmeticSameObject -> ⊥
f9Rank1QuotientDoesNotCreateArithmeticSameObject ()

------------------------------------------------------------------------
-- 5. Unified target shape.
------------------------------------------------------------------------

data ExceptionalAntipodalTarget : Set where
  p3Rank1Quotient : ExceptionalAntipodalTarget
  p2BinaryOverRank2Quotient : ExceptionalAntipodalTarget

exceptionalTargetComponentCount :
  ExceptionalAntipodalTarget -> Nat
exceptionalTargetComponentCount p3Rank1Quotient =
  Hierarchy.quotientOrbitCount Hierarchy.rank1
exceptionalTargetComponentCount p2BinaryOverRank2Quotient =
  Hierarchy.binaryRetainedSheetCount
  * Hierarchy.quotientOrbitCount Hierarchy.rank2

p3ExceptionalTargetCountIsTwo :
  exceptionalTargetComponentCount p3Rank1Quotient ≡ 2
p3ExceptionalTargetCountIsTwo = refl

p2ExceptionalTargetCountIsTen :
  exceptionalTargetComponentCount p2BinaryOverRank2Quotient ≡ 10
p2ExceptionalTargetCountIsTen = refl

claimOrigin : Source.ClaimOrigin
claimOrigin = Source.repositoryCrossModuleInference

record OggSSPSmallCharacteristicAntipodalHierarchyBoundary : Set where
  constructor ogg-ssp-small-characteristic-antipodal-hierarchy-boundary
  field
    p3ResidualOrbitIsRank1AntipodalPresentation : Bool
    p2FiveOrbitIsRank2AntipodalPresentation : Bool
    p2FineCarrierIsBinaryOverRank2 : Bool
    f9ExtensionQuotientFactorsThroughRank1 : Bool
    p3ResidualCountRecoveredFromRank1 : Bool
    p2ResidualCountRecoveredFromBinaryRank2 : Bool
    markedArithmeticSourceRecognized : Bool

canonicalOggSSPSmallCharacteristicAntipodalHierarchyBoundary :
  OggSSPSmallCharacteristicAntipodalHierarchyBoundary
canonicalOggSSPSmallCharacteristicAntipodalHierarchyBoundary =
  ogg-ssp-small-characteristic-antipodal-hierarchy-boundary
    true true true true true true false
