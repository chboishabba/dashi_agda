module DASHI.Biology.IITProjectiveF9Pointed80Exact where

open import DASHI.Core.Prelude

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Moonshine.OggSSPP3F9FrobeniusCandidateNoGoExact as F9
import DASHI.Moonshine.OggSSPP2PuncturedKernel2BidiExact as P2
import DASHI.Analysis.RiemannQuarticTriadicCodecKernelBridgeExact as P4
import DASHI.Biology.IITJFineSelectedCrossPunctured79Exact as JCodec

------------------------------------------------------------------------
-- Exact original source carrier isomorphism:
--   harmonic ordinary nine + completionJ <-> F9-shaped nine + infinity.
-- Distinguish this **pointed chart** from the algebraic quotient of
-- F81^× by F9^×: its actual 80-point trivialisation is a numerical
-- finite witness (scripts/iit_projective_f9_pointed80_audit.py), not yet
-- a kernel-checked Agda operation on the literal Kernel4 source.
------------------------------------------------------------------------

data ProjectiveF9Chart : Set where
  affine : F9.F9Point → ProjectiveF9Chart
  infinity : ProjectiveF9Chart

toF3 : Harmonic.BalancedTrit → F9.F3
toF3 Harmonic.negativeTrit = F9.t3
toF3 Harmonic.zeroTrit = F9.z3
toF3 Harmonic.positiveTrit = F9.o3

fromF3 : F9.F3 → Harmonic.BalancedTrit
fromF3 F9.z3 = Harmonic.zeroTrit
fromF3 F9.o3 = Harmonic.positiveTrit
fromF3 F9.t3 = Harmonic.negativeTrit

fromAfterToF3 :
  (x : Harmonic.BalancedTrit) → fromF3 (toF3 x) ≡ x
fromAfterToF3 Harmonic.negativeTrit = refl
fromAfterToF3 Harmonic.zeroTrit = refl
fromAfterToF3 Harmonic.positiveTrit = refl

toAfterFromF3 : (x : F9.F3) → toF3 (fromF3 x) ≡ x
toAfterFromF3 F9.z3 = refl
toAfterFromF3 F9.o3 = refl
toAfterFromF3 F9.t3 = refl

toProjectiveChart : Harmonic.CoarseChannel → ProjectiveF9Chart
toProjectiveChart Harmonic.completionJ = infinity
toProjectiveChart
  (Harmonic.ordinaryChannel (Harmonic.balancedPair a b)) =
  affine (F9.f9 (toF3 a) (toF3 b))

fromProjectiveChart : ProjectiveF9Chart → Harmonic.CoarseChannel
fromProjectiveChart infinity = Harmonic.completionJ
fromProjectiveChart (affine (F9.f9 a b)) =
  Harmonic.ordinaryChannel
    (Harmonic.balancedPair (fromF3 a) (fromF3 b))

fromAfterToChart :
  (c : Harmonic.CoarseChannel) →
  fromProjectiveChart (toProjectiveChart c) ≡ c
fromAfterToChart Harmonic.completionJ = refl
fromAfterToChart
  (Harmonic.ordinaryChannel (Harmonic.balancedPair a b))
  rewrite fromAfterToF3 a | fromAfterToF3 b = refl

toAfterFromChart :
  (p : ProjectiveF9Chart) →
  toProjectiveChart (fromProjectiveChart p) ≡ p
toAfterFromChart infinity = refl
toAfterFromChart (affine (F9.f9 a b))
  rewrite toAfterFromF3 a | toAfterFromF3 b = refl

jCompletionIsInfinity :
  toProjectiveChart Harmonic.completionJ ≡ infinity
jCompletionIsInfinity = refl

-- These two actual pre-existing punctured carrier types have 8 and 80
-- elements respectively. Converting one into the other via the projective
-- scalar fibre requires an explicit F9 scalar multiplication and chart.
PuncturedEight : Set
PuncturedEight = P2.PuncturedKernel2

PuncturedEighty : Set
PuncturedEighty = P4.PuncturedKernel4

record Projective80Trivialisation : Set₁ where
  field
    toProjectiveFibre :
      PuncturedEighty → ProjectiveF9Chart × PuncturedEight
    fromProjectiveFibre :
      ProjectiveF9Chart × PuncturedEight → PuncturedEighty
    decodeEncode :
      (x : ProjectiveF9Chart × PuncturedEight) →
      toProjectiveFibre (fromProjectiveFibre x) ≡ x
    encodeDecode :
      (x : PuncturedEighty) →
      fromProjectiveFibre (toProjectiveFibre x) ≡ x

nineTimesEightPlusEight : 9 * 8 + 8 ≡ 80
nineTimesEightPlusEight = refl

pointedTimesEight : (9 + 1) * 8 ≡ 80
pointedTimesEight = refl

seventyNineInverseExponent : 79 + 1 ≡ 80
seventyNineInverseExponent = refl

record ProjectiveF9AuthorityBoundary : Set where
  constructor projective-f9-authority-boundary
  field
    ninePlusInfinityCoarseChartConstructed : Bool
    originalPuncturedSourcesReused : Bool
    literalPunctured80AgdaTrivialisationConstructed : Bool
    independentF81ProjectiveFiniteReceiptAvailable : Bool
    externalClassicalModularJIdentityConstructed : Bool
    MonsterActionConstructed : Bool

canonicalProjectiveF9AuthorityBoundary : ProjectiveF9AuthorityBoundary
canonicalProjectiveF9AuthorityBoundary =
  projective-f9-authority-boundary true true false true false false
