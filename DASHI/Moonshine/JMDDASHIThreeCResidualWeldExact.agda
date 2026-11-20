module DASHI.Moonshine.JMDDASHIThreeCResidualWeldExact where

-- JMD: 3C centralizer and North Star diagrams (2026-11-20).
-- DASHI: doubled ternary orbit and residual 54 diagram.
-- Joint synthesis: cyclic character comparison; not an original VOA map.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Integer.Base using (+_)
open import Data.Integer using (-_)
import DASHI.Moonshine.Monster3BBalancedRegularFibreExact as B
import DASHI.Moonshine.MonsterC3CyclotomicEvaluationExact as C
import DASHI.Biology.MonsterSubgroupBranchingBenchmarksExact as N

sixfold : Nat
sixfold = 3 * 2

residual : Nat
residual = sixfold * 3 * 3

residual-weld : residual ≡ B.monster3BConformalTrace
residual-weld = refl

common-core : Nat
common-core = B.monster3BRegularMultiplicity

origami-core : common-core ≡ (5 * 2) * 6561
origami-core rewrite B.monster3BRegularMultiplicityIs65610 = refl

transfer : Nat
transfer = sixfold * 3

balanced-core : common-core + transfer ≡ 65628
balanced-core rewrite B.monster3BRegularMultiplicityIs65610 = refl

b-weight-two c-weight-two : C.C3PhaseMultiplicity
b-weight-two = C.c3PhaseMultiplicity (+ 65664) (+ 65610) (+ 65610)
c-weight-two = C.c3PhaseMultiplicity (+ 65628) (+ 65628) (+ 65628)

b-trace : C.generatorEvaluation b-weight-two ≡ C.c3 (+ 54) (+ 0)
b-trace = refl

c-trace : C.generatorEvaluation c-weight-two ≡ C.zeroC3
c-trace = refl

b-dimension : C.identityEvaluation b-weight-two ≡ + 196884
b-dimension = refl

c-dimension : C.identityEvaluation c-weight-two ≡ + 196884
c-dimension = refl

fixed-transfer : 65628 + 36 ≡ 65664
fixed-transfer = refl

phase-transfer : 65610 + transfer ≡ 65628
phase-transfer = refl

normalizer-label : N.normalizerKind N.class3C ≡ N.symmetricThreeTimesThompson
normalizer-label = N.threeCLaneIsDistinct

-- The normalizer label is source data, not a constructed embedding.
-- No same-object H1-H5 or Thompson module promotion is made.

-- Published 2A reflection source: Breuer, Magaard, Wilson,
-- arXiv:2412.12182, Fact 1 (product of 2A involutions in class 3C).
-- Arithmetic consequences only; no subgroup embedding constructed here.
s3-trivial : Nat
s3-trivial = 35000

s3-sign : Nat
s3-sign = 30628

s3-standard : Nat
s3-standard = 65628

s3-dimension : s3-trivial + s3-sign + 2 * s3-standard ≡ 196884
s3-dimension = refl

s3-reflection : s3-sign + 4372 ≡ s3-trivial
s3-reflection = refl

s3-rotation-zero : s3-trivial + s3-sign ≡ s3-standard
s3-rotation-zero = refl

s3-regular-core-and-ternary-residual : 6 * s3-sign + 3 * 4372 ≡ 196884
s3-regular-core-and-ternary-residual = refl

s3-standard-split : 2 * s3-sign + 4372 ≡ s3-standard
s3-standard-split = refl

-- Character-level tensor factors only. No canonical Monster intertwiner.
shared-cyclic-remainder : Nat
shared-cyclic-remainder = 1 + 1215 * 3

shared-remainder-size : shared-cyclic-remainder ≡ 3646
shared-remainder-size = refl

shared-tensor-dimension : residual * shared-cyclic-remainder ≡ 196884
shared-tensor-dimension = refl

three-b-free-blocks : 54 * 1215 ≡ 65610
three-b-free-blocks = refl

three-c-free-blocks : 18 * shared-cyclic-remainder ≡ 65628
three-c-free-blocks = refl

s3-small-factor-dimension : 10 + 8 + 2 * 18 ≡ 54
s3-small-factor-dimension = refl

s3-small-factor-rotation : 10 + 8 ≡ 18
s3-small-factor-rotation = refl

s3-small-factor-reflection : 8 + 2 ≡ 10
s3-small-factor-reflection = refl

s3-large-factor-dimension : 2186 + 2 * 730 ≡ 3646
s3-large-factor-dimension = refl

s3-large-factor-rotation : 730 + 1456 ≡ 2186
s3-large-factor-rotation = refl

s3-tensor-reflection : 2 * 2186 ≡ 4372
s3-tensor-reflection = refl

s3-small-factor-regular-and-natural : 8 * 6 + 2 * 3 ≡ 54
s3-small-factor-regular-and-natural = refl

-- Existing source-defined 729 and nested 90, no duplicate carrier.
import DASHI.Moonshine.Base369Pointed729NestedNinetyBidiExact as Nested
import DASHI.Moonshine.Monster3BHeisenbergMultiplicityExact as H
import DASHI.Moonshine.Base369Monster3BMultiplicityTenByNineBidiExact as M

nested729-rechart : Nested.nestedPointedDimension ≡ H.threePowerSix
nested729-rechart rewrite Nested.nestedPointedDimensionIs729 | H.threePowerSixIs729 = refl

nested90-rechart : M.tenByNineDimension ≡ H.multiplicityDegree
nested90-rechart rewrite M.tenByNineDimensionIsNinety | H.multiplicityDegreeIs90 = refl

nested-core-rechart : Nested.nestedZetaDimension ≡ common-core
nested-core-rechart rewrite Nested.nestedZetaDimensionIs65610 | B.monster3BRegularMultiplicityIs65610 = refl

nested-pointed-remainder : 5 * Nested.nestedPointedDimension + 1 ≡ shared-cyclic-remainder
nested-pointed-remainder rewrite Nested.nestedPointedDimensionIs729 = refl

nested-permutation-factor : 1456 + 3 * (Nested.nestedPointedDimension + 1) ≡ shared-cyclic-remainder
nested-permutation-factor rewrite Nested.nestedPointedDimensionIs729 = refl

-- Arithmetic leaves of the Thompson tensor obstruction. The published
-- representation-degree bound and actual involution trace alternatives are
-- external hypotheses; no selected Th action is manufactured here.
th-involution-2a-remainder : 54 * 80 + 52 ≡ 4372
th-involution-2a-remainder = refl

th-involution-2b-remainder : 54 * 5 + 6 ≡ 276
th-involution-2b-remainder = refl
