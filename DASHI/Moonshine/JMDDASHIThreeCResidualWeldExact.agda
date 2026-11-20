{-# OPTIONS --safe #-}
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
