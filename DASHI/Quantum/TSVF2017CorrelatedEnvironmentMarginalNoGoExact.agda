{-# OPTIONS --safe #-}
module DASHI.Quantum.TSVF2017CorrelatedEnvironmentMarginalNoGoExact where

-- P01.L13/L15: strict correlated-environment falsifier for the claim
-- that independent local (one-register) marginal records determine
-- the actual global Hilbert overlap or selected TSVF Born weight.
--
-- The two unnormalized Bell-sector vectors |00>+|11> and |00>-|11>
-- have identical reduced one-register density matrices (both I),
-- equal norm-square 2, but ZERO global inner product. After a common
-- 1/sqrt(2) normalization their reduced density matrices are both
-- I/2 yet their global Born overlap remains exactly zero.
-- This finite algebraic no-go does not assert an actual entanglement
-- source was produced by the physical 2017 experiment.
--
-- Reuses DASHI rational-complex Cayley-Dickson source; no new axiom,
-- incomplete proof, or ad hoc physical probability convention.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as C

record TwoRegisterKet : Set where
  constructor twoRegisterKet
  field
    amp00 amp01 amp10 amp11 : C.RationalComplex
open TwoRegisterKet public

bellRight bellWrong : TwoRegisterKet
bellRight = twoRegisterKet C.oneC C.zeroC C.zeroC C.oneC
bellWrong = twoRegisterKet C.oneC C.zeroC C.zeroC (C.negC C.oneC)

hermitianTerm :
  C.RationalComplex → C.RationalComplex → C.RationalComplex
hermitianTerm a b = C._*c_ (C.conjugateC a) b

globalOverlap : TwoRegisterKet → TwoRegisterKet → C.RationalComplex
globalOverlap a b =
  C._+c_
    (C._+c_
      (hermitianTerm (amp00 a) (amp00 b))
      (hermitianTerm (amp01 a) (amp01 b)))
    (C._+c_
      (hermitianTerm (amp10 a) (amp10 b))
      (hermitianTerm (amp11 a) (amp11 b)))

globalBorn : TwoRegisterKet → TwoRegisterKet → ℚ
globalBorn a b = C.complexNormSq (globalOverlap a b)

normSquare : TwoRegisterKet → ℚ
normSquare a = globalBorn a a

-- Each one-register reduced density is represented by its four
-- COMPLEX matrix entries, including off-diagonals (not just probabilities).
record OneRegisterDensity : Set where
  constructor oneRegisterDensity
  field
    rho00 rho01 rho10 rho11 : C.RationalComplex
open OneRegisterDensity public

firstReduced : TwoRegisterKet → OneRegisterDensity
firstReduced v = oneRegisterDensity
  (C._+c_ (hermitianTerm (amp00 v) (amp00 v))
           (hermitianTerm (amp01 v) (amp01 v)))
  (C._+c_ (hermitianTerm (amp00 v) (amp10 v))
           (hermitianTerm (amp01 v) (amp11 v)))
  (C._+c_ (hermitianTerm (amp10 v) (amp00 v))
           (hermitianTerm (amp11 v) (amp01 v)))
  (C._+c_ (hermitianTerm (amp10 v) (amp10 v))
           (hermitianTerm (amp11 v) (amp11 v)))

secondReduced : TwoRegisterKet → OneRegisterDensity
secondReduced v = oneRegisterDensity
  (C._+c_ (hermitianTerm (amp00 v) (amp00 v))
           (hermitianTerm (amp10 v) (amp10 v)))
  (C._+c_ (hermitianTerm (amp00 v) (amp01 v))
           (hermitianTerm (amp10 v) (amp11 v)))
  (C._+c_ (hermitianTerm (amp01 v) (amp00 v))
           (hermitianTerm (amp11 v) (amp10 v)))
  (C._+c_ (hermitianTerm (amp01 v) (amp01 v))
           (hermitianTerm (amp11 v) (amp11 v)))

identityLocalDensity : OneRegisterDensity
identityLocalDensity =
  oneRegisterDensity C.oneC C.zeroC C.zeroC C.oneC

-- Concrete complete matrices: same reductions in BOTH sites, with
-- zero off-diagonals (the phase resides in a GLOBAL correlation).
firstRightIsIdentity :
  firstReduced bellRight ≡ identityLocalDensity
firstRightIsIdentity = refl

firstWrongIsIdentity :
  firstReduced bellWrong ≡ identityLocalDensity
firstWrongIsIdentity = refl

secondRightIsIdentity :
  secondReduced bellRight ≡ identityLocalDensity
secondRightIsIdentity = refl

secondWrongIsIdentity :
  secondReduced bellWrong ≡ identityLocalDensity
secondWrongIsIdentity = refl

record BothLocalReductions : Set where
  constructor bothLocalReductions
  field
    first second : OneRegisterDensity

localSignature : TwoRegisterKet → BothLocalReductions
localSignature v =
  bothLocalReductions (firstReduced v) (secondReduced v)

sameFullLocalReductions :
  localSignature bellRight ≡ localSignature bellWrong
sameFullLocalReductions = refl

bothNormSquaresAreTwo :
  (normSquare bellRight ≡ 1ℚ + 1ℚ)
  × (normSquare bellWrong ≡ 1ℚ + 1ℚ)
bothNormSquaresAreTwo = refl , refl

-- Despite identical single-site matrices, the complete two-register
-- overlap vanishes by coherent phase cancellation.
twoBellStatesGloballyOrthogonal :
  globalOverlap bellRight bellWrong ≡ C.zeroC
twoBellStatesGloballyOrthogonal = refl

globalBornIsZero :
  globalBorn bellRight bellWrong ≡ 0ℚ
globalBornIsZero = refl

bellStatesDistinct : bellRight ≡ bellWrong → ⊥
bellStatesDistinct ()

-- No deterministic map from the TWO complete local one-site density
-- matrices can reconstruct BOTH different global state vectors.
noLocalMarginalDecoder :
  (decode : BothLocalReductions → TwoRegisterKet) →
  decode (localSignature bellRight) ≡ bellRight →
  decode (localSignature bellWrong) ≡ bellWrong →
  ⊥
noLocalMarginalDecoder decode recR recW =
  bellStatesDistinct
    (trans (sym recR)
      (trans (cong decode sameFullLocalReductions) recW))

-- The identity of all ONE-SITE density matrices is therefore insufficient
-- to replace the global environmental overlap by a product of marginal
-- overlaps. Any physical P01.L13--15 application must supply a true
-- product-state theorem or a quantitative correlated-state error bound.
