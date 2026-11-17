module DASHI.Mathematics.Topology.AlexanderHornedC3ModularJordanF3Exact where

------------------------------------------------------------------------
-- ACTUAL F3-NONSPLITTING SIDE OF THE C3 MASCHKE COMPARISON
--
-- Classical root: modular representation theory of C3, the group
-- algebra F3[C3] = F3[T]/(T-1)^3. See Maschke, Serre and Milne.
--
-- Previous repo owners: C3FourierConjugationExact,
-- C3CyclotomicRealDescentExact, and
-- AlexanderHornedC3MaschkeReynoldsExact (NONMODULAR Q owner).
--
-- SAME integral matrix in both modules:
--   A = [ 0 -1 ; 1 -1 ], A^2+A+I=0 and A^3=I.
--
-- This is an explicit characteristic-3 2D representation,
-- with nonzero nilpotent N=A-I, N^2=0 and a new fixed line.
-- The F3 group algebra is not semisimple, although SOME
-- F3[C3] modules (e.g. trivial 1D modules) remain semisimple.
--
-- No conclusion about Dirac operator zero eigenstates is drawn.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data F3 : Set where
  f0 : F3
  f1 : F3
  f2 : F3

infixl 6 _+3_ _-3_
_+3_ : F3 → F3 → F3
f0 +3 x = x
f1 +3 f0 = f1
f1 +3 f1 = f2
f1 +3 f2 = f0
f2 +3 f0 = f2
f2 +3 f1 = f0
f2 +3 f2 = f1

neg3 : F3 → F3
neg3 f0 = f0
neg3 f1 = f2
neg3 f2 = f1

_-3_ : F3 → F3 → F3
a -3 b = a +3 neg3 b

record V2 : Set where
  constructor v2
  field
    first second : F3
open V2 public

zero : V2
zero = v2 f0 f0

A : V2 → V2
A (v2 x y) = v2 (neg3 y) (x -3 y)

N : V2 → V2
N (v2 x y) = v2 ((neg3 y) -3 x) ((x -3 y) -3 y)

AThreeIsIdentity : ∀ x → A (A (A x)) ≡ x
AThreeIsIdentity (v2 f0 f0) = refl
AThreeIsIdentity (v2 f0 f1) = refl
AThreeIsIdentity (v2 f0 f2) = refl
AThreeIsIdentity (v2 f1 f0) = refl
AThreeIsIdentity (v2 f1 f1) = refl
AThreeIsIdentity (v2 f1 f2) = refl
AThreeIsIdentity (v2 f2 f0) = refl
AThreeIsIdentity (v2 f2 f1) = refl
AThreeIsIdentity (v2 f2 f2) = refl

NSquareIsZero : ∀ x → N (N x) ≡ zero
NSquareIsZero (v2 f0 f0) = refl
NSquareIsZero (v2 f0 f1) = refl
NSquareIsZero (v2 f0 f2) = refl
NSquareIsZero (v2 f1 f0) = refl
NSquareIsZero (v2 f1 f1) = refl
NSquareIsZero (v2 f1 f2) = refl
NSquareIsZero (v2 f2 f0) = refl
NSquareIsZero (v2 f2 f1) = refl
NSquareIsZero (v2 f2 f2) = refl

NIsNonzero : N (v2 f0 f1) ≡ zero → ⊥
NIsNonzero ()

newFixedVector : V2
newFixedVector = v2 f1 f2

newFixedVectorIsFixed : A newFixedVector ≡ newFixedVector
newFixedVectorIsFixed = refl

newFixedVectorNonzero : newFixedVector ≡ zero → ⊥
newFixedVectorNonzero ()

-- There is NO characteristic-3 scalar 1/3, because
-- 3*x=0 for every x in F3. The ordinary Reynolds
-- averaging expression therefore cannot be constructed.
threeTimesAlwaysZero : ∀ x → (x +3 x) +3 x ≡ f0
threeTimesAlwaysZero f0 = refl
threeTimesAlwaysZero f1 = refl
threeTimesAlwaysZero f2 = refl

noInverseOfThree : ∀ x → (x +3 x) +3 x ≡ f1 → ⊥
noInverseOfThree f0 ()
noInverseOfThree f1 ()
noInverseOfThree f2 ()

-- One and the same A is STILL order three in characteristic 3,
-- but unlike the characteristic-5/7 models, it acquires a
-- NONTRIVIAL unipotent Jordan part. The full no-complement
-- classification of its four one-dimensional F3 subspaces
-- is independently enumerated by the prime-comparison probe.
