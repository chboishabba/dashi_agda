module DASHI.Cognition.Teleodynamics.AlbertE6BranchingWeldRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.Teleodynamics.AlbertE6BranchingWeldExact as W

open W.AlbertE6BranchingBoundary

repoAlbertAvailable :
  rationalAlbert27Available W.canonicalAlbertE6BranchingBoundary ≡ true
repoAlbertAvailable = refl

repoUnitAvailable :
  rationalAlbertUnitTheoremAvailable W.canonicalAlbertE6BranchingBoundary ≡ true
repoUnitAvailable = refl

ternaryNotPromoted :
  ternary27RecognizedAsRationalAlbert W.canonicalAlbertE6BranchingBoundary ≡ false
ternaryNotPromoted = refl

e8FibreNotPromoted :
  e8Fibre27RecognizedAsRationalAlbert W.canonicalAlbertE6BranchingBoundary ≡ false
e8FibreNotPromoted = refl

f4StillOpen :
  f4AutomorphismActionInhabitedHere W.canonicalAlbertE6BranchingBoundary ≡ false
f4StillOpen = refl

e6StillOpen :
  e6NormStabilizerActionInhabitedHere W.canonicalAlbertE6BranchingBoundary ≡ false
e6StillOpen = refl
