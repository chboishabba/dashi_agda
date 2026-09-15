module DASHI.Physics.Closure.NSTriadKNLiteralUpperShellCanonicalSuffixRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellCanonicalSuffixExact as Subject

canonicalDropSuffixConstructed :
  Subject.literalCanonicalUpperShellSuffixConstructed ≡ true
canonicalDropSuffixConstructed =
  Subject.literalCanonicalUpperShellSuffixConstructedIsTrue

selectorFoldEqualsCanonicalSuffix :
  Subject.upperShellSelectorEqualsCanonicalSuffixFoldClosed ≡ true
selectorFoldEqualsCanonicalSuffix =
  Subject.upperShellSelectorEqualsCanonicalSuffixFoldClosedIsTrue

canonicalSuffixR98BoundaryFluxClosed :
  Subject.canonicalUpperShellSuffixBoundaryFluxClosed ≡ true
canonicalSuffixR98BoundaryFluxClosed =
  Subject.canonicalUpperShellSuffixBoundaryFluxClosedIsTrue

r104StructuralTailStillOpen :
  Subject.r104StructuralTailEqualsCanonicalSuffixClosed ≡ false
r104StructuralTailStillOpen =
  Subject.r104StructuralTailEqualsCanonicalSuffixClosedIsFalse
