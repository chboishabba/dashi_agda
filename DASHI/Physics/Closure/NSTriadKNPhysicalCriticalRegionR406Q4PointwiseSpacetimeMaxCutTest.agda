module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4PointwiseSpacetimeMaxCutTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4PointwiseSpacetimeMaxCutExact as Q

compilerClosed : Q.q4PointwiseToSpacetimeCompilerClosed ≡ true
compilerClosed = Q.q4PointwiseToSpacetimeCompilerClosedIsTrue

pointwiseOpen : Q.q4PointwisePhysicalGramEstimateClosedHere ≡ false
pointwiseOpen = Q.q4PointwisePhysicalGramEstimateClosedHereIsFalse
