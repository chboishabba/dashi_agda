module DASHI.Law.QueryDependencySliceCompilationRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.QueryDependencySliceCompilationExact as Slice

boundary : Slice.QueryDependencySliceCompilationBoundary
boundary = Slice.canonicalQueryDependencySliceCompilationBoundary

semanticSeedsSlice :
  Slice.requiredSemanticRefSeedsSlice boundary ≡ true
semanticSeedsSlice =
  Slice.requiredSemanticRefSeedsSliceIsTrue boundary

reviewDependencyIncluded :
  Slice.transitiveExplanationDependencyEntersSlice boundary ≡ true
reviewDependencyIncluded =
  Slice.transitiveExplanationDependencyEntersSliceIsTrue boundary

revisionIncluded :
  Slice.provenanceSourceRevisionEntersSlice boundary ≡ true
revisionIncluded =
  Slice.provenanceSourceRevisionEntersSliceIsTrue boundary

unrelatedExcluded :
  Slice.unrelatedWorldSourceAutomaticallyEntersSlice boundary ≡ false
unrelatedExcluded =
  Slice.unrelatedWorldSourceAutomaticallyEntersSliceIsFalse boundary
