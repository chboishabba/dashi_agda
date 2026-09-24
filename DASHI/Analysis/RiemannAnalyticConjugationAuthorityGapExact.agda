module DASHI.Analysis.RiemannAnalyticConjugationAuthorityGapExact where

------------------------------------------------------------------------
-- CURRENT AnalyticSubstrate ZERO-CONJUGATION AUTHORITY GAP
--
-- CompletedRiemannZeta owns xi(conj s) = conj(xi s), but its isZero predicate
-- is abstract and the record does not currently own either equality transport
-- for isZero or preservation of zero under value conjugation.  Therefore
-- nontrivial-zero conjugation cannot be derived from the present fields alone.
--
-- The older RiemannCompletedZetaBoundary package owns those extra laws on a
-- different coordinate/value presentation.  Reusing it requires a same-object
-- bridge rather than a theorem-name import.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

record AnalyticConjugationAuthorityGapBoundary : Set where
  constructor analytic-conjugation-authority-gap-boundary
  field
    analyticSubstrateOwnsXiConjugationEquation : Bool
    analyticSubstrateOwnsIsZeroEqualityTransport : Bool
    analyticSubstrateOwnsConjugateValuePreservesZero : Bool
    nontrivialZeroConjugationDerivableFromCurrentFieldsAlone : Bool
    olderCompletedZetaPackageHasRequiredZeroSymmetryLaws : Bool
    sameObjectBridgeToOlderPackageStillRequiredForReuse : Bool

open AnalyticConjugationAuthorityGapBoundary public

canonicalAnalyticConjugationAuthorityGapBoundary :
  AnalyticConjugationAuthorityGapBoundary
canonicalAnalyticConjugationAuthorityGapBoundary =
  analytic-conjugation-authority-gap-boundary
    true false false false true true
