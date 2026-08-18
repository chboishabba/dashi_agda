module DASHI.Ontology.DisjointUnionLatticeJMDBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge using (LeanTheoremContract)
open import DASHI.Ontology.LeanWikidataLatestEpistemicConformanceBridge

------------------------------------------------------------------------
-- Finite-KB disjoint-union semantics.
--
-- JMD's RequestProject.Wikidata.ClassAlgebra defines, over the known entity
-- carrier of one finite KB:
--
--   IsUnionOn kb c ms :=
--     every member m is a subclass of c
--     AND every known instance of c is an instance of some m in ms
--
--   IsDisjointUnionOn kb c ms :=
--     IsUnionOn kb c ms
--     AND distinct members are pairwise DisjointOn.
--
-- `Wikidata.dunOk_iff` proves the executable checker exact for that semantics.
-- This is deliberately an open-world finite-KB contract: coverage concerns the
-- known entity carrier, not every possible real-world instance.
------------------------------------------------------------------------

jmdFiniteDisjointUnionExactness : LeanTheoremContract
jmdFiniteDisjointUnionExactness = jmdDisjointUnionCheckerExact

infixr 6 _∧ᵇ_

_∧ᵇ_ : Bool → Bool → Bool
true  ∧ᵇ x = x
false ∧ᵇ _ = false

record FiniteDisjointUnionStatus : Set where
  constructor finiteDisjointUnionStatus
  field
    componentsSubclassHolder : Bool
    knownHolderInstancesCovered : Bool
    pairwiseKnownDisjoint : Bool

open FiniteDisjointUnionStatus public

finiteDunOk : FiniteDisjointUnionStatus → Bool
finiteDunOk status =
  componentsSubclassHolder status
  ∧ᵇ knownHolderInstancesCovered status
  ∧ᵇ pairwiseKnownDisjoint status

completeFiniteDisjointUnion : FiniteDisjointUnionStatus
completeFiniteDisjointUnion = finiteDisjointUnionStatus true true true

missingSubclassEdge : FiniteDisjointUnionStatus
missingSubclassEdge = finiteDisjointUnionStatus false true true

nonExhaustiveKnownUnion : FiniteDisjointUnionStatus
nonExhaustiveKnownUnion = finiteDisjointUnionStatus true false true

overlappingMembers : FiniteDisjointUnionStatus
overlappingMembers = finiteDisjointUnionStatus true true false

completeFiniteDisjointUnionPasses :
  finiteDunOk completeFiniteDisjointUnion ≡ true
completeFiniteDisjointUnionPasses = refl

componentNotSubclassOfUnionFails :
  finiteDunOk missingSubclassEdge ≡ false
componentNotSubclassOfUnionFails = refl

unionExhaustivityFailureFails :
  finiteDunOk nonExhaustiveKnownUnion ≡ false
unionExhaustivityFailureFails = refl

pairwiseDisjointnessFailureFails :
  finiteDunOk overlappingMembers ≡ false
pairwiseDisjointnessFailureFails = refl

------------------------------------------------------------------------
-- The three obligations are independent diagnostic coordinates.
-- Pairwise disjointness alone does not establish a disjoint union; likewise
-- coverage without disjointness only establishes an ordinary finite union.
------------------------------------------------------------------------

pairwiseDisjointAloneDoesNotEstablishDun :
  pairwiseKnownDisjoint nonExhaustiveKnownUnion ≡ true
pairwiseDisjointAloneDoesNotEstablishDun = refl

coverageAloneDoesNotEstablishDun :
  knownHolderInstancesCovered overlappingMembers ≡ true
coverageAloneDoesNotEstablishDun = refl

subclassAndCoverageCanHoldWhileDisjointnessFails :
  (componentsSubclassHolder overlappingMembers ∧ᵇ
   knownHolderInstancesCovered overlappingMembers) ≡ true
subclassAndCoverageCanHoldWhileDisjointnessFails = refl

record DisjointUnionDiagnosticBoundary : Set where
  constructor disjointUnionDiagnosticBoundary
  field
    componentFailureIndependent : Bool
    exhaustivityFailureIndependent : Bool
    pairwiseFailureIndependent : Bool
    exhaustivityIsKnownCarrierScoped : Bool

canonicalDisjointUnionDiagnosticBoundary : DisjointUnionDiagnosticBoundary
canonicalDisjointUnionDiagnosticBoundary =
  disjointUnionDiagnosticBoundary true true true true
