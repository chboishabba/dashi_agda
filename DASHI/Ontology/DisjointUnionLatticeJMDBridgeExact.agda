module DASHI.Ontology.DisjointUnionLatticeJMDBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge using (LeanTheoremContract)
open import DASHI.Ontology.LeanWikidataLatestEpistemicConformanceBridge

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
  componentsSubclassHolder status ∧ᵇ
  knownHolderInstancesCovered status ∧ᵇ
  pairwiseKnownDisjoint status

completeFiniteDisjointUnion : FiniteDisjointUnionStatus
completeFiniteDisjointUnion = finiteDisjointUnionStatus true true true

missingSubclassEdge : FiniteDisjointUnionStatus
missingSubclassEdge = finiteDisjointUnionStatus false true true

nonExhaustiveKnownUnion : FiniteDisjointUnionStatus
nonExhaustiveKnownUnion = finiteDisjointUnionStatus true false true

overlappingMembers : FiniteDisjointUnionStatus
overlappingMembers = finiteDisjointUnionStatus true true false

completeFiniteDisjointUnionPasses : finiteDunOk completeFiniteDisjointUnion ≡ true
completeFiniteDisjointUnionPasses = refl

componentNotSubclassOfUnionFails : finiteDunOk missingSubclassEdge ≡ false
componentNotSubclassOfUnionFails = refl

unionExhaustivityFailureFails : finiteDunOk nonExhaustiveKnownUnion ≡ false
unionExhaustivityFailureFails = refl

pairwiseDisjointnessFailureFails : finiteDunOk overlappingMembers ≡ false
pairwiseDisjointnessFailureFails = refl

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
