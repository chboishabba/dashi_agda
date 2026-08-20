module DASHI.Ontology.RdfViewInformationOrderJMDBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge using (LeanTheoremContract)
open import DASHI.Ontology.LeanWikidataLatestEpistemicConformanceBridge

jmdReifiedDeterminesDirect : LeanTheoremContract
jmdReifiedDeterminesDirect = jmdReifiedDeterminesDirectRdf

jmdDirectDoesNotDetermineReified : LeanTheoremContract
jmdDirectDoesNotDetermineReified = jmdDirectDoesNotDetermineReifiedRdf

record ReifiedStatementWitness : Set where
  constructor reifiedStatementWitness
  field
    directTruthValue : Bool
    preferredRank : Bool
open ReifiedStatementWitness public

DirectStatementWitness : Set
DirectStatementWitness = Bool

directView : ReifiedStatementWitness → DirectStatementWitness
directView statement = directTruthValue statement

normalRankStatement : ReifiedStatementWitness
normalRankStatement = reifiedStatementWitness true false

preferredRankStatement : ReifiedStatementWitness
preferredRankStatement = reifiedStatementWitness true true

sameDirectDifferentReification : directView normalRankStatement ≡ directView preferredRankStatement
sameDirectDifferentReification = refl

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

reifiedStatesAreDistinct : normalRankStatement ≡ preferredRankStatement → ⊥
reifiedStatesAreDistinct equality = falseNotTrue (cong preferredRank equality)

record ExactDirectReconstruction : Set where
  constructor exactDirectReconstruction
  field
    reconstruct : DirectStatementWitness → ReifiedStatementWitness
    exact : (statement : ReifiedStatementWitness) → reconstruct (directView statement) ≡ statement
open ExactDirectReconstruction public

noExactDirectReconstruction : ExactDirectReconstruction → ⊥
noExactDirectReconstruction reconstruction =
  reifiedStatesAreDistinct
    (trans (sym (exact reconstruction normalRankStatement))
           (exact reconstruction preferredRankStatement))

record RdfViewInformationBoundary : Set where
  constructor rdfViewInformationBoundary
  field
    reifiedDeterminesDirect : Bool
    directDeterminesReified : Bool
    oneWayDeterminationImpliesTwoSidedEquivalence : Bool

canonicalRdfViewInformationBoundary : RdfViewInformationBoundary
canonicalRdfViewInformationBoundary = rdfViewInformationBoundary true false false
