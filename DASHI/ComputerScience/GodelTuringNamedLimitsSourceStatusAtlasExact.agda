module DASHI.ComputerScience.GodelTuringNamedLimitsSourceStatusAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import Ontology.GodelLattice as GodelLattice
import Ontology.GodelScalarization as GodelScalarization

------------------------------------------------------------------------
-- SOURCE-ATTRIBUTED NAMED LIMITS ATLAS
--
-- This module is an audit/status owner, not a proof of the named theorems.
-- It records which ingredients already exist in-repo and which theorem-level
-- contracts remain to be supplied.  Source citation does not import proof.
------------------------------------------------------------------------

godel1931 : Source.AttributedSource
godel1931 =
  Source.mkDOISource
    "Kurt Gödel"
    "Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I"
    "Monatshefte für Mathematik und Physik 38, 173–198"
    "1931"
    "10.1007/BF01700692"
    "https://doi.org/10.1007/BF01700692"
    Source.academicArticleSource
    "primary source for arithmetisation and the incompleteness results; citation does not instantiate the local theorem contracts"
    Source.publicAttribution

lob1955 : Source.AttributedSource
lob1955 =
  Source.mkDOISource
    "M. H. Löb"
    "Solution of a Problem of Leon Henkin"
    "The Journal of Symbolic Logic 20(2), 115–118"
    "1955"
    "10.2307/2266895"
    "https://doi.org/10.2307/2266895"
    Source.academicArticleSource
    "primary source for the provability theorem now called Löb's theorem"
    Source.publicAttribution

turing1936 : Source.AttributedSource
turing1936 =
  Source.mkNoDOISource
    "Alan M. Turing"
    "On Computable Numbers, with an Application to the Entscheidungsproblem"
    "Proceedings of the London Mathematical Society (2) 42, 230–265"
    "1936"
    "https://www.turing.org.uk/sources/biblio4.html"
    Source.academicArticleSource
    "primary historical source identity for universal computation/undecidability; URL is a bibliographic carrier, not a proof import"
    Source.publicAttribution

rice1953 : Source.AttributedSource
rice1953 =
  Source.mkDOISource
    "H. G. Rice"
    "Classes of Recursively Enumerable Sets and Their Decision Problems"
    "Transactions of the American Mathematical Society 74(2), 358–366"
    "1953"
    "10.1090/S0002-9947-1953-0053041-6"
    "https://doi.org/10.1090/S0002-9947-1953-0053041-6"
    Source.academicArticleSource
    "primary source for the nontrivial semantic-property undecidability theorem"
    Source.publicAttribution

rado1962 : Source.AttributedSource
rado1962 =
  Source.mkDOISource
    "Tibor Radó"
    "On Non-Computable Functions"
    "Bell System Technical Journal 41(3), 877–884"
    "1962"
    "10.1002/j.1538-7305.1962.tb00480.x"
    "https://doi.org/10.1002/j.1538-7305.1962.tb00480.x"
    Source.academicArticleSource
    "primary source for the Busy Beaver non-computable-function construction"
    Source.publicAttribution

kleene1936 : Source.AttributedSource
kleene1936 =
  Source.mkDOISource
    "S. C. Kleene"
    "General Recursive Functions of Natural Numbers"
    "Mathematische Annalen 112, 727–742"
    "1936"
    "10.1007/BF01565439"
    "https://doi.org/10.1007/BF01565439"
    Source.academicArticleSource
    "primary source for general recursive-function machinery used by later fixed-point/recursion-theorem developments"
    Source.publicAttribution

namedLimitsSourceAtlas : Source.AttributedSourceAtlas
namedLimitsSourceAtlas =
  Source.mkSourceAtlas
    "Gödel/Turing named limits source atlas"
    "DASHI.ComputerScience.GodelTuringNamedLimitsSourceStatusAtlasExact"
    (godel1931 ∷ lob1955 ∷ turing1936 ∷ rice1953 ∷ rado1962 ∷ kleene1936 ∷ [])
    "original-source identities for the named formal limits lane; Tarski/Church and later fixed-point source additions remain explicit acquisition extensions rather than fabricated metadata"

------------------------------------------------------------------------
-- WHAT IS ALREADY IN-REPO?
------------------------------------------------------------------------

data FormalisationStatus : Set where
  implementedExecutableSubstrate
  implementedFiniteAnalogue
  typedContractOnly
  sourceEstablishedUnformalised
  sourceMetadataPending
  notClaimed : FormalisationStatus

data NamedLimitProblem : Set where
  godelNumbering
  arithmetisedSubstitution
  representabilityOfProofRelation
  diagonalFixedPointLemma
  godelFirstIncompleteness
  hilbertBernaysDerivabilityConditions
  godelSecondIncompleteness
  lobTheorem
  tarskiUndefinability
  churchEntscheidungsproblem
  turingHaltingUndecidability
  kleeneRecursionFixedPoint
  riceTheorem
  busyBeaverNoncomputability : NamedLimitProblem

status : NamedLimitProblem → FormalisationStatus
status godelNumbering = implementedExecutableSubstrate
status arithmetisedSubstitution = sourceEstablishedUnformalised
status representabilityOfProofRelation = sourceEstablishedUnformalised
status diagonalFixedPointLemma = sourceEstablishedUnformalised
status godelFirstIncompleteness = sourceEstablishedUnformalised
status hilbertBernaysDerivabilityConditions = sourceEstablishedUnformalised
status godelSecondIncompleteness = sourceEstablishedUnformalised
status lobTheorem = sourceEstablishedUnformalised
status tarskiUndefinability = sourceEstablishedUnformalised
status churchEntscheidungsproblem = sourceMetadataPending
status turingHaltingUndecidability = sourceEstablishedUnformalised
status kleeneRecursionFixedPoint = sourceEstablishedUnformalised
status riceTheorem = sourceEstablishedUnformalised
status busyBeaverNoncomputability = sourceEstablishedUnformalised

------------------------------------------------------------------------
-- EXISTING SUBSTRATE RECEIPT
--
-- GodelLattice already owns abstract Text -> Nat/factor-vector contracts.
-- GodelScalarization owns an executable prime-exponent FactorVec -> Nat map.
-- Neither module supplies arithmetised substitution, a proof predicate, or a
-- diagonal/fixed-point theorem.  Those are separate required coordinates.
------------------------------------------------------------------------

record ExistingGodelSubstrateReceipt : Set where
  constructor existingGodelSubstrateReceipt
  field
    abstractTextEncodingContractExists : Bool
    executableFactorVectorScalarisationExists : Bool
    substitutionOperationExistsHere : Bool
    proofPredicateExistsHere : Bool
    diagonalLemmaExistsHere : Bool
    incompletenessTheoremExistsHere : Bool

canonicalExistingGodelSubstrateReceipt : ExistingGodelSubstrateReceipt
canonicalExistingGodelSubstrateReceipt =
  existingGodelSubstrateReceipt
    true true false false false false

------------------------------------------------------------------------
-- DEPENDENCY COORDINATES
------------------------------------------------------------------------

data RequiredCoordinate : Set where
  syntaxCarrier
  godelCode
  numeralQuotation
  substitutionOnCodes
  proofRelation
  proofRelationRepresentability
  provabilityPredicate
  diagonalFixedPoint
  consistencyHypothesis
  derivabilityConditions
  universalComputationEncoding
  selfApplicationEncoding
  nontrivialSemanticProperty
  finiteMachineEnumeration
  terminatingRuntimeMaximum : RequiredCoordinate

record ProblemDependency : Set where
  constructor problemDependency
  field
    problem : NamedLimitProblem
    coordinates : List RequiredCoordinate

open ProblemDependency public

diagonalDependency : ProblemDependency
diagonalDependency =
  problemDependency diagonalFixedPointLemma
    (syntaxCarrier ∷ godelCode ∷ numeralQuotation ∷ substitutionOnCodes ∷ [])

godelIDependency : ProblemDependency
godelIDependency =
  problemDependency godelFirstIncompleteness
    (syntaxCarrier ∷ godelCode ∷ substitutionOnCodes ∷ proofRelation ∷
     proofRelationRepresentability ∷ provabilityPredicate ∷ diagonalFixedPoint ∷
     consistencyHypothesis ∷ [])

godelIIDependency : ProblemDependency
godelIIDependency =
  problemDependency godelSecondIncompleteness
    (provabilityPredicate ∷ diagonalFixedPoint ∷ derivabilityConditions ∷
     consistencyHypothesis ∷ [])

lobDependency : ProblemDependency
lobDependency =
  problemDependency lobTheorem
    (provabilityPredicate ∷ diagonalFixedPoint ∷ derivabilityConditions ∷ [])

turingDependency : ProblemDependency
turingDependency =
  problemDependency turingHaltingUndecidability
    (universalComputationEncoding ∷ selfApplicationEncoding ∷ [])

riceDependency : ProblemDependency
riceDependency =
  problemDependency riceTheorem
    (universalComputationEncoding ∷ nontrivialSemanticProperty ∷ [])

busyBeaverDependency : ProblemDependency
busyBeaverDependency =
  problemDependency busyBeaverNoncomputability
    (universalComputationEncoding ∷ finiteMachineEnumeration ∷
     terminatingRuntimeMaximum ∷ [])

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data GodelNumberingImpliesDiagonalLemma : Set where
data FiniteBusyBeaverImpliesUniversalBusyBeaver : Set where
data BoundedHaltingDeciderImpliesUniversalHaltingDecider : Set where
data TernaryDecisionCarrierImpliesIncompleteness : Set where

godelNumberingDoesNotSupplyDiagonalLemma :
  GodelNumberingImpliesDiagonalLemma → ⊥
godelNumberingDoesNotSupplyDiagonalLemma ()

finiteBusyBeaverDoesNotSupplyUniversalBusyBeaver :
  FiniteBusyBeaverImpliesUniversalBusyBeaver → ⊥
finiteBusyBeaverDoesNotSupplyUniversalBusyBeaver ()

boundedHaltingDoesNotSupplyUniversalHalting :
  BoundedHaltingDeciderImpliesUniversalHaltingDecider → ⊥
boundedHaltingDoesNotSupplyUniversalHalting ()

ternaryDecisionDoesNotSupplyGodel :
  TernaryDecisionCarrierImpliesIncompleteness → ⊥
ternaryDecisionDoesNotSupplyGodel ()

record GodelTuringNamedLimitsBoundary : Set where
  constructor godelTuringNamedLimitsBoundary
  field
    godelNumberingAlreadyPresent : Bool
    executableScalarisationAlreadyPresent : Bool
    diagonalLemmaAlreadyPresent : Bool
    godelIAlreadyPresent : Bool
    universalHaltingAlreadyPresent : Bool
    finiteAnaloguesMayBeReused : Bool
    theoremSourcesAreNotProofImports : Bool

canonicalGodelTuringNamedLimitsBoundary : GodelTuringNamedLimitsBoundary
canonicalGodelTuringNamedLimitsBoundary =
  godelTuringNamedLimitsBoundary true true false false false true true
