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

rosser1936 : Source.AttributedSource
rosser1936 =
  Source.mkDOISource
    "Barkley Rosser"
    "Extensions of Some Theorems of Gödel and Church"
    "The Journal of Symbolic Logic 1(3), 87–91"
    "1936"
    "10.2307/2269028"
    "https://doi.org/10.2307/2269028"
    Source.academicArticleSource
    "primary source for the Rosser strengthening; its consistency hypotheses and modified sentence remain distinct from the ordinary Gödel sentence"
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

tarski1936 : Source.AttributedSource
tarski1936 =
  Source.mkNoDOISource
    "Alfred Tarski"
    "Der Wahrheitsbegriff in den formalisierten Sprachen"
    "Studia Philosophica 1, 261–405"
    "1936"
    ""
    Source.academicArticleSource
    "primary publication carrier for the formal-truth work; the German publication is in volume 1 (1936), with a reprint/offprint dated 1935; no DOI is asserted here"
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

church1936 : Source.AttributedSource
church1936 =
  Source.mkDOISource
    "Alonzo Church"
    "An Unsolvable Problem of Elementary Number Theory"
    "American Journal of Mathematics 58(2), 345–363"
    "1936"
    "10.2307/2371045"
    "https://doi.org/10.2307/2371045"
    Source.academicArticleSource
    "primary source for Church's undecidability result and effective-calculability formulation"
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
    "primary source for general recursive-function machinery"
    Source.publicAttribution

kleene1938 : Source.AttributedSource
kleene1938 =
  Source.mkDOISource
    "S. C. Kleene"
    "On Notation for Ordinal Numbers"
    "The Journal of Symbolic Logic 3(4), 150–155"
    "1938"
    "10.2307/2267778"
    "https://doi.org/10.2307/2267778"
    Source.academicArticleSource
    "primary historical source attached to the recursion/fixed-point theorem family; theorem statement still requires local source alignment"
    Source.publicAttribution

namedLimitsSourceAtlas : Source.AttributedSourceAtlas
namedLimitsSourceAtlas =
  Source.mkSourceAtlas
    "Gödel/Turing named limits source atlas"
    "DASHI.ComputerScience.GodelTuringNamedLimitsSourceStatusAtlasExact"
    (godel1931 ∷ rosser1936 ∷ lob1955 ∷ tarski1936 ∷ turing1936 ∷ church1936 ∷ rice1953 ∷ rado1962 ∷ kleene1936 ∷ kleene1938 ∷ [])
    "original-source identities for the named formal-limits lane; source identity does not transport theorem proof or exact local hypotheses"

------------------------------------------------------------------------
-- WHAT IS ALREADY IN-REPO?
------------------------------------------------------------------------

data FormalisationStatus : Set where
  implementedExecutableSubstrate
  implementedGenericCompiler
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
  rosserFirstIncompleteness
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
status arithmetisedSubstitution = implementedGenericCompiler
status representabilityOfProofRelation = sourceEstablishedUnformalised
status diagonalFixedPointLemma = implementedGenericCompiler
status godelFirstIncompleteness = typedContractOnly
status rosserFirstIncompleteness = typedContractOnly
status hilbertBernaysDerivabilityConditions = typedContractOnly
status godelSecondIncompleteness = typedContractOnly
status lobTheorem = typedContractOnly
status tarskiUndefinability = typedContractOnly
status churchEntscheidungsproblem = sourceEstablishedUnformalised
status turingHaltingUndecidability = sourceEstablishedUnformalised
status kleeneRecursionFixedPoint = sourceEstablishedUnformalised
status riceTheorem = sourceEstablishedUnformalised
status busyBeaverNoncomputability = sourceEstablishedUnformalised

------------------------------------------------------------------------
-- EXISTING SUBSTRATE RECEIPT
--
-- GodelLattice already owns abstract Text -> Nat/factor-vector contracts.
-- GodelScalarization owns an executable prime-exponent FactorVec -> Nat map.
-- The current branch additionally owns generic compilers from a concrete
-- formula-code retraction to ArithmetisedSubstitution and from a concrete
-- DiagonalFormulaConstruction to DiagonalLemmaAuthority.  Concrete arithmetic
-- inhabitants remain open.
------------------------------------------------------------------------

record ExistingGodelSubstrateReceipt : Set where
  constructor existingGodelSubstrateReceipt
  field
    abstractTextEncodingContractExists : Bool
    executableFactorVectorScalarisationExists : Bool
    genericSubstitutionCompilerExists : Bool
    concreteFormulaCodeRetractionExists : Bool
    genericDiagonalCompilerExists : Bool
    concreteSelfSubstitutionRepresentabilityExists : Bool
    proofPredicateExistsHere : Bool
    incompletenessTheoremExistsHere : Bool

canonicalExistingGodelSubstrateReceipt : ExistingGodelSubstrateReceipt
canonicalExistingGodelSubstrateReceipt =
  existingGodelSubstrateReceipt
    true true true false true false false false

------------------------------------------------------------------------
-- DEPENDENCY COORDINATES
------------------------------------------------------------------------

data RequiredCoordinate : Set where
  syntaxCarrier
  godelCode
  formulaCodeRetraction
  numeralQuotation
  substitutionOnCodes
  selfSubstitutionRepresentability
  proofRelation
  proofRelationRepresentability
  provabilityPredicate
  diagonalFixedPoint
  consistencyHypothesis
  strongerOrdinaryGodelUnrefutabilityHypothesis
  rosserSentenceConstruction
  derivabilityConditions
  truthDefinitionCandidate
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

arithmetisedSubstitutionDependency : ProblemDependency
arithmetisedSubstitutionDependency =
  problemDependency arithmetisedSubstitution
    (syntaxCarrier ∷ godelCode ∷ formulaCodeRetraction ∷ numeralQuotation ∷ [])

diagonalDependency : ProblemDependency
diagonalDependency =
  problemDependency diagonalFixedPointLemma
    (syntaxCarrier ∷ godelCode ∷ formulaCodeRetraction ∷ numeralQuotation ∷
     substitutionOnCodes ∷ selfSubstitutionRepresentability ∷ [])

godelIDependency : ProblemDependency
godelIDependency =
  problemDependency godelFirstIncompleteness
    (syntaxCarrier ∷ godelCode ∷ substitutionOnCodes ∷ proofRelation ∷
     proofRelationRepresentability ∷ provabilityPredicate ∷ diagonalFixedPoint ∷
     consistencyHypothesis ∷ strongerOrdinaryGodelUnrefutabilityHypothesis ∷ [])

rosserIDependency : ProblemDependency
rosserIDependency =
  problemDependency rosserFirstIncompleteness
    (syntaxCarrier ∷ godelCode ∷ substitutionOnCodes ∷ proofRelation ∷
     proofRelationRepresentability ∷ provabilityPredicate ∷ diagonalFixedPoint ∷
     consistencyHypothesis ∷ rosserSentenceConstruction ∷ [])

godelIIDependency : ProblemDependency
godelIIDependency =
  problemDependency godelSecondIncompleteness
    (provabilityPredicate ∷ diagonalFixedPoint ∷ derivabilityConditions ∷
     consistencyHypothesis ∷ [])

lobDependency : ProblemDependency
lobDependency =
  problemDependency lobTheorem
    (provabilityPredicate ∷ diagonalFixedPoint ∷ derivabilityConditions ∷ [])

tarskiDependency : ProblemDependency
tarskiDependency =
  problemDependency tarskiUndefinability
    (syntaxCarrier ∷ godelCode ∷ diagonalFixedPoint ∷ truthDefinitionCandidate ∷ [])

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
data FormulaRetractionImpliesRepresentability : Set where
data OrdinaryGodelSentenceEqualsRosserSentence : Set where
data FiniteBusyBeaverImpliesUniversalBusyBeaver : Set where
data BoundedHaltingDeciderImpliesUniversalHaltingDecider : Set where
data TernaryDecisionCarrierImpliesIncompleteness : Set where

godelNumberingDoesNotSupplyDiagonalLemma :
  GodelNumberingImpliesDiagonalLemma → ⊥
godelNumberingDoesNotSupplyDiagonalLemma ()

formulaRetractionDoesNotSupplyInternalRepresentability :
  FormulaRetractionImpliesRepresentability → ⊥
formulaRetractionDoesNotSupplyInternalRepresentability ()

ordinaryGodelSentenceIsNotDefinitionallyRosserSentence :
  OrdinaryGodelSentenceEqualsRosserSentence → ⊥
ordinaryGodelSentenceIsNotDefinitionallyRosserSentence ()

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
    genericSubstitutionCompilerPresent : Bool
    concreteFormulaRetractionPresent : Bool
    genericDiagonalCompilerPresent : Bool
    concreteDiagonalRepresentabilityPresent : Bool
    godelIAlreadyPresent : Bool
    rosserKeptDistinctFromOrdinaryGodel : Bool
    tarskiSourceMetadataPresent : Bool
    universalHaltingAlreadyPresent : Bool
    finiteAnaloguesMayBeReused : Bool
    theoremSourcesAreNotProofImports : Bool

canonicalGodelTuringNamedLimitsBoundary : GodelTuringNamedLimitsBoundary
canonicalGodelTuringNamedLimitsBoundary =
  godelTuringNamedLimitsBoundary
    true true true false true false false true true false true true
