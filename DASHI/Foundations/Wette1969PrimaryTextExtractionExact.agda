module DASHI.Foundations.Wette1969PrimaryTextExtractionExact where

------------------------------------------------------------------------
-- WETTE 1969 PRIMARY-TEXT EXTRACTION
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", in Foundations of Mathematics: Symposium Papers Commemorating
-- the Sixtieth Birthday of Kurt Gödel, Springer, 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- This module records only source-visible structural facts and theorem CLAIMS.
-- It does not identify the historical calculus with any existing DASHI machine
-- and does not certify Wette's Hauptsatz proofs.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Exact source-visible finite-calculus data.
------------------------------------------------------------------------

record Wette1969CalculusSurface : Set where
  constructor wette1969CalculusSurface
  field
    constants : Nat
    functors : Nat
    initialRelators : Nat
    initialRuleCount : Nat
    modifiedRelators : Nat
    modifiedRuleCount : Nat
    alternateModifiedRelators : Nat
    alternateModifiedRuleCount : Nat
    mainRulePremises : Nat

open Wette1969CalculusSurface public

-- Printed pp. 142--146 give the initial specification and 98-rule presentation.
-- The Zusatz on pp. 193--194 changes premise 6 of rule 9.1.5, adds the unary
-- relator _A with six rules, and states the final counts 97 / 129.
canonicalWette1969CalculusSurface : Wette1969CalculusSurface
canonicalWette1969CalculusSurface =
  wette1969CalculusSurface
    7 8 15 98
    16 97
    17 129
    27

------------------------------------------------------------------------
-- Native completeness vocabulary in the primary text.
------------------------------------------------------------------------

data WetteCompletenessKind : Set where
  transfiniteCompleteness : WetteCompletenessKind
  exorbitantCompleteness : WetteCompletenessKind

record Wette1969CompletenessClaim : Set where
  constructor wette1969CompletenessClaim
  field
    kind : WetteCompletenessKind
    printedPage : Nat
    finiteProcedureClaimed : Bool
    sourceIsDeductionLevel : Bool
    targetIsConstructiveSphereG1 : Bool
    replacementAndCardinalSchemasIncluded : Bool
    substitutionRegionDependsOnSourceDeduction : Bool

open Wette1969CompletenessClaim public

-- Hauptsatz 1, printed p. 178:
-- every deduction in Takeuti-style classical ordinal arithmetic WITHOUT the
-- replacement/cardinal-number axiom schemata is claimed to map, by a finite
-- translation procedure, to a deduction in G1.
hauptsatz1Claim : Wette1969CompletenessClaim
hauptsatz1Claim =
  wette1969CompletenessClaim
    transfiniteCompleteness
    178
    true true true
    false
    false

-- Hauptsatz 2, printed p. 181:
-- every deduction in ZF-Skolem set theory / Takeuti classical ordinal theory
-- WITH replacement and cardinal-number schemata is claimed to be assigned a
-- deduction in G1 by a finite reinterpretation procedure.  Wette explicitly
-- says the substitution domain needed to solve the reinterpretation already
-- depends on the source deduction d<.
hauptsatz2Claim : Wette1969CompletenessClaim
hauptsatz2Claim =
  wette1969CompletenessClaim
    exorbitantCompleteness
    181
    true true true
    true
    true

------------------------------------------------------------------------
-- Source precision / addendum facts.
------------------------------------------------------------------------

record Wette1969SourcePrecisionBoundary : Set where
  constructor wette1969SourcePrecisionBoundary
  field
    pureCalculusExplicitlyListed : Bool
    pureCalculusExplicitlyListedIsTrue :
      pureCalculusExplicitlyListed ≡ true

    intendedInterpretationKeptSeparateFromPureCalculus : Bool
    intendedInterpretationKeptSeparateFromPureCalculusIsTrue :
      intendedInterpretationKeptSeparateFromPureCalculus ≡ true

    appendixAdvertisesLowerPrecisionThanCalculusSection : Bool
    appendixAdvertisesLowerPrecisionThanCalculusSectionIsTrue :
      appendixAdvertisesLowerPrecisionThanCalculusSection ≡ true

    hauptsatz2SubstitutionDomainIsDeductionDependent : Bool
    hauptsatz2SubstitutionDomainIsDeductionDependentIsTrue :
      hauptsatz2SubstitutionDomainIsDeductionDependent ≡ true

    hauptsatzClaimsAreKernelCheckedHere : Bool
    hauptsatzClaimsAreKernelCheckedHereIsFalse :
      hauptsatzClaimsAreKernelCheckedHere ≡ false

    historicalRuleSetFullyTranscribedIntoAgda : Bool
    historicalRuleSetFullyTranscribedIntoAgdaIsFalse :
      historicalRuleSetFullyTranscribedIntoAgda ≡ false

canonicalWette1969SourcePrecisionBoundary : Wette1969SourcePrecisionBoundary
canonicalWette1969SourcePrecisionBoundary =
  wette1969SourcePrecisionBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
