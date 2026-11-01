module DASHI.Analysis.CubicalHoTTRealBackendBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Experimental backend provenance and non-promotion boundary.
--
-- Jackson Brough, "Formalizing the Real Numbers in Homotopy Type Theory with
-- Cubical Agda", Senior Honors Thesis, University of Utah, April 2026.
-- arXiv:2604.24782.  No DOI was assigned to the thesis.
--
-- Andrea Vezzosi, Anders Mörtberg and Andreas Abel,
-- "Cubical Agda: A Dependently Typed Programming Language with Univalence and
-- Higher Inductive Types", Proceedings of the ACM on Programming Languages 3,
-- ICFP (2019). DOI: 10.1145/3341691.
--
-- Gaëtan Gilbert, "Formalising Real Numbers in Homotopy Type Theory",
-- CPP 2017, pp. 112--124. DOI: 10.1145/3018610.3018614.
--
-- Russell O'Connor, "A Monadic, Functional Implementation of Real Numbers",
-- Mathematical Structures in Computer Science 17 (2007), 129--159.
-- DOI: 10.1017/S0960129506005871.
--
-- Nicolai Kraus, "The General Universal Property of the Propositional
-- Truncation", TYPES 2014. DOI: 10.4230/LIPIcs.TYPES.2014.111.
------------------------------------------------------------------------

-- Current Dashi backend policy:
--
-- * Bishop/Murray is the constructive ordered-real authority for the
--   migrated Dashi slice and is used as the semantic embedding target.
-- * Proof-critical estimates should remain in normalized ℚ whenever they
--   are rationalizable; embed the resulting certificate only afterward.
-- * Deeply composed native Bishop-real evaluation is not assumed efficient.
--   Future archetypes must be classified as rationalizable, fixed algebraic,
--   general analytic, or proof-only abstract before choosing a backend.
-- * Cubical/HoTT reals are a comparative prototype lane, not a replacement
--   dependency for the current theorem graph.
--
-- These performance and backend-scope observations do not block the Bishop
-- Agda 2.9 migration.  For the migration itself, inspect ℚᵘ directly rather
-- than inferring it from normalized ℚ: the ℚᵘ properties API supplies the
-- propositional absolute-value idempotence used by K-abs, and reconstruction
-- may be judgmental when the constructor and projections genuinely match.
-- Bishop commit d732b0340d729b264227a70fcf38383d8fb3ac3c now closes this
-- particular K-abs/index seam; common-index transport remains a future
-- fallback rather than a requirement for the absolute-product theorem.

record CubicalHoTTRealSourceReceipt : Set where
  field
    author : String
    title : String
    arXiv : String
    repository : String
    moduleCount : Nat
    approximateLineCount : Nat
    higherInductiveInductiveDefinition : Bool
    rationalArithmeticComputesDefinitionally : Bool
    reportedPostulateFree : Bool
    reportedHoleFree : Bool

open CubicalHoTTRealSourceReceipt public

broughHoTTRealReceipt : CubicalHoTTRealSourceReceipt
broughHoTTRealReceipt = record
  { author = "Jackson Brough"
  ; title = "Formalizing the Real Numbers in Homotopy Type Theory with Cubical Agda"
  ; arXiv = "2604.24782"
  ; repository = "utahplt/hott-reals"
  ; moduleCount = 33
  ; approximateLineCount = 13560
  ; higherInductiveInductiveDefinition = true
  ; rationalArithmeticComputesDefinitionally = true
  ; reportedPostulateFree = true
  ; reportedHoleFree = true
  }

record CubicalBackendCompatibilityBoundary : Set where
  field
    requiresCubicalAgda : Bool
    requiresCubicalLibrary : Bool
    requiresHigherInductiveTypes : Bool
    ordinaryAgdaDropInReplacement : Bool
    packagedCompleteOrderedFieldInterfacePresent : Bool
    formalInitialityTheoremPresent : Bool
    trigonometricSeriesLayerPresent : Bool
    locatorOrApproximationExtractionPresent : Bool
    safeToImportIntoCurrentYangMillsAggregate : Bool
    separateExperimentalBranchRecommended : Bool

open CubicalBackendCompatibilityBoundary public

currentCubicalBoundary : CubicalBackendCompatibilityBoundary
currentCubicalBoundary = record
  { requiresCubicalAgda = true
  ; requiresCubicalLibrary = true
  ; requiresHigherInductiveTypes = true
  ; ordinaryAgdaDropInReplacement = false
  ; packagedCompleteOrderedFieldInterfacePresent = false
  ; formalInitialityTheoremPresent = false
  ; trigonometricSeriesLayerPresent = false
  ; locatorOrApproximationExtractionPresent = false
  ; safeToImportIntoCurrentYangMillsAggregate = false
  ; separateExperimentalBranchRecommended = true
  }

record FutureHoTTBackendAdapter : Set₁ where
  field
    cubicalToolchainCompatibility : Set
    orderedCompleteRealPackaging : Set
    DASHISetoidBackendAdapter : Set
    rationalCertificateSeparation : Set
    agdaToLeanBoundaryReviewed : Set
    ordinaryAggregateIsolationProved : Set

open FutureHoTTBackendAdapter public

cubicalHoTTProvenanceLevel : ProofLevel
cubicalHoTTProvenanceLevel = machineChecked

cubicalHoTTBackendAdapterLevel : ProofLevel
cubicalHoTTBackendAdapterLevel = conditional
