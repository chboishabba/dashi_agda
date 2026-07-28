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
