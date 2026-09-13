module DASHI.Wikimedia.IbrahimMonster3B729ExtensionFiniteFieldProducerSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BSuzukiQuotientDescentCorrectionExact as Descent

------------------------------------------------------------------------
-- BARRACLOUGH SECTION 5.3: THE 729-EXTENSION PRODUCER
--
-- Primary computational route recovered from Richard William Barraclough,
-- "Some Calculations Related To The Monster Group", PhD thesis, University of
-- Birmingham, September 2005, Section 5.3.
--
-- Source-paid statements:
--
--   * the two degree-729 irreducible representations of 3^(1+12) extend to
--       3^(1+12):6.Suz;
--   * the outer involution fuses them to a degree-1458 representation in
--       3^(1+12):6.Suz:2;
--   * construction over F_31 allows eigenvalues to be lifted to C and hence
--       determines values of the degree-729 characters;
--   * independent constructions over F_103 and F_223 constrain / determine
--       the rational degree-1458 fused character;
--   * the 3-part of the centre of 6.Suz is represented trivially in the fused
--       1458 construction as stated in the thesis.
--
-- This owner makes those computational roles explicit.  It does NOT pretend a
-- citation is an executed matrix construction, and it does NOT identify an
-- arbitrary degree-729 Irr(6.Suz) object.  The 729 character belongs to the
-- inertia extension 3^(1+12):6.Suz.
------------------------------------------------------------------------

heisenbergDegree : Nat
heisenbergDegree = 729

fusedDegree : Nat
fusedDegree = 2 * heisenbergDegree

fusedDegreeIs1458 : fusedDegree ≡ 1458
fusedDegreeIs1458 = refl

fieldForComplexEigenvalueLift : Nat
fieldForComplexEigenvalueLift = 31

firstRationalCrossCheckField : Nat
firstRationalCrossCheckField = 103

secondRationalCrossCheckField : Nat
secondRationalCrossCheckField = 223

------------------------------------------------------------------------
-- 1. Attribution / source roles.
------------------------------------------------------------------------

barracloughThesis : Attribution.AttributedSource
barracloughThesis = Attribution.mkNoDOISource
  "Richard William Barraclough"
  "Some Calculations Related To The Monster Group"
  "PhD thesis, University of Birmingham"
  "September 2005"
  "https://webspace.maths.qmul.ac.uk/r.a.wilson/RWBphd.pdf"
  (Attribution.namedSourceKind "primary computational thesis")
  "primary source for the Section 5.3 finite-field construction of the degree-729 inertia representations; no DOI located/asserted for the thesis"
  Attribution.publicAttribution

barracloughThesisAttribution =
  Snowball.canonicalSourceRoleSnowballReceipt barracloughThesis

publishedTablePaper : Attribution.AttributedSource
publishedTablePaper = Descent.paperSource

publishedTablePaperAttribution =
  Snowball.canonicalSourceRoleSnowballReceipt publishedTablePaper

paperDOI : String
paperDOI = "10.1112/S1461157000001352"

magmaProducerSource : Attribution.AttributedSource
magmaProducerSource = Attribution.mkNoDOISource
  "Computational Algebra Group, University of Sydney; Magma contributors"
  "Magma computational algebra system"
  "software system used in Barraclough Section 5.3"
  "historical computational dependency"
  "https://magma.maths.usyd.edu.au/magma/"
  (Attribution.namedSourceKind "computational algebra software")
  "software producer role only; no DOI asserted here and software identity does not itself certify Barraclough's exact historical matrices or outputs"
  Attribution.publicAttribution

magmaProducerAttribution =
  Snowball.canonicalSourceRoleSnowballReceipt magmaProducerSource

record ExtensionProducerExternalCoordinates : Set where
  constructor extension-producer-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    thesisSpecificDewey : String
    thesisSpecificDeweyResolved : Bool
    oeisCoordinate : String
    oeisHasCharacterProducerAuthority : Bool
open ExtensionProducerExternalCoordinates public

canonicalExtensionProducerExternalCoordinates : ExtensionProducerExternalCoordinates
canonicalExtensionProducerExternalCoordinates =
  extension-producer-external-coordinates
    "Q1055807"
    "Q600043"
    "Q1057968"
    "512.22"
    "512.23"
    "unresolved"
    false
    "not applicable: 729=3^6 is numerical context only; no OEIS entry is allowed to stand in for the inertia representation or finite-field reconstruction"
    false

------------------------------------------------------------------------
-- 2. Exact source-described producer stages.
------------------------------------------------------------------------

data ProducerFieldRole : Set where
  complexEigenvalueLiftField
  rationalFusedCharacterCrossCheckField : ProducerFieldRole

record FiniteFieldRepresentationRun : Set₁ where
  constructor finite-field-representation-run
  field
    fieldSize : Nat
    role : ProducerFieldRole
    inertiaRepresentationConstructed : Set
    generatorWordsAlignedAcrossRepresentations : Set
    traceOrEigenvalueDataProduced : Set

open FiniteFieldRepresentationRun public

record Degree729ComplexCharacterLift : Set₁ where
  constructor degree-729-complex-character-lift
  field
    f31Run : FiniteFieldRepresentationRun
    f31FieldExact : fieldSize f31Run ≡ 31
    eigenvaluesLiftedToComplex : Set
    degree729CharacterValuesRecovered : Set

open Degree729ComplexCharacterLift public

record Fused1458RationalCharacterCrossCheck : Set₁ where
  constructor fused-1458-rational-character-cross-check
  field
    f103Run : FiniteFieldRepresentationRun
    f223Run : FiniteFieldRepresentationRun
    f103FieldExact : fieldSize f103Run ≡ 103
    f223FieldExact : fieldSize f223Run ≡ 223
    rational1458CharacterRecovered : Set
    agreesWithComplexConjugate729Pair : Set

open Fused1458RationalCharacterCrossCheck public

record Barraclough729ExtensionProducer : Set₁ where
  constructor barraclough-729-extension-producer
  field
    complexLift : Degree729ComplexCharacterLift
    rationalCrossCheck : Fused1458RationalCharacterCrossCheck
    sourceNativeInertiaActor : Set
    degree729ExtensionToThreeOnePlusTwelveSixSuz : Set
    outerFusionToDegree1458 : Set
    publishedMainTable1458SameCharacter : Set

open Barraclough729ExtensionProducer public

------------------------------------------------------------------------
-- 3. Bidi same-object requirement.
--
-- We now have two potential producers of the same 1458 character:
--   historical Section-5.3 finite-field reconstruction;
--   published / CTblLib main-table irreducible row.
-- Neither is allowed to replace the other by degree alone.
------------------------------------------------------------------------

record MainTable1458CharacterMatch : Set₁ where
  constructor main-table-1458-character-match
  field
    historicalProducer : Barraclough729ExtensionProducer
    mainTableCharacterPosition : Nat
    mainTableCharacterDegree : Nat
    mainTableDegreeIs1458 : mainTableCharacterDegree ≡ 1458
    fullClassFunctionEquality : Set
    sourceClassOrderingAligned : Set

open MainTable1458CharacterMatch public

------------------------------------------------------------------------
-- 4. Non-promotion boundaries.
------------------------------------------------------------------------

data Number729CreatesInertiaRepresentation : Set where
data Field31CreatesComplexCharacter : Set where
data Rational1458Creates729PhaseSplit : Set where
data MainTableDegree1458CreatesHistoricalProducerIdentity : Set where
data ThesisCitationCreatesExecutionReceipt : Set where

number729DoesNotCreateRepresentation : Number729CreatesInertiaRepresentation → ⊥
number729DoesNotCreateRepresentation ()

field31DoesNotCreateComplexCharacter : Field31CreatesComplexCharacter → ⊥
field31DoesNotCreateComplexCharacter ()

rational1458DoesNotCreatePhaseSplit : Rational1458Creates729PhaseSplit → ⊥
rational1458DoesNotCreatePhaseSplit ()

mainTableDegreeDoesNotCreateHistoricalIdentity :
  MainTableDegree1458CreatesHistoricalProducerIdentity → ⊥
mainTableDegreeDoesNotCreateHistoricalIdentity ()

thesisCitationDoesNotCreateExecutionReceipt : ThesisCitationCreatesExecutionReceipt → ⊥
thesisCitationDoesNotCreateExecutionReceipt ()

------------------------------------------------------------------------
-- 5. Highest-alpha frontier.
------------------------------------------------------------------------

record Extension729ProducerFrontier : Set where
  constructor extension-729-producer-frontier
  field
    thesisPrimarySourceLocated : Bool
    thesisDOIResolved : Bool
    section53F31ComplexLiftRoutePaid : Bool
    section53F103F223RationalCrossCheckRoutePaid : Bool
    inertiaActorIdentityPaidAtSourceLevel : Bool
    fused1458SourceStatementPaid : Bool
    exactHistoricalMagmaArtifactsLocated : Bool
    finiteFieldProducerReexecuted : Bool
    exactPublishedMainTable1458RowPaid : Bool
    historicalToMainTableFullCharacterMatchPaid : Bool
    actual729ExtensionCharacterProducerPaid : Bool
    nextResidual : String
open Extension729ProducerFrontier public

currentExtension729ProducerFrontier : Extension729ProducerFrontier
currentExtension729ProducerFrontier =
  extension-729-producer-frontier
    true false true true true true
    false false false false false
    "locate or reconstruct the exact degree-1458 main-table irreducible corresponding to the fused pair of Barraclough Section-5.3 degree-729 extensions, and pay it by full class-function identity rather than degree. Prefer recovered primary supplementary/main-table data or an exact CTblLib row. If historical F31/F103/F223 matrix artifacts surface, retain them append-only and compare their reconstructed character against the same row. Once the 1458 character is same-object paid, combine it with the exact 12a/12b and 78a/78b Suzuki candidate families and the qGtoN3B quotient map; let full character equality decide quotient-compatible labels and phase convention."
