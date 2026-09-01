module DASHI.Analysis.RiemannG2FkSelectedTestSameObjectBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact as Orbit
import DASHI.Analysis.RiemannG2FkOrbitExplicitFormulaWeldExact as Weld

------------------------------------------------------------------------
-- SELECTED fk SAME-OBJECT WELD
--
-- Cross-pollination from the Moonshine same-element pattern:
-- trace/character information and literal VOA state action are only combined
-- after both are forced to use the same Monster element.  Here the analogous
-- risk is using one embedded source test for provenance/admissibility and a
-- second (merely corresponding) Weil test for the explicit-formula response.
--
-- This owner removes that ambiguity.  One literal selected Test is simultaneously
--   * the image of the selected checked-source fk/window orbit;
--   * admissible in the canonical Weil space;
--   * the input of the same RiemannExplicitFormula arithmeticForm;
--   * the input of the same RiemannExplicitFormula spectralZeroForm.
------------------------------------------------------------------------

record SelectedFkSameObjectWeld
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (attachment : Orbit.FkOrbitConsumerAttachment space formula orbit)
    : Set₁ where
  private
    Test = Weil.WeilTestSpace.Test space

  field
    literalSelectedTest : Test

    literalSelectedTestIsEmbeddedSourceSelection :
      literalSelectedTest
      ≡ Orbit.FkOrbitConsumerAttachment.embedSourceTest attachment
          (Orbit.SourceFkOrbit.selectedSourceTest orbit)

    literalSelectedTestIsAttachmentSelection :
      literalSelectedTest
      ≡ Orbit.FkOrbitConsumerAttachment.selectedPoleTest attachment

    literalSelectedAdmissible :
      Weil.WeilTestSpace.admissible space literalSelectedTest

    sameSourceOrbitReference : String

open SelectedFkSameObjectWeld public

------------------------------------------------------------------------
-- Paired observation from the SAME literal selected test.
------------------------------------------------------------------------

record SelectedFkPairedObservation
    {space : Weil.WeilTestSpace}
    {formula : Explicit.RiemannExplicitFormula space}
    {orbit : Orbit.SourceFkOrbit}
    {attachment : Orbit.FkOrbitConsumerAttachment space formula orbit}
    (same : SelectedFkSameObjectWeld space formula orbit attachment)
    : Set where
  private
    Scalar = Weil.WeilTestSpace.Scalar space

  field
    arithmeticObservation : Scalar
    spectralObservation : Scalar

    arithmeticObservationIsLiteral :
      arithmeticObservation
      ≡ Explicit.RiemannExplicitFormula.arithmeticForm formula
          (literalSelectedTest same)

    spectralObservationIsLiteral :
      spectralObservation
      ≡ Explicit.RiemannExplicitFormula.spectralZeroForm formula
          (literalSelectedTest same)

open SelectedFkPairedObservation public

canonicalPairedObservation :
  ∀ {space formula orbit attachment} →
  (same : SelectedFkSameObjectWeld space formula orbit attachment) →
  SelectedFkPairedObservation same
canonicalPairedObservation {formula = formula} same = record
  { arithmeticObservation =
      Explicit.RiemannExplicitFormula.arithmeticForm formula
        (literalSelectedTest same)
  ; spectralObservation =
      Explicit.RiemannExplicitFormula.spectralZeroForm formula
        (literalSelectedTest same)
  ; arithmeticObservationIsLiteral = refl
  ; spectralObservationIsLiteral = refl
  }

------------------------------------------------------------------------
-- The canonical explicit formula relates the two coordinates on that SAME test.
------------------------------------------------------------------------

sameTestExplicitFormulaEquality :
  ∀ {space formula orbit attachment} →
  (same : SelectedFkSameObjectWeld space formula orbit attachment) →
  Explicit.RiemannExplicitFormula.arithmeticForm formula
    (literalSelectedTest same)
  ≡
  Explicit.RiemannExplicitFormula.spectralZeroForm formula
    (literalSelectedTest same)
sameTestExplicitFormulaEquality {formula = formula} same =
  Explicit.RiemannExplicitFormula.explicitFormula formula
    (literalSelectedTest same)
    (literalSelectedAdmissible same)

------------------------------------------------------------------------
-- Attach the existing near/far weld only after proving it uses this same test.
------------------------------------------------------------------------

record SameObjectNearFarAttachment
    {space : Weil.WeilTestSpace}
    {formula : Explicit.RiemannExplicitFormula space}
    {orbit : Orbit.SourceFkOrbit}
    {attachment : Orbit.FkOrbitConsumerAttachment space formula orbit}
    (same : SelectedFkSameObjectWeld space formula orbit attachment)
    (nearFar : Weld.SelectedFkExplicitFormulaWeld space formula orbit attachment)
    : Set where
  field
    nearFarSelectedTestIsLiteralSelectedTest :
      Orbit.FkOrbitConsumerAttachment.selectedPoleTest attachment
      ≡ literalSelectedTest same

open SameObjectNearFarAttachment public

------------------------------------------------------------------------
-- Search pruning.
------------------------------------------------------------------------

data SameObjectFkPayment : Set where
  relateSourceAndWeilTestsByName
  useDifferentTestForAdmissibility
  useDifferentTestForSpectralDecomposition
  weldLiteralSelectedTest
  attachNearFarToSameLiteralTest
  : SameObjectFkPayment

PaymentRelevant : SameObjectFkPayment → Set
PaymentRelevant relateSourceAndWeilTestsByName = ⊥
PaymentRelevant useDifferentTestForAdmissibility = ⊥
PaymentRelevant useDifferentTestForSpectralDecomposition = ⊥
PaymentRelevant weldLiteralSelectedTest = ⊤
PaymentRelevant attachNearFarToSameLiteralTest = ⊤

nameOnlyCorrespondencePruned :
  PaymentRelevant relateSourceAndWeilTestsByName → ⊥
nameOnlyCorrespondencePruned x = x

secondAdmissibilityTestPruned :
  PaymentRelevant useDifferentTestForAdmissibility → ⊥
secondAdmissibilityTestPruned x = x

secondSpectralTestPruned :
  PaymentRelevant useDifferentTestForSpectralDecomposition → ⊥
secondSpectralTestPruned x = x

record SelectedFkSameObjectBoundary : Set where
  constructor selected-fk-same-object-boundary
  field
    sourceProvenanceAndSpectralEvaluationMayUseDifferentTests : Bool
    sourceProvenanceAndSpectralEvaluationMayUseDifferentTestsIsFalse :
      sourceProvenanceAndSpectralEvaluationMayUseDifferentTests ≡ false

    oneLiteralSelectedTestCarriesBothFormulaObservations : Bool
    oneLiteralSelectedTestCarriesBothFormulaObservationsIsTrue :
      oneLiteralSelectedTestCarriesBothFormulaObservations ≡ true

    sameObjectNearFarAttachmentStillRequired : Bool
    sameObjectNearFarAttachmentStillRequiredIsTrue :
      sameObjectNearFarAttachmentStillRequired ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalSelectedFkSameObjectBoundary : SelectedFkSameObjectBoundary
canonicalSelectedFkSameObjectBoundary =
  selected-fk-same-object-boundary
    false refl
    true refl
    true refl
    false refl
    "Use the Moonshine same-element lesson literally: the selected checked-source fk/window object, Weil admissibility, arithmeticForm and spectralZeroForm must all meet on one literal Agda Test. Do not prove source provenance on one embedded test and the near/far spectral decomposition on another merely corresponding test. Once the same-object weld is inhabited, the canonical explicitFormula theorem relates the arithmetic and spectral observations automatically; the remaining zero-side payment is to attach the same cluster/finite-near/far decomposition to that literal selected test. RH remains open."
