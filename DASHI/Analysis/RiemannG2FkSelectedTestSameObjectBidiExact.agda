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

≡-sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
≡-sym refl = refl

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
-- Existing FkOrbitConsumerAttachment ALREADY pays this weld.
------------------------------------------------------------------------

fromConsumerAttachment :
  ∀ {space formula orbit} →
  (attachment : Orbit.FkOrbitConsumerAttachment space formula orbit) →
  SelectedFkSameObjectWeld space formula orbit attachment
fromConsumerAttachment attachment = record
  { literalSelectedTest =
      Orbit.FkOrbitConsumerAttachment.selectedPoleTest attachment
  ; literalSelectedTestIsEmbeddedSourceSelection =
      Orbit.FkOrbitConsumerAttachment.selectedPoleTestIsEmbeddedSourceSelection
        attachment
  ; literalSelectedTestIsAttachmentSelection = refl
  ; literalSelectedAdmissible =
      Orbit.FkOrbitConsumerAttachment.selectedPoleAdmissible attachment
  ; sameSourceOrbitReference =
      Orbit.FkOrbitConsumerAttachment.attachmentReference attachment
  }

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
-- The existing near/far weld is indexed by the same attachment, hence its
-- selected test is definitionally the same selectedPoleTest used above.
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

nearFarFromConsumerAttachment :
  ∀ {space formula orbit} →
  (attachment : Orbit.FkOrbitConsumerAttachment space formula orbit) →
  (nearFar : Weld.SelectedFkExplicitFormulaWeld space formula orbit attachment) →
  SameObjectNearFarAttachment (fromConsumerAttachment attachment) nearFar
nearFarFromConsumerAttachment attachment nearFar = record
  { nearFarSelectedTestIsLiteralSelectedTest = refl }

------------------------------------------------------------------------
-- Search pruning.
------------------------------------------------------------------------

data SameObjectFkPayment : Set where
  relateSourceAndWeilTestsByName
  useDifferentTestForAdmissibility
  useDifferentTestForSpectralDecomposition
  weldLiteralSelectedTest
  attachNearFarToSameLiteralTest
  recoverNearFarSpectralEquality
  : SameObjectFkPayment

PaymentRelevant : SameObjectFkPayment → Set
PaymentRelevant relateSourceAndWeilTestsByName = ⊥
PaymentRelevant useDifferentTestForAdmissibility = ⊥
PaymentRelevant useDifferentTestForSpectralDecomposition = ⊥
PaymentRelevant weldLiteralSelectedTest = ⊥
PaymentRelevant attachNearFarToSameLiteralTest = ⊥
PaymentRelevant recoverNearFarSpectralEquality = ⊤

nameOnlyCorrespondencePruned :
  PaymentRelevant relateSourceAndWeilTestsByName → ⊥
nameOnlyCorrespondencePruned x = x

secondAdmissibilityTestPruned :
  PaymentRelevant useDifferentTestForAdmissibility → ⊥
secondAdmissibilityTestPruned x = x

secondSpectralTestPruned :
  PaymentRelevant useDifferentTestForSpectralDecomposition → ⊥
secondSpectralTestPruned x = x

literalSelectedTestWeldAlreadyCompiled :
  PaymentRelevant weldLiteralSelectedTest → ⊥
literalSelectedTestWeldAlreadyCompiled x = x

nearFarSameObjectAttachmentAlreadyCompiled :
  PaymentRelevant attachNearFarToSameLiteralTest → ⊥
nearFarSameObjectAttachmentAlreadyCompiled x = x

record SelectedFkSameObjectBoundary : Set where
  constructor selected-fk-same-object-boundary
  field
    sourceProvenanceAndSpectralEvaluationMayUseDifferentTests : Bool
    sourceProvenanceAndSpectralEvaluationMayUseDifferentTestsIsFalse :
      sourceProvenanceAndSpectralEvaluationMayUseDifferentTests ≡ false

    oneLiteralSelectedTestCarriesBothFormulaObservations : Bool
    oneLiteralSelectedTestCarriesBothFormulaObservationsIsTrue :
      oneLiteralSelectedTestCarriesBothFormulaObservations ≡ true

    sameObjectWeldAlreadyFollowsFromConsumerAttachment : Bool
    sameObjectWeldAlreadyFollowsFromConsumerAttachmentIsTrue :
      sameObjectWeldAlreadyFollowsFromConsumerAttachment ≡ true

    nearFarSameObjectAttachmentAlreadyFollows : Bool
    nearFarSameObjectAttachmentAlreadyFollowsIsTrue :
      nearFarSameObjectAttachmentAlreadyFollows ≡ true

    nearFarSpectralEqualityStillRequired : Bool
    nearFarSpectralEqualityStillRequiredIsTrue :
      nearFarSpectralEqualityStillRequired ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalSelectedFkSameObjectBoundary : SelectedFkSameObjectBoundary
canonicalSelectedFkSameObjectBoundary =
  selected-fk-same-object-boundary
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    "Use the Moonshine same-element lesson literally: source provenance, Weil admissibility, arithmeticForm and spectralZeroForm meet on one literal selected Agda Test. The existing FkOrbitConsumerAttachment already constructs that same-object weld, and any SelectedFkExplicitFormulaWeld indexed by the same attachment automatically uses the same selected test. Therefore neither same-object welding nor near/far test identity is a live payment anymore. The remaining zero-side payment is the substantive same-formula equality spectralZeroForm(selectedPoleTest) = same-ordinate cluster + finite signed near response + the same far remainder. RH remains open."
