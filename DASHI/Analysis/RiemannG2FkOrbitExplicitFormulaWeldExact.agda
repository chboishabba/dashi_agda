module DASHI.Analysis.RiemannG2FkOrbitExplicitFormulaWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact as Orbit

------------------------------------------------------------------------
-- SELECTED fk ORBIT -> SAME RIEMANN EXPLICIT FORMULA
--
-- This is the consumer-minimal replacement for the old broad
-- LiteralG2ExplicitFormulaWeld Set sockets.  It is indexed by one actual
-- WeilTestSpace and one actual RiemannExplicitFormula and speaks only about the
-- selected embedded source pole test consumed by the near/far route.
------------------------------------------------------------------------

≡-trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans refl refl = refl

record SelectedFkExplicitFormulaWeld
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (attachment : Orbit.FkOrbitConsumerAttachment space formula orbit)
    : Set₁ where
  private
    Scalar = Weil.WeilTestSpace.Scalar space
    Test = Weil.WeilTestSpace.Test space

  field
    sameOrdinateCluster : Scalar
    finitePoleNearSigned : Scalar
    farZeroRemainder : Scalar

    -- Literal spectral decomposition for THIS formula and THIS selected test.
    spectralIsClusterNearFar :
      Explicit.RiemannExplicitFormula.spectralZeroForm formula
        (Orbit.FkOrbitConsumerAttachment.selectedPoleTest attachment)
      ≡
      Weil.WeilTestSpace._+S_ space sameOrdinateCluster
        (Weil.WeilTestSpace._+S_ space finitePoleNearSigned farZeroRemainder)

    -- The finite near summand is the same source-selected nearOffFinset object,
    -- not merely a numerically equal scalar assembled from another carrier.
    finiteNearUsesSelectedSourceOrbit : Set
    finiteNearUsesSelectedSourceOrbitWitness :
      finiteNearUsesSelectedSourceOrbit

    sameOrdinateClusterUsesSelectedTarget : Set
    sameOrdinateClusterUsesSelectedTargetWitness :
      sameOrdinateClusterUsesSelectedTarget

    farRemainderUsesSameCutoffComplement : Set
    farRemainderUsesSameCutoffComplementWitness :
      farRemainderUsesSameCutoffComplement

    weldReference : String

open SelectedFkExplicitFormulaWeld public

------------------------------------------------------------------------
-- Once the spectral decomposition is attached, the canonical explicit formula
-- immediately transports the SAME selected test's arithmetic form to it.
------------------------------------------------------------------------

selectedArithmeticIsClusterNearFar :
  ∀ {space formula orbit attachment} →
  (weld : SelectedFkExplicitFormulaWeld space formula orbit attachment) →
  Explicit.RiemannExplicitFormula.arithmeticForm formula
    (Orbit.FkOrbitConsumerAttachment.selectedPoleTest attachment)
  ≡
  Weil.WeilTestSpace._+S_ space
    (sameOrdinateCluster weld)
    (Weil.WeilTestSpace._+S_ space
      (finitePoleNearSigned weld)
      (farZeroRemainder weld))
selectedArithmeticIsClusterNearFar {space} {formula} {attachment = attachment} weld =
  ≡-trans
    (Explicit.RiemannExplicitFormula.explicitFormula formula
      (Orbit.FkOrbitConsumerAttachment.selectedPoleTest attachment)
      (Orbit.FkOrbitConsumerAttachment.selectedPoleAdmissible attachment))
    (spectralIsClusterNearFar weld)

------------------------------------------------------------------------
-- Search pruning.
------------------------------------------------------------------------

data ExplicitFormulaWeldPayment : Set where
  reconstructGenericExplicitFormula
  identifyWholeSourceTestCarrier
  recoverSelectedOrbitEmbedding
  recoverSelectedSpectralNearFarEquality
  reuseCanonicalExplicitFormulaOnSelectedTest
  : ExplicitFormulaWeldPayment

PaymentRelevant : ExplicitFormulaWeldPayment → Set
PaymentRelevant reconstructGenericExplicitFormula = ⊥
PaymentRelevant identifyWholeSourceTestCarrier = ⊥
PaymentRelevant recoverSelectedOrbitEmbedding = ⊤
PaymentRelevant recoverSelectedSpectralNearFarEquality = ⊤
PaymentRelevant reuseCanonicalExplicitFormulaOnSelectedTest = ⊤

reconstructGenericExplicitFormulaPruned :
  PaymentRelevant reconstructGenericExplicitFormula → ⊥
reconstructGenericExplicitFormulaPruned x = x

wholeSourceCarrierIdentificationPruned :
  PaymentRelevant identifyWholeSourceTestCarrier → ⊥
wholeSourceCarrierIdentificationPruned x = x

record SelectedFkExplicitFormulaWeldBoundary : Set where
  constructor selected-fk-explicit-formula-weld-boundary
  field
    genericExplicitFormulaAlreadyOwned : Bool
    genericExplicitFormulaAlreadyOwnedIsTrue :
      genericExplicitFormulaAlreadyOwned ≡ true

    wholeSourceCarrierEqualityRequired : Bool
    wholeSourceCarrierEqualityRequiredIsFalse :
      wholeSourceCarrierEqualityRequired ≡ false

    selectedOrbitEmbeddingRequired : Bool
    selectedOrbitEmbeddingRequiredIsTrue :
      selectedOrbitEmbeddingRequired ≡ true

    sameFormulaNearFarSpectralEqualityRequired : Bool
    sameFormulaNearFarSpectralEqualityRequiredIsTrue :
      sameFormulaNearFarSpectralEqualityRequired ≡ true

    arithmeticSideThenFollowsByExistingExplicitFormula : Bool
    arithmeticSideThenFollowsByExistingExplicitFormulaIsTrue :
      arithmeticSideThenFollowsByExistingExplicitFormula ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalSelectedFkExplicitFormulaWeldBoundary :
  SelectedFkExplicitFormulaWeldBoundary
canonicalSelectedFkExplicitFormulaWeldBoundary =
  selected-fk-explicit-formula-weld-boundary
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
    "The canonical RiemannExplicitFormula is already owned. Do not rebuild it and do not identify the whole checked-source function space with the abstract Test carrier. Embed the selected source fk/window orbit into the chosen Weil Test, prove admissibility there, and prove the spectralZeroForm of that exact selected test is same-ordinate cluster plus finite pole-near signed response plus the same far remainder. The existing explicitFormula theorem then transports the arithmeticForm of the same test to that decomposition automatically. RH remains open."
