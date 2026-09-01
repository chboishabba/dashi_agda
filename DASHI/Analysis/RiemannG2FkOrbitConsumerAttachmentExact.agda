module DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit

------------------------------------------------------------------------
-- CONSUMER-RELATIVE SOURCE fk ORBIT ATTACHMENT
--
-- Backward from the target-centred pole/near consumer, whole-carrier equality
-- between the checked Lean C_c^2 function space and WeilTestSpace.Test is
-- stronger than necessary.  The terminal consumer uses one base pole test and
-- one selected target/windowed test, together with admissibility and the exact
-- observations of the same RiemannExplicitFormula.
--
-- Therefore the minimal same-object payment is an embedding of the selected
-- source orbit into the already-chosen Weil Test carrier which preserves the
-- exact observations consumed downstream.  This is the same architecture as
-- DashiWeilQuadratic.embed, but specialized to the literal Zeta23 fk orbit.
------------------------------------------------------------------------

record SourceFkOrbit : Set₁ where
  field
    SourceTest Target Cutoff : Set

    baseSourceTest : SourceTest
    target : Target
    cutoff : Cutoff

    modulateSource : Target → SourceTest → SourceTest
    windowSource : Cutoff → SourceTest → SourceTest

    selectedSourceTest : SourceTest
    selectedSourceTestIsConstruction :
      selectedSourceTest ≡
      windowSource cutoff (modulateSource target baseSourceTest)

    sourceReference : String

open SourceFkOrbit public

record FkOrbitConsumerAttachment
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : SourceFkOrbit) : Set₁ where
  field
    -- Only the selected source family is attached; no equality of whole
    -- function spaces is required.
    embedSourceTest : SourceFkOrbit.SourceTest orbit →
                      Weil.WeilTestSpace.Test space

    basePoleTest : Weil.WeilTestSpace.Test space
    basePoleTestIsEmbeddedSourceBase :
      basePoleTest ≡ embedSourceTest (SourceFkOrbit.baseSourceTest orbit)

    selectedPoleTest : Weil.WeilTestSpace.Test space
    selectedPoleTestIsEmbeddedSourceSelection :
      selectedPoleTest ≡ embedSourceTest (SourceFkOrbit.selectedSourceTest orbit)

    basePoleAdmissible :
      Weil.WeilTestSpace.admissible space basePoleTest

    selectedPoleAdmissible :
      Weil.WeilTestSpace.admissible space selectedPoleTest

    -- Exact same-formula observations required by the target-centred consumer.
    ExpectedSpectralValue : Set
    expectedSpectralValue : ExpectedSpectralValue

    spectralObservationPreserved :
      Explicit.RiemannExplicitFormula.spectralZeroForm formula selectedPoleTest
      ≡ Explicit.RiemannExplicitFormula.spectralZeroForm formula
          (embedSourceTest (SourceFkOrbit.selectedSourceTest orbit))

    SameOrdinateCluster FinitePoleNearSigned FarZeroRemainder : Set
    sameOrdinateCluster : SameOrdinateCluster
    finitePoleNearSigned : FinitePoleNearSigned
    farZeroRemainder : FarZeroRemainder

    spectralDecompositionForSameFormula : Set
    spectralDecompositionForSameFormulaWitness :
      spectralDecompositionForSameFormula

    preservesTargetRelativeGap : Set
    preservesTargetRelativeGapWitness : preservesTargetRelativeGap

    preservesMultiplicity : Set
    preservesMultiplicityWitness : preservesMultiplicity

    preservesNearOffFinset : Set
    preservesNearOffFinsetWitness : preservesNearOffFinset

    attachmentReference : String

open FkOrbitConsumerAttachment public

------------------------------------------------------------------------
-- BIDI search pruning.
------------------------------------------------------------------------

data FkRepresentationPayment : Set where
  identifyWholeSourceFunctionSpaceWithWeilTest
  identifyWholeSourceFunctionSpaceWithMellinTest
  recoverSelectedFkOrbitEmbedding
  recoverSelectedFkAdmissibility
  recoverSelectedSameFormulaSpectralObservation
  recoverSelectedPoleNearDecomposition
  : FkRepresentationPayment

PaymentRelevant : FkRepresentationPayment → Set
PaymentRelevant identifyWholeSourceFunctionSpaceWithWeilTest = ⊥
PaymentRelevant identifyWholeSourceFunctionSpaceWithMellinTest = ⊥
PaymentRelevant recoverSelectedFkOrbitEmbedding = ⊤
PaymentRelevant recoverSelectedFkAdmissibility = ⊤
PaymentRelevant recoverSelectedSameFormulaSpectralObservation = ⊤
PaymentRelevant recoverSelectedPoleNearDecomposition = ⊤

wholeWeilCarrierEqualityPruned :
  PaymentRelevant identifyWholeSourceFunctionSpaceWithWeilTest → ⊥
wholeWeilCarrierEqualityPruned x = x

wholeMellinCarrierEqualityPruned :
  PaymentRelevant identifyWholeSourceFunctionSpaceWithMellinTest → ⊥
wholeMellinCarrierEqualityPruned x = x

record FkOrbitConsumerBoundary : Set where
  constructor fk-orbit-consumer-boundary
  field
    terminalConsumerRequiresWholeFunctionSpaceEquality : Bool
    terminalConsumerRequiresWholeFunctionSpaceEqualityIsFalse :
      terminalConsumerRequiresWholeFunctionSpaceEquality ≡ false

    selectedOrbitEmbeddingIsConsumerSufficientShape : Bool
    selectedOrbitEmbeddingIsConsumerSufficientShapeIsTrue :
      selectedOrbitEmbeddingIsConsumerSufficientShape ≡ true

    selectedAdmissibilityStillRequired : Bool
    selectedAdmissibilityStillRequiredIsTrue :
      selectedAdmissibilityStillRequired ≡ true

    sameFormulaSpectralObservationStillRequired : Bool
    sameFormulaSpectralObservationStillRequiredIsTrue :
      sameFormulaSpectralObservationStillRequired ≡ true

    poleNearDecompositionStillRequired : Bool
    poleNearDecompositionStillRequiredIsTrue :
      poleNearDecompositionStillRequired ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalFkOrbitConsumerBoundary : FkOrbitConsumerBoundary
canonicalFkOrbitConsumerBoundary =
  fk-orbit-consumer-boundary
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    "Do not reconstruct an equality between the entire checked Lean C_c^2 source function space and the abstract Agda Weil/Mellin Test carrier. The target-centred consumer only needs the literal source base/target/window orbit embedded into the already-selected Weil Test, with admissibility and same-RiemannExplicitFormula observations preserved for that selected object. Recover that consumer-relative attachment and the exact pole-near spectral decomposition; whole-carrier equality is overpayment. RH remains open."
