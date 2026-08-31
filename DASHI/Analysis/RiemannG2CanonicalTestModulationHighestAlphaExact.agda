module DASHI.Analysis.RiemannG2CanonicalTestModulationHighestAlphaExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl; trans)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannG2ConstructedComplexAnalyticCarrierAdapterExact as Carrier

------------------------------------------------------------------------
-- H_A HIGHEST-ALPHA CUT AFTER THE CANONICAL H_X CARRIER ATTACHMENT
--
-- RiemannFormulaAnalyticCompatibility already owns two identities that should
-- not be paid again by H_A:
--
--   Weil Test   = Gamma/Mellin Test
--   Weil Scalar = canonical analytic Real.
--
-- Once the canonical analytic carrier is identified with the constructed
-- complex carrier, transitivity therefore fixes the target scalar carrier too.
-- H_A must not introduce a second Target type or a shadow test space.  Its live
-- payment is an endomorphism of the existing Test carrier, admissibility
-- preservation, and the spectral shift theorem for the same explicit formula.
------------------------------------------------------------------------

weilScalarIsConstructedReal :
  ∀ {analytic space formula C F} →
  (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula) →
  Carrier.CanonicalConstructedCarrierRealization analytic C F →
  Weil.WeilTestSpace.Scalar space
  ≡ Real.Real (Real.real (Complex.realPackage C))
weilScalarIsConstructedReal compat realization =
  trans
    (Compat.RiemannFormulaAnalyticCompatibility.scalarCarrierMatchesReal compat)
    (Carrier.realCarrierIdentityFromWholeCarrier realization)

weilTestIsCanonicalMellinTest :
  ∀ {analytic space formula} →
  (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula) →
  Weil.WeilTestSpace.Test space
  ≡ Analytic.GammaMellinLayer.Test (Analytic.AnalyticSubstrate.gammaMellin analytic)
weilTestIsCanonicalMellinTest compat =
  Compat.RiemannFormulaAnalyticCompatibility.testCarrierMatchesMellin compat

record SameCarrierTestModulationPayment
    (analytic : Analytic.AnalyticSubstrate)
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula)
    (C : Complex.ConstructedComplexPackage)
    (F : Carrier.ConstructedComplexAnalyticFunctionLayer C)
    (realization : Carrier.CanonicalConstructedCarrierRealization analytic C F)
    : Set₁ where
  field
    -- Target is not separately chosen: it is the exact Weil scalar carrier,
    -- already identified with the analytic/constructed real by compatibility.
    modulateTest :
      Weil.WeilTestSpace.Scalar space →
      Weil.WeilTestSpace.Test space →
      Weil.WeilTestSpace.Test space

    modulationPreservesAdmissibility :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : Weil.WeilTestSpace.Test space) →
      Weil.WeilTestSpace.admissible space f →
      Weil.WeilTestSpace.admissible space (modulateTest t f)

    -- These receipts must refer to this exact formula, not a separately chosen
    -- transform surface.  The concrete character action is supplied by H_X.
    targetCharacterActionUsesCanonicalHX : Set
    spectralShiftLawForSameFormula : Set
    shiftedResponseIsConcreteFormulaSpectralResponse : Set
    transformShiftUsesCanonicalWeilTransform : Set

    paymentReference : String

open SameCarrierTestModulationPayment public

------------------------------------------------------------------------
-- Search pruning.
------------------------------------------------------------------------

data HATestAction : Set where
  rebuildWeilTestSpace
  chooseIndependentTargetCarrier
  chooseIndependentMellinTestCarrier
  useDifferentExplicitFormula
  recoverExistingTestModulation
  proveAdmissibilityPreservation
  recoverSameFormulaSpectralShift
  : HATestAction

HARelevant : HATestAction → Set
HARelevant rebuildWeilTestSpace = ⊥
HARelevant chooseIndependentTargetCarrier = ⊥
HARelevant chooseIndependentMellinTestCarrier = ⊥
HARelevant useDifferentExplicitFormula = ⊥
HARelevant recoverExistingTestModulation = ⊤
HARelevant proveAdmissibilityPreservation = ⊤
HARelevant recoverSameFormulaSpectralShift = ⊤

rebuildWeilTestSpacePruned : HARelevant rebuildWeilTestSpace → ⊥
rebuildWeilTestSpacePruned x = x

independentTargetCarrierPruned : HARelevant chooseIndependentTargetCarrier → ⊥
independentTargetCarrierPruned x = x

independentMellinCarrierPruned :
  HARelevant chooseIndependentMellinTestCarrier → ⊥
independentMellinCarrierPruned x = x

differentExplicitFormulaPruned : HARelevant useDifferentExplicitFormula → ⊥
differentExplicitFormulaPruned x = x

record CanonicalTestModulationHighestAlphaBoundary : Set where
  constructor canonical-test-modulation-highest-alpha-boundary
  field
    testCarrierIdentityNeedsFreshChoice : Bool
    testCarrierIdentityNeedsFreshChoiceIsFalse :
      testCarrierIdentityNeedsFreshChoice ≡ false

    targetScalarCarrierNeedsFreshChoice : Bool
    targetScalarCarrierNeedsFreshChoiceIsFalse :
      targetScalarCarrierNeedsFreshChoice ≡ false

    sameConcreteExplicitFormulaMustBePreserved : Bool
    sameConcreteExplicitFormulaMustBePreservedIsTrue :
      sameConcreteExplicitFormulaMustBePreserved ≡ true

    genericTransformExistenceAloneClosesHA : Bool
    genericTransformExistenceAloneClosesHAIsFalse :
      genericTransformExistenceAloneClosesHA ≡ false

    testModulationAdmissibilityAndSameFormulaShiftAreLive : Bool
    testModulationAdmissibilityAndSameFormulaShiftAreLiveIsTrue :
      testModulationAdmissibilityAndSameFormulaShiftAreLive ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalTestModulationHighestAlphaBoundary :
  CanonicalTestModulationHighestAlphaBoundary
canonicalTestModulationHighestAlphaBoundary =
  canonical-test-modulation-highest-alpha-boundary
    false refl
    false refl
    true refl
    false refl
    true refl
    false refl
    "After the canonical H_X carrier realization, do not allocate search to a new Target carrier, a new Mellin test carrier, or a shadow explicit formula. RiemannFormulaAnalyticCompatibility already identifies Weil Test with the selected Gamma/Mellin Test and Weil Scalar with the selected analytic Real; whole-carrier realization then identifies that scalar with the constructed real donor. The live H_A payment is therefore only the actual modulation endomorphism on the existing Test carrier, admissibility preservation, and a spectral shift law tied to the same concrete RiemannExplicitFormula and canonical H_X character."
