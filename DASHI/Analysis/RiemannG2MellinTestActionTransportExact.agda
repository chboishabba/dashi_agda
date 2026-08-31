module DASHI.Analysis.RiemannG2MellinTestActionTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannG2CanonicalTestModulationHighestAlphaExact as HA
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.RiemannG2ConstructedComplexAnalyticCarrierAdapterExact as Carrier

------------------------------------------------------------------------
-- CANONICAL MELLIN-TEST ACTION -> WEIL-TEST ACTION
--
-- RiemannFormulaAnalyticCompatibility already gives an exact equality
--
--   WeilTestSpace.Test space
--   ≡ GammaMellinLayer.Test (AnalyticSubstrate.gammaMellin analytic).
--
-- Therefore H_A does not require its source producer to have been authored on
-- the WeilTestSpace facade.  A producer on the literal canonical Mellin Test
-- can be transported across that SAME equality.  This widens lawful recovery
-- without weakening same-object identity or introducing an isomorphic shadow
-- test space.
------------------------------------------------------------------------

transport : ∀ {A B : Set} → A ≡ B → A → B
transport refl x = x

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

record CanonicalMellinTestAction
    (analytic : Analytic.AnalyticSubstrate)
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula)
    : Set₁ where
  private
    MellinTest =
      Analytic.GammaMellinLayer.Test (Analytic.AnalyticSubstrate.gammaMellin analytic)
  field
    -- Target is still the exact Weil scalar carrier fixed by compatibility.
    modulateMellin :
      Weil.WeilTestSpace.Scalar space → MellinTest → MellinTest

    -- Admissibility is pulled back along the exact Test equality.  This avoids
    -- inventing a second admissibility predicate on the Mellin carrier.
    preservesTransportedWeilAdmissibility :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : MellinTest) →
      Weil.WeilTestSpace.admissible space
        (transport
          (sym (Compat.RiemannFormulaAnalyticCompatibility.testCarrierMatchesMellin compat))
          f) →
      Weil.WeilTestSpace.admissible space
        (transport
          (sym (Compat.RiemannFormulaAnalyticCompatibility.testCarrierMatchesMellin compat))
          (modulateMellin t f))

    targetCharacterActionUsesCanonicalHX : Set
    spectralShiftLawForSameFormula : Set
    shiftedResponseIsConcreteFormulaSpectralResponse : Set
    transformShiftUsesCanonicalWeilTransform : Set
    producerReference : String

open CanonicalMellinTestAction public

mellinToWeil :
  ∀ {analytic space formula compat} →
  Analytic.GammaMellinLayer.Test (Analytic.AnalyticSubstrate.gammaMellin analytic) →
  Weil.WeilTestSpace.Test space
mellinToWeil {compat = compat} =
  transport
    (sym (Compat.RiemannFormulaAnalyticCompatibility.testCarrierMatchesMellin compat))

weilToMellin :
  ∀ {analytic space formula compat} →
  Weil.WeilTestSpace.Test space →
  Analytic.GammaMellinLayer.Test (Analytic.AnalyticSubstrate.gammaMellin analytic)
weilToMellin {compat = compat} =
  transport
    (Compat.RiemannFormulaAnalyticCompatibility.testCarrierMatchesMellin compat)

transportedMellinModulation :
  ∀ {analytic space formula compat} →
  CanonicalMellinTestAction analytic space formula compat →
  Weil.WeilTestSpace.Scalar space →
  Weil.WeilTestSpace.Test space →
  Weil.WeilTestSpace.Test space
transportedMellinModulation {compat = compat} action t f =
  mellinToWeil {compat = compat}
    (modulateMellin action t (weilToMellin {compat = compat} f))

transportedMellinModulationPreservesAdmissibility :
  ∀ {analytic space formula compat} →
  (action : CanonicalMellinTestAction analytic space formula compat) →
  (t : Weil.WeilTestSpace.Scalar space) →
  (f : Weil.WeilTestSpace.Test space) →
  Weil.WeilTestSpace.admissible space f →
  Weil.WeilTestSpace.admissible space (transportedMellinModulation action t f)
transportedMellinModulationPreservesAdmissibility
  {compat = compat} action t f admissibleF
  with Compat.RiemannFormulaAnalyticCompatibility.testCarrierMatchesMellin compat
... | refl = preservesTransportedWeilAdmissibility action t f admissibleF

------------------------------------------------------------------------
-- Compiler to the already-isolated H_A payment.
------------------------------------------------------------------------

toSameCarrierTestModulationPayment :
  ∀ {analytic space formula compat C F realization} →
  CanonicalMellinTestAction analytic space formula compat →
  HA.SameCarrierTestModulationPayment
    analytic space formula compat C F realization
toSameCarrierTestModulationPayment action = record
  { HA.modulateTest = transportedMellinModulation action
  ; HA.modulationPreservesAdmissibility =
      transportedMellinModulationPreservesAdmissibility action
  ; HA.targetCharacterActionUsesCanonicalHX =
      targetCharacterActionUsesCanonicalHX action
  ; HA.spectralShiftLawForSameFormula = spectralShiftLawForSameFormula action
  ; HA.shiftedResponseIsConcreteFormulaSpectralResponse =
      shiftedResponseIsConcreteFormulaSpectralResponse action
  ; HA.transformShiftUsesCanonicalWeilTransform =
      transformShiftUsesCanonicalWeilTransform action
  ; HA.paymentReference = producerReference action
  }

------------------------------------------------------------------------
-- Search consequence.
------------------------------------------------------------------------

data MellinActionSearchAction : Set where
  demandProducerDirectlyOnWeilFacade
  recoverProducerOnCanonicalMellinTest
  useMerelyIsomorphicFunctionSpace
  transportAcrossCompatibilityEquality
  continueToSameFormulaShift
  : MellinActionSearchAction

MellinActionRelevant : MellinActionSearchAction → Set
MellinActionRelevant demandProducerDirectlyOnWeilFacade = ⊥
MellinActionRelevant recoverProducerOnCanonicalMellinTest = ⊤
MellinActionRelevant useMerelyIsomorphicFunctionSpace = ⊥
MellinActionRelevant transportAcrossCompatibilityEquality = ⊤
MellinActionRelevant continueToSameFormulaShift = ⊤

directWeilFacadeRequirementPruned :
  MellinActionRelevant demandProducerDirectlyOnWeilFacade → ⊥
directWeilFacadeRequirementPruned x = x

merelyIsomorphicFunctionSpacePruned :
  MellinActionRelevant useMerelyIsomorphicFunctionSpace → ⊥
merelyIsomorphicFunctionSpacePruned x = x

record MellinTestActionTransportBoundary : Set where
  constructor mellin-test-action-transport-boundary
  field
    producerMustBeAuthoredOnWeilFacade : Bool
    producerMustBeAuthoredOnWeilFacadeIsFalse :
      producerMustBeAuthoredOnWeilFacade ≡ false

    canonicalMellinTestProducerIsLawfulSource : Bool
    canonicalMellinTestProducerIsLawfulSourceIsTrue :
      canonicalMellinTestProducerIsLawfulSource ≡ true

    testEqualitySupportsExactActionTransport : Bool
    testEqualitySupportsExactActionTransportIsTrue :
      testEqualitySupportsExactActionTransport ≡ true

    arbitraryIsomorphicFunctionCarrierIsAccepted : Bool
    arbitraryIsomorphicFunctionCarrierIsAcceptedIsFalse :
      arbitraryIsomorphicFunctionCarrierIsAccepted ≡ false

    transportAloneProvesSpectralShift : Bool
    transportAloneProvesSpectralShiftIsFalse :
      transportAloneProvesSpectralShift ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalMellinTestActionTransportBoundary : MellinTestActionTransportBoundary
canonicalMellinTestActionTransportBoundary =
  mellin-test-action-transport-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "Search for the target action on either the exact Weil Test facade or the exact Gamma/Mellin Test selected by the same AnalyticSubstrate. RiemannFormulaAnalyticCompatibility supplies propositional equality between those carriers, so a Mellin-native action and its admissibility theorem transport exactly into the H_A payment. Do not accept merely isomorphic or analogous function spaces. The same-formula spectral shift theorem remains a substantive receipt and is not manufactured by carrier transport."
