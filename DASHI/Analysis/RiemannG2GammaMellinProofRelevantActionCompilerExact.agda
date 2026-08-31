module DASHI.Analysis.RiemannG2GammaMellinProofRelevantActionCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.RiemannG2ConstructedComplexAnalyticCarrierAdapterExact as Carrier
import DASHI.Analysis.RiemannG2MellinTestActionTransportExact as Mellin
import DASHI.Analysis.RiemannG2GammaMellinImplementationRecoveryExact as Recovery
import DASHI.Analysis.RiemannG2CanonicalTestModulationProofRelevantExact as StrongHA

------------------------------------------------------------------------
-- CONCRETE GAMMA/MELLIN IMPLEMENTATION -> PROOF-RELEVANT H_A
--
-- The implementation-recovery owner found the correct representation seam:
-- an action may already live on the concrete implementation of the canonical
-- Gamma/Mellin Test.  This compiler makes that BIDI route theorem-bearing.
-- Every action/shift receipt below is an actual equality or admissibility proof,
-- not a Set-valued label.
------------------------------------------------------------------------

implementationToMellin :
  ∀ {analytic} →
  (impl : Recovery.GammaMellinTestImplementation analytic) →
  Recovery.ImplementationTest impl →
  Analytic.GammaMellinLayer.Test (Analytic.AnalyticSubstrate.gammaMellin analytic)
implementationToMellin impl =
  Mellin.transport (Recovery.implementationTestIsCanonicalMellinTest impl)

mellinToImplementation :
  ∀ {analytic} →
  (impl : Recovery.GammaMellinTestImplementation analytic) →
  Analytic.GammaMellinLayer.Test (Analytic.AnalyticSubstrate.gammaMellin analytic) →
  Recovery.ImplementationTest impl
mellinToImplementation impl =
  Mellin.transport
    (Mellin.sym (Recovery.implementationTestIsCanonicalMellinTest impl))

implementationToWeil :
  ∀ {analytic space formula compat} →
  (impl : Recovery.GammaMellinTestImplementation analytic) →
  Recovery.ImplementationTest impl →
  Weil.WeilTestSpace.Test space
implementationToWeil {compat = compat} impl x =
  Mellin.mellinToWeil {compat = compat} (implementationToMellin impl x)

weilToImplementation :
  ∀ {analytic space formula compat} →
  (impl : Recovery.GammaMellinTestImplementation analytic) →
  Weil.WeilTestSpace.Test space →
  Recovery.ImplementationTest impl
weilToImplementation {compat = compat} impl f =
  mellinToImplementation impl (Mellin.weilToMellin {compat = compat} f)

record ProofRelevantImplementedMellinAction
    (analytic : Analytic.AnalyticSubstrate)
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula)
    (impl : Recovery.GammaMellinTestImplementation analytic) : Set₁ where
  field
    act :
      Weil.WeilTestSpace.Scalar space →
      Recovery.ImplementationTest impl →
      Recovery.ImplementationTest impl

    expectedCharacterAction :
      Weil.WeilTestSpace.Scalar space →
      Weil.WeilTestSpace.Test space →
      Weil.WeilTestSpace.Test space

    expectedShiftedSpectralResponse :
      Weil.WeilTestSpace.Scalar space →
      Weil.WeilTestSpace.Test space →
      Weil.WeilTestSpace.Scalar space

    expectedTransformShift :
      Weil.WeilTestSpace.Scalar space →
      Weil.WeilTestSpace.Test space →
      Weil.WeilTestSpace.TransformValue space

    preservesPulledBackWeilAdmissibility :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : Weil.WeilTestSpace.Test space) →
      Weil.WeilTestSpace.admissible space f →
      Weil.WeilTestSpace.admissible space
        (implementationToWeil impl (act t (weilToImplementation impl f)))

    actionAgreesWithCanonicalHXAfterTransport :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : Weil.WeilTestSpace.Test space) →
      implementationToWeil impl (act t (weilToImplementation impl f))
      ≡ expectedCharacterAction t f

    sameFormulaSpectralShiftAfterTransport :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : Weil.WeilTestSpace.Test space) →
      Explicit.RiemannExplicitFormula.spectralZeroForm formula
        (implementationToWeil impl (act t (weilToImplementation impl f)))
      ≡ expectedShiftedSpectralResponse t f

    sameWeilTransformShiftAfterTransport :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : Weil.WeilTestSpace.Test space) →
      Weil.WeilTestSpace.transform space
        (implementationToWeil impl (act t (weilToImplementation impl f)))
      ≡ expectedTransformShift t f

    producerReference : String

open ProofRelevantImplementedMellinAction public

transportedImplementationModulation :
  ∀ {analytic space formula compat impl} →
  ProofRelevantImplementedMellinAction analytic space formula compat impl →
  Weil.WeilTestSpace.Scalar space →
  Weil.WeilTestSpace.Test space →
  Weil.WeilTestSpace.Test space
transportedImplementationModulation {impl = impl} P t f =
  implementationToWeil impl (act P t (weilToImplementation impl f))

toProofRelevantCanonicalTestModulation :
  ∀ {analytic space formula compat C F realization impl} →
  ProofRelevantImplementedMellinAction analytic space formula compat impl →
  StrongHA.ProofRelevantCanonicalTestModulation
    analytic space formula compat C F realization
toProofRelevantCanonicalTestModulation {impl = impl} P = record
  { StrongHA.expectedCharacterAction = expectedCharacterAction P
  ; StrongHA.expectedShiftedSpectralResponse = expectedShiftedSpectralResponse P
  ; StrongHA.expectedTransformShift = expectedTransformShift P
  ; StrongHA.modulateTest = transportedImplementationModulation P
  ; StrongHA.modulationPreservesAdmissibility = preservesPulledBackWeilAdmissibility P
  ; StrongHA.modulateIsCanonicalCharacterAction =
      actionAgreesWithCanonicalHXAfterTransport P
  ; StrongHA.sameFormulaSpectralShift = sameFormulaSpectralShiftAfterTransport P
  ; StrongHA.canonicalWeilTransformShift = sameWeilTransformShiftAfterTransport P
  ; StrongHA.producerReference = producerReference P
  }

------------------------------------------------------------------------
-- Cross-pollination boundary.
--
-- Finite Heisenberg/C3 action calculi correctly suggest the architecture
-- "carrier + parameterized action + intertwining law", but consumer-relative
-- same-object discipline decides whether that architecture transfers to RH.
------------------------------------------------------------------------

record GammaMellinProofRelevantActionCompilerBoundary : Set where
  constructor gamma-mellin-proof-relevant-action-compiler-boundary
  field
    exactImplementationEqualitySupportsTransport : Bool
    exactImplementationEqualitySupportsTransportIsTrue :
      exactImplementationEqualitySupportsTransport ≡ true

    actionArchitectureReusableAcrossDomains : Bool
    actionArchitectureReusableAcrossDomainsIsTrue :
      actionArchitectureReusableAcrossDomains ≡ true

    finiteCharacterActionItselfIsRHHADonor : Bool
    finiteCharacterActionItselfIsRHHADonorIsFalse :
      finiteCharacterActionItselfIsRHHADonor ≡ false

    transportedAdmissibilityProofRequired : Bool
    transportedAdmissibilityProofRequiredIsTrue :
      transportedAdmissibilityProofRequired ≡ true

    transportedSameFormulaShiftProofRequired : Bool
    transportedSameFormulaShiftProofRequiredIsTrue :
      transportedSameFormulaShiftProofRequired ≡ true

    theoremBearingCompilerOwned : Bool
    theoremBearingCompilerOwnedIsTrue : theoremBearingCompilerOwned ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalGammaMellinProofRelevantActionCompilerBoundary :
  GammaMellinProofRelevantActionCompilerBoundary
canonicalGammaMellinProofRelevantActionCompilerBoundary =
  gamma-mellin-proof-relevant-action-compiler-boundary
    true refl
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
    "The BIDI recovery route is now executable at the representation seam: an exact equality from the concrete Gamma/Mellin implementation carrier to the selected Mellin Test transports an already-owned parameterized action into the literal Weil Test. To count as H_A, the producer must carry actual admissibility, canonical-character agreement, same-RiemannExplicitFormula spectral shift, and same-Weil-transform equalities after transport. The finite Heisenberg/C3 lane contributes action/intertwiner architecture only; without the RH carrier equality it is not an analytic donor."
