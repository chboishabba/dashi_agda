module DASHI.Analysis.RiemannG2GammaMellinImplementationRecoveryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannG2MellinTestActionTransportExact as Transport

------------------------------------------------------------------------
-- BIDI RECOVERY CUT BELOW H_A
--
-- The canonical GammaMellinLayer intentionally leaves Test opaque.  Therefore
-- an existing modulation theorem may be authored against the concrete
-- implementation of that Test carrier rather than against the public record
-- projection itself.  Under the repo-complete assumption, the next search leaf
-- is not another Fourier identity: it is the realization object identifying an
-- already-constructed test/function carrier with the literal GammaMellin Test.
------------------------------------------------------------------------

record GammaMellinTestImplementation
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  field
    ImplementationTest : Set
    implementationTestIsCanonicalMellinTest :
      ImplementationTest
      ≡ Analytic.GammaMellinLayer.Test
          (Analytic.AnalyticSubstrate.gammaMellin analytic)
    implementationReference : String

open GammaMellinTestImplementation public

------------------------------------------------------------------------
-- Once the implementation carrier is identified exactly, an action authored
-- there transports to the canonical Mellin Test.  This is representation
-- transport only; it does not invent admissibility or a spectral-shift law.
------------------------------------------------------------------------

record ImplementedMellinAction
    (analytic : Analytic.AnalyticSubstrate)
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula)
    (impl : GammaMellinTestImplementation analytic) : Set₁ where
  field
    act :
      Weil.WeilTestSpace.Scalar space →
      ImplementationTest impl →
      ImplementationTest impl

    preservesPulledBackWeilAdmissibility : Set
    sameFormulaSpectralShift : Set
    actionReference : String

open ImplementedMellinAction public

------------------------------------------------------------------------
-- Search pruning.  Generic operator calculi and domain-local Fourier actions
-- are useful architecture, but cannot satisfy H_A without an exact carrier
-- realization into the canonical Mellin Test.
------------------------------------------------------------------------

data MellinImplementationSearchAction : Set where
  reuseDomainLocalFourierOperator
  reuseFiniteC3CharacterAction
  inferCarrierFromSimilarFunctionShape
  recoverGammaMellinImplementationCarrier
  recoverActionOnThatImplementation
  recoverAdmissibilityTheorem
  recoverSameFormulaShiftTheorem
  : MellinImplementationSearchAction

SearchRelevant : MellinImplementationSearchAction → Set
SearchRelevant reuseDomainLocalFourierOperator = ⊥
SearchRelevant reuseFiniteC3CharacterAction = ⊥
SearchRelevant inferCarrierFromSimilarFunctionShape = ⊥
SearchRelevant recoverGammaMellinImplementationCarrier = ⊤
SearchRelevant recoverActionOnThatImplementation = ⊤
SearchRelevant recoverAdmissibilityTheorem = ⊤
SearchRelevant recoverSameFormulaShiftTheorem = ⊤

record GammaMellinImplementationRecoveryBoundary : Set where
  constructor gamma-mellin-implementation-recovery-boundary
  field
    canonicalMellinTestInterfaceAlreadyExposesModulation : Bool
    canonicalMellinTestInterfaceAlreadyExposesModulationIsFalse :
      canonicalMellinTestInterfaceAlreadyExposesModulation ≡ false

    canonicalMellinTestInterfaceAlreadyExposesConcreteFunctionCarrier : Bool
    canonicalMellinTestInterfaceAlreadyExposesConcreteFunctionCarrierIsFalse :
      canonicalMellinTestInterfaceAlreadyExposesConcreteFunctionCarrier ≡ false

    exactImplementationCarrierMayLawfullySupplyAction : Bool
    exactImplementationCarrierMayLawfullySupplyActionIsTrue :
      exactImplementationCarrierMayLawfullySupplyAction ≡ true

    analogousFourierOperatorCanReplaceCarrierIdentity : Bool
    analogousFourierOperatorCanReplaceCarrierIdentityIsFalse :
      analogousFourierOperatorCanReplaceCarrierIdentity ≡ false

    implementationCarrierIdentityAloneClosesHA : Bool
    implementationCarrierIdentityAloneClosesHAIsFalse :
      implementationCarrierIdentityAloneClosesHA ≡ false

    sameFormulaSpectralShiftStillRequired : Bool
    sameFormulaSpectralShiftStillRequiredIsTrue :
      sameFormulaSpectralShiftStillRequired ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalGammaMellinImplementationRecoveryBoundary :
  GammaMellinImplementationRecoveryBoundary
canonicalGammaMellinImplementationRecoveryBoundary =
  gamma-mellin-implementation-recovery-boundary
    false refl
    false refl
    true refl
    false refl
    false refl
    true refl
    false refl
    "Treat the public GammaMellinLayer.Test projection as an opaque facade. Recover the repository object that actually implements that Test carrier, prove literal equality to the canonical Mellin Test, and then recover the already-owned parameterized endomorphism on that implementation together with admissibility preservation and the same-RiemannExplicitFormula spectral-shift theorem. Domain-local Fourier/C3 operators remain pruned unless such a carrier identity is present."
