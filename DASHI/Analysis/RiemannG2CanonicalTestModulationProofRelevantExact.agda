module DASHI.Analysis.RiemannG2CanonicalTestModulationProofRelevantExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannG2ConstructedComplexAnalyticCarrierAdapterExact as Carrier
import DASHI.Analysis.RiemannG2CanonicalTestModulationHighestAlphaExact as HA

------------------------------------------------------------------------
-- PROOF-RELEVANT H_A PAYMENT
--
-- The earlier highest-alpha owner correctly fixed the SAME Test, Scalar and
-- RiemannExplicitFormula objects, but several shift/agreement coordinates were
-- deliberately represented only by Set-valued sockets.  That is sufficient as
-- an interface audit, but it is too weak as a theorem-bearing producer: merely
-- choosing a proposition is not the same as supplying its proof.
--
-- This owner upgrades the live H_A payment to actual equalities on the exact
-- selected objects.  It does not invent a new transform or character carrier.
------------------------------------------------------------------------

record ProofRelevantCanonicalTestModulation
    (analytic : Analytic.AnalyticSubstrate)
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula)
    (C : Complex.ConstructedComplexPackage)
    (F : Carrier.ConstructedComplexAnalyticFunctionLayer C)
    (realization : Carrier.CanonicalConstructedCarrierRealization analytic C F)
    : Set₁ where
  field
    -- These expected actions are not shadow carriers.  They are comparison
    -- maps on the already selected Weil Scalar/Test carrier and transform.
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

    modulateTest :
      Weil.WeilTestSpace.Scalar space →
      Weil.WeilTestSpace.Test space →
      Weil.WeilTestSpace.Test space

    modulationPreservesAdmissibility :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : Weil.WeilTestSpace.Test space) →
      Weil.WeilTestSpace.admissible space f →
      Weil.WeilTestSpace.admissible space (modulateTest t f)

    -- H_X/action agreement is now a proof, not a proposition label.
    modulateIsCanonicalCharacterAction :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : Weil.WeilTestSpace.Test space) →
      modulateTest t f ≡ expectedCharacterAction t f

    -- The spectral shift is tied literally to THIS formula's spectralZeroForm.
    sameFormulaSpectralShift :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : Weil.WeilTestSpace.Test space) →
      Explicit.RiemannExplicitFormula.spectralZeroForm formula (modulateTest t f)
      ≡ expectedShiftedSpectralResponse t f

    -- Likewise the transform theorem is on THIS WeilTestSpace.transform.
    canonicalWeilTransformShift :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : Weil.WeilTestSpace.Test space) →
      Weil.WeilTestSpace.transform space (modulateTest t f)
      ≡ expectedTransformShift t f

    producerReference : String

open ProofRelevantCanonicalTestModulation public

------------------------------------------------------------------------
-- Backward compatibility with the earlier consumer-shaped payment.
--
-- The old Set sockets are populated by the actual proposition TYPES whose
-- witnesses are carried above.  Consumers that only need the interface may use
-- the old payment; theorem-bearing work should retain the proof-relevant owner.
------------------------------------------------------------------------

toSameCarrierTestModulationPayment :
  ∀ {analytic space formula compat C F realization} →
  ProofRelevantCanonicalTestModulation
    analytic space formula compat C F realization →
  HA.SameCarrierTestModulationPayment
    analytic space formula compat C F realization
toSameCarrierTestModulationPayment P = record
  { HA.modulateTest = modulateTest P
  ; HA.modulationPreservesAdmissibility = modulationPreservesAdmissibility P
  ; HA.targetCharacterActionUsesCanonicalHX =
      (t : Weil.WeilTestSpace.Scalar _) →
      (f : Weil.WeilTestSpace.Test _) →
      modulateTest P t f ≡ expectedCharacterAction P t f
  ; HA.spectralShiftLawForSameFormula =
      (t : Weil.WeilTestSpace.Scalar _) →
      (f : Weil.WeilTestSpace.Test _) →
      Explicit.RiemannExplicitFormula.spectralZeroForm _ (modulateTest P t f)
      ≡ expectedShiftedSpectralResponse P t f
  ; HA.shiftedResponseIsConcreteFormulaSpectralResponse =
      (t : Weil.WeilTestSpace.Scalar _) →
      (f : Weil.WeilTestSpace.Test _) →
      Explicit.RiemannExplicitFormula.spectralZeroForm _ (modulateTest P t f)
      ≡ expectedShiftedSpectralResponse P t f
  ; HA.transformShiftUsesCanonicalWeilTransform =
      (t : Weil.WeilTestSpace.Scalar _) →
      (f : Weil.WeilTestSpace.Test _) →
      Weil.WeilTestSpace.transform _ (modulateTest P t f)
      ≡ expectedTransformShift P t f
  ; HA.paymentReference = producerReference P
  }

------------------------------------------------------------------------
-- Consumer-relative BIDI boundary.
------------------------------------------------------------------------

data ModulationEvidenceLevel : Set where
  interfaceSocket
  namedProducer
  proofRelevantSameObjectProducer
  : ModulationEvidenceLevel

AcceptedForTheoremBearingHA : ModulationEvidenceLevel → Set
AcceptedForTheoremBearingHA interfaceSocket = ⊥
AcceptedForTheoremBearingHA namedProducer = ⊥
AcceptedForTheoremBearingHA proofRelevantSameObjectProducer = ⊤

interfaceSocketNotEnough :
  AcceptedForTheoremBearingHA interfaceSocket → ⊥
interfaceSocketNotEnough x = x

namedProducerNotEnough :
  AcceptedForTheoremBearingHA namedProducer → ⊥
namedProducerNotEnough x = x

record CanonicalTestModulationProofRelevantBoundary : Set where
  constructor canonical-test-modulation-proof-relevant-boundary
  field
    choosingSetValuedShiftSocketCountsAsShiftProof : Bool
    choosingSetValuedShiftSocketCountsAsShiftProofIsFalse :
      choosingSetValuedShiftSocketCountsAsShiftProof ≡ false

    exactModulationEndomorphismRequired : Bool
    exactModulationEndomorphismRequiredIsTrue :
      exactModulationEndomorphismRequired ≡ true

    admissibilityWitnessRequired : Bool
    admissibilityWitnessRequiredIsTrue : admissibilityWitnessRequired ≡ true

    sameFormulaSpectralEqualityRequired : Bool
    sameFormulaSpectralEqualityRequiredIsTrue :
      sameFormulaSpectralEqualityRequired ≡ true

    sameWeilTransformEqualityRequired : Bool
    sameWeilTransformEqualityRequiredIsTrue :
      sameWeilTransformEqualityRequired ≡ true

    genericMonsterOrFiniteCharacterActionCanPayThisRHCarrier : Bool
    genericMonsterOrFiniteCharacterActionCanPayThisRHCarrierIsFalse :
      genericMonsterOrFiniteCharacterActionCanPayThisRHCarrier ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalTestModulationProofRelevantBoundary :
  CanonicalTestModulationProofRelevantBoundary
canonicalTestModulationProofRelevantBoundary =
  canonical-test-modulation-proof-relevant-boundary
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "Recover the existing target-character endomorphism on the literal Weil Test carrier and retain its admissibility proof, same-RiemannExplicitFormula spectral equality, and same-Weil-transform shift equality as first-class witnesses. Set-valued interface sockets and name-only donors are search metadata, not theorem payments. Finite Monster/Heisenberg character actions remain useful action architecture but cannot inhabit this analytic same-carrier payment without an exact carrier realization."
