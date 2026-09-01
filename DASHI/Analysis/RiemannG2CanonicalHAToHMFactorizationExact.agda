module DASHI.Analysis.RiemannG2CanonicalHAToHMFactorizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannAnalyticComplexCharacterExtensionExact as Character
import DASHI.Analysis.RiemannAnalyticModulationExtensionExact as HM
import DASHI.Analysis.RiemannG2ConstructedComplexAnalyticCarrierAdapterExact as Carrier
import DASHI.Analysis.RiemannG2CanonicalTestModulationProofRelevantExact as StrongHA

------------------------------------------------------------------------
-- H_M REDUCTION AFTER PROOF-RELEVANT H_A
--
-- The historical H_M record contains a richer pointwise phase-action surface
-- than the newer proof-relevant H_A.  Most H_M fields are already supplied by
-- canonical H_X or proof-relevant H_A.  The genuinely additional theorem is a
-- factorisation of the SAME modulated test response through the H_X character
-- action at each (b,u).
--
-- This owner isolates exactly that factorisation.  Once it is supplied, H_M is
-- compiler output; no second modulation endomorphism or fresh character theory
-- is needed.
------------------------------------------------------------------------

record CanonicalHMFactorizationBridge
    {analytic : Analytic.AnalyticSubstrate}
    {space : Weil.WeilTestSpace}
    {formula : Explicit.RiemannExplicitFormula space}
    {compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula}
    {C : _}
    {F : Carrier.ConstructedComplexAnalyticFunctionLayer C}
    {realization : Carrier.CanonicalConstructedCarrierRealization analytic C F}
    (H_X : Character.RiemannComplexCharacterExtension analytic)
    (H_A : StrongHA.ProofRelevantCanonicalTestModulation
      analytic space formula compat C F realization)
    : Set₁ where
  field
    -- H_M uses the canonical H_X real carrier as ordinate/frequency.  H_A uses
    -- the canonical Weil scalar.  This is the only target-carrier transport
    -- operation needed by the compiler.
    toWeilTarget :
      Character.RealCarrier H_X → Weil.WeilTestSpace.Scalar space

    SpectralResponse : Set
    spectralResponse :
      Weil.WeilTestSpace.Test space →
      Character.RealCarrier H_X →
      Character.RealCarrier H_X →
      SpectralResponse

    phaseAct :
      Character.ComplexCarrier H_X →
      SpectralResponse →
      SpectralResponse

    -- The one genuinely stronger H_M theorem: the proof-relevant H_A action
    -- factors through the literal H_X target character on the same response.
    spectralShiftFactorization :
      (t b u : Character.RealCarrier H_X) →
      (f : Weil.WeilTestSpace.Test space) →
      spectralResponse
        (StrongHA.modulateTest H_A (toWeilTarget t) f) b u
      ≡ phaseAct
          (Character.targetCharacter H_X t u)
          (spectralResponse f b u)

    factorizationReference : String

open CanonicalHMFactorizationBridge public

canonicalHXAndProofRelevantHAToHM :
  ∀ {analytic space formula compat C F realization} →
  (H_X : Character.RiemannComplexCharacterExtension analytic) →
  (H_A : StrongHA.ProofRelevantCanonicalTestModulation
    analytic space formula compat C F realization) →
  CanonicalHMFactorizationBridge H_X H_A →
  HM.RiemannAnalyticModulationExtension analytic space formula compat
canonicalHXAndProofRelevantHAToHM H_X H_A bridge =
  HM.riemann-analytic-modulation-extension
    -- carrierAgreementUsed
    ⊤
    -- concreteExplicitFormulaAgreementUsed
    ⊤
    -- Ordinate / Frequency
    (Character.RealCarrier H_X)
    (Character.RealCarrier H_X)
    -- targetDifference
    (Character.subR H_X)
    -- targetDifferenceIsSubtract
    ((b t : Character.RealCarrier H_X) →
      Character.subR H_X b t
      ≡ Character.addR H_X b (Character.negR H_X t))
    -- Character / multiplication
    (Character.ComplexCarrier H_X)
    (Character.mulC H_X)
    -- targetCharacter: H_M orders frequency before target
    (λ u t → Character.targetCharacter H_X t u)
    -- zeroCharacter: unshifted source phase exp(+ i b u)
    (λ u b → Character.sourceCharacter H_X b u)
    -- modulateTest
    (λ t f → StrongHA.modulateTest H_A (toWeilTarget bridge t) f)
    -- admissibility
    (λ t f adm →
      StrongHA.modulationPreservesAdmissibility H_A
        (toWeilTarget bridge t) f adm)
    -- SpectralResponse / response / phase action
    (SpectralResponse bridge)
    (spectralResponse bridge)
    (phaseAct bridge)
    -- theorem-bearing factorisation
    (spectralShiftFactorization bridge)
    -- response belongs to same concrete formula: legacy Set socket
    ((t b u : Character.RealCarrier H_X) →
      (f : Weil.WeilTestSpace.Test _) → Set)
    -- H_X character proposition sockets
    ((t u : Character.RealCarrier H_X) →
      Character.targetCharacter H_X t u
      ≡ Character.expC H_X (Character.minusIProduct H_X t u))
    ((b u : Character.RealCarrier H_X) →
      Character.sourceCharacter H_X b u
      ≡ Character.expC H_X (Character.plusIProduct H_X b u))
    ((b t u : Character.RealCarrier H_X) →
      Character.mulC H_X
        (Character.targetCharacter H_X t u)
        (Character.sourceCharacter H_X b u)
      ≡ Character.gapCharacter H_X b t u)
    (factorizationReference bridge)

------------------------------------------------------------------------
-- Search consequences.
------------------------------------------------------------------------

data HMSearchAction : Set where
  rebuildTargetCharacterTheory
  rebuildTestModulation
  recoverCanonicalPhaseActionFactorization
  compileHistoricalHM
  recoverHTAdapter
  : HMSearchAction

data SearchStatus : Set where
  live pruned downstream : SearchStatus

searchStatus : HMSearchAction → SearchStatus
searchStatus rebuildTargetCharacterTheory = pruned
searchStatus rebuildTestModulation = pruned
searchStatus recoverCanonicalPhaseActionFactorization = live
searchStatus compileHistoricalHM = downstream
searchStatus recoverHTAdapter = downstream

characterRebuildPruned : searchStatus rebuildTargetCharacterTheory ≡ pruned
characterRebuildPruned = refl

testModulationRebuildPruned : searchStatus rebuildTestModulation ≡ pruned
testModulationRebuildPruned = refl

record CanonicalHAToHMFactorizationBoundary : Set where
  constructor canonical-ha-to-hm-factorization-boundary
  field
    hMNeedsFreshCharacterTheory : Bool
    hMNeedsFreshCharacterTheoryIsFalse : hMNeedsFreshCharacterTheory ≡ false

    hMNeedsFreshTestModulation : Bool
    hMNeedsFreshTestModulationIsFalse : hMNeedsFreshTestModulation ≡ false

    oneAdditionalPhaseActionFactorizationIsSufficient : Bool
    oneAdditionalPhaseActionFactorizationIsSufficientIsTrue :
      oneAdditionalPhaseActionFactorizationIsSufficient ≡ true

    historicalHMCompilerClosedConditionally : Bool
    historicalHMCompilerClosedConditionallyIsTrue :
      historicalHMCompilerClosedConditionally ≡ true

    factorizationRecoveredHere : Bool
    factorizationRecoveredHereIsFalse : factorizationRecoveredHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalHAToHMFactorizationBoundary : CanonicalHAToHMFactorizationBoundary
canonicalHAToHMFactorizationBoundary =
  canonical-ha-to-hm-factorization-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "After canonical H_X and proof-relevant H_A are owned, historical H_M does not require another character theory or another modulation endomorphism. Its genuinely stronger content is one same-object pointwise factorisation: the modulated spectral response must equal the action of the literal H_X target character on the unmodulated response. Supply that bridge plus target-carrier transport and the historical H_M record is compiler output. The factorisation itself is not recovered here and RH is not derived."
