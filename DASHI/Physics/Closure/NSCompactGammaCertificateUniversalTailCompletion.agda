module DASHI.Physics.Closure.NSCompactGammaCertificateUniversalTailCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaFourCriticalObligations
import DASHI.Physics.Closure.NSCompactGammaGeneratedCertificateBridge as Generated
import DASHI.Physics.Closure.NSPeriodicFourierNearTriadPreYoung as Near
import DASHI.Physics.Closure.NSPeriodicFourierRadiusEightPrimitiveReduction as Tail
import DASHI.Physics.Closure.NSPeriodicFourierUniversalTailReduction as Universal

------------------------------------------------------------------------
-- Concrete successor to the predicate-only generated-certificate bridge.
--
-- A checked finite core is paired with the structured six-package universal
-- input owner.  The theorems below project actual inequalities and official-data
-- coverage from that pair.  There is still no constructor for the concrete
-- periodic carrier unless the universal analytic packages are supplied.
------------------------------------------------------------------------

record CheckedCertificateWithUniversalTailInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (S : OfficialInitialDataSetting i) : Set (lsuc i) where
  field
    finiteCore : Generated.ExactFiniteCertificateCore i
    universalInputs : Universal.UniversalPeriodicFourierTailInputs A Index S

open CheckedCertificateWithUniversalTailInputs public

certificateSuppliesFiveHalves :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  (C : CheckedCertificateWithUniversalTailInputs A Index S) →
  ∀ q τ →
  _≤_ A
    (Universal.IndexedFiveHalvesUniversal.weightedFiveHalvesSum
      (Universal.fiveHalves (universalInputs C)) q τ)
    (Universal.IndexedFiveHalvesUniversal.compactGammaEnvelope
      (Universal.fiveHalves (universalInputs C)) q τ)
certificateSuppliesFiveHalves C =
  Universal.universalFiveHalvesEndpoint (universalInputs C)

certificateSuppliesNearTriadAbsorption :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  (C : CheckedCertificateWithUniversalTailInputs A Index S) →
  ∀ q τ →
  _≤_ A
    (Near.nearTriadMagnitude
      (Universal.nearTriad (universalInputs C)) q τ)
    (_+_ A
      (Near.deltaDissipation
        (Universal.nearTriad (universalInputs C)) q τ)
      (Near.residualEnvelope
        (Universal.nearTriad (universalInputs C)) q τ))
certificateSuppliesNearTriadAbsorption C =
  Universal.universalNearTriadEndpoint (universalInputs C)

certificateSuppliesRadiusEightFarLow :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  (C : CheckedCertificateWithUniversalTailInputs A Index S) →
  ∀ q τ →
  _≤_ A
    (Tail.farLowTail
      (Tail.low (Universal.radiusEight (universalInputs C))) q τ)
    (Tail.displayedLowBudget
      (Tail.low (Universal.radiusEight (universalInputs C))) q τ)
certificateSuppliesRadiusEightFarLow C =
  Universal.universalRadiusEightFarLowEndpoint (universalInputs C)

certificateSuppliesRadiusEightFarHigh :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  (C : CheckedCertificateWithUniversalTailInputs A Index S) →
  ∀ q τ →
  _≤_ A
    (Tail.farHighTail
      (Tail.high (Universal.radiusEight (universalInputs C))) q τ)
    (Tail.displayedHighBudget
      (Tail.high (Universal.radiusEight (universalInputs C))) q τ)
certificateSuppliesRadiusEightFarHigh C =
  Universal.universalRadiusEightFarHighEndpoint (universalInputs C)

certificateSuppliesOfficialCoverage :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {S : OfficialInitialDataSetting i} →
  CheckedCertificateWithUniversalTailInputs A Index S →
  UniversalReplacementMechanism S
certificateSuppliesOfficialCoverage C =
  Universal.universalOfficialCoverageEndpoint (universalInputs C)

checkedFiniteCoreAloneSuppliesUniversalTailInputs : Bool
checkedFiniteCoreAloneSuppliesUniversalTailInputs = false

checkedCertificateCompletionProvesGlobalRegularity : Bool
checkedCertificateCompletionProvesGlobalRegularity = false
