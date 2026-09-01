module DASHI.Analysis.RiemannG2HAConsumerQuotientActiveSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannG2ConstructedComplexAnalyticCarrierAdapterExact as Carrier
import DASHI.Analysis.RiemannG2CanonicalTestModulationProofRelevantExact as StrongHA
import DASHI.Analysis.RiemannG2GammaMellinProofRelevantActionCompilerExact as Compiler
import DASHI.Analysis.RiemannG2SourceNativePhiHatModulationAdapterExact as Source
import DASHI.Computation.SSSPConsumerInvariantSymmetryQuotientExact as Quot
import DASHI.Reasoning.AristotleActiveExperimentalProofSearchLoopExact as Active

------------------------------------------------------------------------
-- SOURCE-NATIVE H_A FINAL COMPILER + CONSUMER-QUOTIENT SEARCH
--
-- Master now contains both sides of the representation seam:
--
--   source-native phiHat/taper action
--      -> concrete Gamma/Mellin implementation action
--      -> proof-relevant canonical Weil-test modulation.
--
-- The first theorem below composes those already-owned compilers.  Therefore
-- no additional H_A interface is needed: once the source-native action proof
-- and canonical carrier realization are recovered, H_A is a compiler output.
--
-- The second half cross-pollinates merged #681 and #678 literally.  Recovery
-- metadata may vary while the theorem consumer sees the same exact evidence;
-- such variation is quotient-invisible to the mathematical H_A consumer but
-- remains visible to the independent provenance/source-audit consumer.
------------------------------------------------------------------------

sourceNativeToProofRelevantCanonicalHA :
  ∀ {analytic space formula compat C F realization} →
  (P : Source.SourceNativePhiHatModulation analytic space formula compat) →
  Source.SourceNativePhiHatModulationProof P →
  StrongHA.ProofRelevantCanonicalTestModulation
    analytic space formula compat C F realization
sourceNativeToProofRelevantCanonicalHA P proof =
  Compiler.toProofRelevantCanonicalTestModulation
    (Source.toProofRelevantImplementedMellinAction P proof)

------------------------------------------------------------------------
-- 1. Exact recovery evidence coordinates.
------------------------------------------------------------------------

data Evidence : Set where
  missing owned : Evidence

data Provenance : Set where
  anonymous sourceNative : Provenance

record HARecoveryState : Set where
  constructor ha-recovery-state
  field
    implementationIdentityEvidence : Evidence
    actionEvidence : Evidence
    admissibilityEvidence : Evidence
    canonicalHXAgreementEvidence : Evidence
    sameFormulaShiftEvidence : Evidence
    sameWeilTransformShiftEvidence : Evidence
    provenanceEvidence : Provenance

open HARecoveryState public

record HAMathematicalObservation : Set where
  constructor ha-mathematical-observation
  field
    implementationIdentityObserved : Evidence
    actionObserved : Evidence
    admissibilityObserved : Evidence
    canonicalHXAgreementObserved : Evidence
    sameFormulaShiftObserved : Evidence
    sameWeilTransformShiftObserved : Evidence

open HAMathematicalObservation public

observeHAMathematics : HARecoveryState → HAMathematicalObservation
observeHAMathematics
  (ha-recovery-state impl action admissible hx formulaShift weilShift provenance) =
  ha-mathematical-observation
    impl action admissible hx formulaShift weilShift

observeHAProvenance : HARecoveryState → Provenance
observeHAProvenance = provenanceEvidence

------------------------------------------------------------------------
-- 2. Consumer quotient: changing provenance alone cannot change the exact
-- mathematical H_A evidence surface.
------------------------------------------------------------------------

data ProvenanceSymmetry : Set where
  keepProvenance flipProvenance : ProvenanceSymmetry

composeProvenance : ProvenanceSymmetry → ProvenanceSymmetry → ProvenanceSymmetry
composeProvenance keepProvenance g = g
composeProvenance flipProvenance keepProvenance = flipProvenance
composeProvenance flipProvenance flipProvenance = keepProvenance

flipProvenanceValue : Provenance → Provenance
flipProvenanceValue anonymous = sourceNative
flipProvenanceValue sourceNative = anonymous

actProvenance : ProvenanceSymmetry → HARecoveryState → HARecoveryState
actProvenance keepProvenance s = s
actProvenance flipProvenance
  (ha-recovery-state impl action admissible hx formulaShift weilShift provenance) =
  ha-recovery-state
    impl action admissible hx formulaShift weilShift
    (flipProvenanceValue provenance)

provenanceIdentityActs :
  (s : HARecoveryState) →
  actProvenance keepProvenance s ≡ s
provenanceIdentityActs s = refl

provenanceActionComposes :
  (g h : ProvenanceSymmetry) (s : HARecoveryState) →
  actProvenance (composeProvenance g h) s ≡
  actProvenance g (actProvenance h s)
provenanceActionComposes keepProvenance keepProvenance s = refl
provenanceActionComposes keepProvenance flipProvenance s = refl
provenanceActionComposes flipProvenance keepProvenance s = refl
provenanceActionComposes flipProvenance flipProvenance
  (ha-recovery-state impl action admissible hx formulaShift weilShift anonymous) = refl
provenanceActionComposes flipProvenance flipProvenance
  (ha-recovery-state impl action admissible hx formulaShift weilShift sourceNative) = refl

haMathematicsInvariantUnderProvenance :
  (g : ProvenanceSymmetry) (s : HARecoveryState) →
  observeHAMathematics (actProvenance g s) ≡ observeHAMathematics s
haMathematicsInvariantUnderProvenance keepProvenance s = refl
haMathematicsInvariantUnderProvenance flipProvenance
  (ha-recovery-state impl action admissible hx formulaShift weilShift provenance) = refl

haMathematicalConsumerQuotient : Quot.ConsumerInvariantAction
haMathematicalConsumerQuotient =
  Quot.consumerInvariantAction
    HARecoveryState
    ProvenanceSymmetry
    HAMathematicalObservation
    keepProvenance
    composeProvenance
    actProvenance
    observeHAMathematics
    provenanceIdentityActs
    provenanceActionComposes
    haMathematicsInvariantUnderProvenance

mathReadyAnonymous : HARecoveryState
mathReadyAnonymous =
  ha-recovery-state owned owned owned owned owned owned anonymous

mathReadySourceNative : HARecoveryState
mathReadySourceNative =
  ha-recovery-state owned owned owned owned owned owned sourceNative

mathReadyStatesShareConsumerOrbit :
  Quot.SameActionOrbit
    haMathematicalConsumerQuotient
    mathReadyAnonymous
    mathReadySourceNative
mathReadyStatesShareConsumerOrbit =
  Quot.sameActionOrbit flipProvenance refl

mathReadyStatesHaveSameMathematicalObservation :
  observeHAMathematics mathReadyAnonymous ≡
  observeHAMathematics mathReadySourceNative
mathReadyStatesHaveSameMathematicalObservation =
  Quot.orbitRelatedStatesAreConsumerEquivalent
    haMathematicalConsumerQuotient
    mathReadyAnonymous
    mathReadySourceNative
    mathReadyStatesShareConsumerOrbit

sourceAuditStillDistinguishesProvenance :
  observeHAProvenance mathReadySourceNative ≡
  observeHAProvenance mathReadyAnonymous → ⊥
sourceAuditStillDistinguishesProvenance ()

------------------------------------------------------------------------
-- 3. BIDI scheduler: probe only the first consumer-relevant missing receipt.
-- Once all theorem receipts are owned, provenance is a separate audit probe;
-- once that is source-native too, compilation is the next action.
------------------------------------------------------------------------

data HARecoveryProbe : Set where
  recoverImplementationIdentity
  recoverParameterizedAction
  recoverAdmissibility
  recoverCanonicalHXAgreement
  recoverSameFormulaSpectralShift
  recoverSameWeilTransformShift
  recoverSourceProvenance
  compileProofRelevantHA
  : HARecoveryProbe

nextHARecoveryProbe : HARecoveryState → HARecoveryProbe
nextHARecoveryProbe
  (ha-recovery-state missing action admissible hx formulaShift weilShift provenance) =
  recoverImplementationIdentity
nextHARecoveryProbe
  (ha-recovery-state owned missing admissible hx formulaShift weilShift provenance) =
  recoverParameterizedAction
nextHARecoveryProbe
  (ha-recovery-state owned owned missing hx formulaShift weilShift provenance) =
  recoverAdmissibility
nextHARecoveryProbe
  (ha-recovery-state owned owned owned missing formulaShift weilShift provenance) =
  recoverCanonicalHXAgreement
nextHARecoveryProbe
  (ha-recovery-state owned owned owned owned missing weilShift provenance) =
  recoverSameFormulaSpectralShift
nextHARecoveryProbe
  (ha-recovery-state owned owned owned owned owned missing provenance) =
  recoverSameWeilTransformShift
nextHARecoveryProbe
  (ha-recovery-state owned owned owned owned owned owned anonymous) =
  recoverSourceProvenance
nextHARecoveryProbe
  (ha-recovery-state owned owned owned owned owned owned sourceNative) =
  compileProofRelevantHA

activeSearchCanCloseOnConsumerWithoutFullHiddenIdentity :
  Active.proofSearchMustIdentifyCompleteHiddenStateBeforeClosing
    Active.canonicalActiveExperimentalProofSearchBoundary ≡ false
activeSearchCanCloseOnConsumerWithoutFullHiddenIdentity =
  Active.proofSearchMustIdentifyCompleteHiddenStateBeforeClosingIsFalse
    Active.canonicalActiveExperimentalProofSearchBoundary

------------------------------------------------------------------------
-- 4. Boundary.
------------------------------------------------------------------------

record HAConsumerQuotientActiveSearchBoundary : Set where
  constructor ha-consumer-quotient-active-search-boundary
  field
    sourceNativeCompilerPathAlreadyComposesToProofRelevantHA : Bool
    sourceNativeCompilerPathAlreadyComposesToProofRelevantHAIsTrue :
      sourceNativeCompilerPathAlreadyComposesToProofRelevantHA ≡ true

    provenanceChangeAloneChangesHAMathematicalConsumer : Bool
    provenanceChangeAloneChangesHAMathematicalConsumerIsFalse :
      provenanceChangeAloneChangesHAMathematicalConsumer ≡ false

    provenanceCanBeDiscardedFromSourceAudit : Bool
    provenanceCanBeDiscardedFromSourceAuditIsFalse :
      provenanceCanBeDiscardedFromSourceAudit ≡ false

    searchMustRebuildGenericFourierOrMellinTheory : Bool
    searchMustRebuildGenericFourierOrMellinTheoryIsFalse :
      searchMustRebuildGenericFourierOrMellinTheory ≡ false

    firstMissingConsumerReceiptCanDriveNextProbe : Bool
    firstMissingConsumerReceiptCanDriveNextProbeIsTrue :
      firstMissingConsumerReceiptCanDriveNextProbe ≡ true

    mergedSSSPConsumerQuotientUsedAsArchitecture : Bool
    mergedSSSPConsumerQuotientUsedAsArchitectureIsTrue :
      mergedSSSPConsumerQuotientUsedAsArchitecture ≡ true

    mergedAristotleActiveSearchUsedAsArchitecture : Bool
    mergedAristotleActiveSearchUsedAsArchitectureIsTrue :
      mergedAristotleActiveSearchUsedAsArchitecture ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalHAConsumerQuotientActiveSearchBoundary :
  HAConsumerQuotientActiveSearchBoundary
canonicalHAConsumerQuotientActiveSearchBoundary =
  ha-consumer-quotient-active-search-boundary
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    "The source-native phiHat -> Gamma/Mellin implementation -> proof-relevant canonical H_A compiler chain is now composed explicitly. Do not construct another modulation interface or generic Fourier theory. Recover only the first missing theorem-bearing receipt on the literal selected objects: implementation identity, action, admissibility, canonical H_X agreement, same-formula spectral shift, then same-Weil-transform shift. Merged SSSP consumer-quotient discipline proves that provenance-only variation is invisible to the mathematical H_A consumer, while the independent source-audit consumer still distinguishes it. Merged Aristotle active-search discipline therefore justifies probing only consumer-relevant residual coordinates and stopping mathematical recovery once the exact H_A consumer closes; source provenance remains a separate admission/audit obligation. RH is not derived."
