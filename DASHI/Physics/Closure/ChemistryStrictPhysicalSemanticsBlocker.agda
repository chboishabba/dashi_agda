module DASHI.Physics.Closure.ChemistryStrictPhysicalSemanticsBlocker where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRRetargetedChannel as Retargeted
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetPolicyDecision as Policy
import DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic as Handoff
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCandidate256Witness as Candidate256
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCouplingRequirement as CrossBand

------------------------------------------------------------------------
-- W4f strict physical-semantics blocker.
--
-- The landed Candidate256 quotient/cross-band law supplies a quotient carrier,
-- a chemistry-facing L_chem witness, a time-symmetric cross-band kernel, and
-- pre-spectral/pre-scale-setting boundary propositions.  It does not supply
-- physical scale semantics.  This module therefore records the strict consumer
-- shape that would be needed, and a typed blocker naming exactly the missing
-- ingredients instead of reusing the pre-physical boundary as a physical
-- carrier.

data StrictPhysicalMissingIngredient : Set where
  missingScaleSettingLaw : StrictPhysicalMissingIngredient
  missingSpectralObservableMap : StrictPhysicalMissingIngredient
  missingBondingInterpretation : StrictPhysicalMissingIngredient
  missingEmpiricalPhysicalValidation : StrictPhysicalMissingIngredient

record StrictPhysicalBoundaryFields
  (quotientLaw :
    CrossBand.ChemistryRightLimitsQuotientCrossBandLaw) :
  Setω where
  field
    physicalScaleCarrier : Set
    spectralObservableCarrier : Set
    bondingInterpretationCarrier : Set
    empiricalValidationCarrier : Set

    scaleSettingMap :
      Handoff.QuotientCarrier quotientLaw →
      physicalScaleCarrier

    spectralObservableMap :
      Handoff.QuotientCarrier quotientLaw →
      spectralObservableCarrier

    bondingInterpretationMap :
      Handoff.QuotientCarrier quotientLaw →
      bondingInterpretationCarrier

    empiricalPhysicalValidationMap :
      Handoff.QuotientCarrier quotientLaw →
      empiricalValidationCarrier

record StrictPhysicalBoundaryPreservation
  (quotientLaw :
    CrossBand.ChemistryRightLimitsQuotientCrossBandLaw)
  (fields : StrictPhysicalBoundaryFields quotientLaw) :
  Setω where
  open StrictPhysicalBoundaryFields fields
  field
    scaleSettingLaw :
      Handoff.QuotientLawAtWitness quotientLaw →
      Set

    spectralObservableLaw :
      Handoff.QuotientLawAtWitness quotientLaw →
      Set

    bondingInterpretationLaw :
      Handoff.QuotientLawAtWitness quotientLaw →
      Set

    empiricalPhysicalValidationLaw :
      Handoff.QuotientLawAtWitness quotientLaw →
      Set

    scaleSettingPreservesLeftRight :
      (law : Handoff.QuotientLawAtWitness quotientLaw) →
      scaleSettingLaw law

    spectralObservablePreservesLeftRight :
      (law : Handoff.QuotientLawAtWitness quotientLaw) →
      spectralObservableLaw law

    bondingInterpretationPreservesLeftRight :
      (law : Handoff.QuotientLawAtWitness quotientLaw) →
      bondingInterpretationLaw law

    empiricalPhysicalValidationPreservesLeftRight :
      (law : Handoff.QuotientLawAtWitness quotientLaw) →
      empiricalPhysicalValidationLaw law

record StrictChemistryPhysicalSemanticsConsumer
  (acceptedCarrier :
    Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted)
  (quotientLaw :
    CrossBand.ChemistryRightLimitsQuotientCrossBandLaw) :
  Setω where
  field
    prePhysicalConsumer :
      Handoff.ChemistryPhysicalConsumer acceptedCarrier quotientLaw

    strictBoundaryFields :
      StrictPhysicalBoundaryFields quotientLaw

    strictBoundaryPreservation :
      StrictPhysicalBoundaryPreservation quotientLaw strictBoundaryFields

    doesNotCollapseToPreSpectralPreScale :
      List String

record ChemistryStrictPhysicalSemanticsBlocker
  (acceptedCarrier :
    Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted)
  (quotientLaw :
    CrossBand.ChemistryRightLimitsQuotientCrossBandLaw) :
  Setω where
  field
    availablePrePhysicalConsumer :
      Handoff.ChemistryPhysicalConsumer acceptedCarrier quotientLaw

    strictConsumerWouldNeed :
      StrictChemistryPhysicalSemanticsConsumer acceptedCarrier quotientLaw →
      Set

    missingIngredients :
      List StrictPhysicalMissingIngredient

    nextMissingIngredientLabel :
      String

    requiredScaleSettingLaw :
      String

    requiredSpectralObservableMap :
      String

    requiredBondingInterpretation :
      String

    requiredEmpiricalPhysicalValidation :
      String

    boundaryExplanation :
      List String

canonicalCandidate256StrictPhysicalSemanticsBlocker :
  ChemistryStrictPhysicalSemanticsBlocker
    Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted
    Candidate256.canonicalCandidate256QuotientCrossBandLaw
canonicalCandidate256StrictPhysicalSemanticsBlocker =
  record
    { availablePrePhysicalConsumer =
        Handoff.canonicalRetargetedQuotientChemistryPhysicalConsumer
    ; strictConsumerWouldNeed =
        λ consumer →
          StrictPhysicalBoundaryFields.physicalScaleCarrier
            (StrictChemistryPhysicalSemanticsConsumer.strictBoundaryFields
              consumer)
    ; missingIngredients =
        missingScaleSettingLaw
        ∷ missingSpectralObservableMap
        ∷ missingBondingInterpretation
        ∷ missingEmpiricalPhysicalValidation
        ∷ []
    ; nextMissingIngredientLabel =
        "scale-setting law for quotient classes over Candidate256"
    ; requiredScaleSettingLaw =
        "map quotient classes to a physical scale carrier and preserve L_chem at the left/right witness"
    ; requiredSpectralObservableMap =
        "map quotient classes to spectral observables without identifying that map with the pre-spectral boundary witness"
    ; requiredBondingInterpretation =
        "interpret quotient/cross-band separation as a bonding-facing structure with its own preservation law"
    ; requiredEmpiricalPhysicalValidation =
        "validate the physical interpretation against empirical payloads rather than the pre-scale/pre-spectral boundary"
    ; boundaryExplanation =
        "Candidate256 gives quotient and cross-band separation at fixed defect/promoted observables"
        ∷ "The handoff diagnostic currently consumes those classes only as pre-spectral and pre-scale-setting boundary witnesses"
        ∷ "A strict physical consumer would need separate scale, spectral, bonding, and empirical carriers plus preservation laws"
        ∷ "No such carriers or laws are present in the quotient law, so promoting now would collapse physical semantics to the pre-physical boundary"
        ∷ []
    }

canonicalCandidate256StrictPhysicalSemanticsNextMissingIngredient :
  StrictPhysicalMissingIngredient
canonicalCandidate256StrictPhysicalSemanticsNextMissingIngredient =
  missingScaleSettingLaw
