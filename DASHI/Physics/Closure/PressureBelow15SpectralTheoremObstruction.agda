module DASHI.Physics.Closure.PressureBelow15SpectralTheoremObstruction where

-- Pressure-below-15 spectral theorem obstruction.
--
-- Worker-B scope: sharpen the W9 pressure-to-spectral-gap obligation without
-- promoting it.  The repo proves the arithmetic pressureBound = 14 < 15 and
-- the carrier-natural deficit 15 - 14 = 1.  It does not currently contain the
-- analytic/coercive theorem that would turn that strict inequality into a
-- Yang-Mills spectral gap.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_<_; _≤_; _∸_; _*_)
open import Data.Nat.Properties as NatP using (≤-trans)
open import Relation.Nullary using (¬_)

open import MonsterOntos using (SSP; p3; p5; p7)
open import Ontology.GodelLattice using (FactorVec)

import DASHI.Quantum.Stone as Stone
import DASHI.Unifier as U
import DASHI.Foundations.RealAnalysisAxioms as RA
import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface as MassGap
import DASHI.Physics.Closure.G2SFGCGaugeFieldSchemaExtension as G2SFGCS
import DASHI.Physics.Closure.PressureBelow15SpectralProbe as Probe
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YM
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftFiniteGaugeSymmetry as SFGS
import DASHI.Physics.ShiftPhaseTableInterference as SPTI4

data PressureBelow15SpectralRequiredHypothesis : Set where
  requiresYangMillsHamiltonianCarrier :
    PressureBelow15SpectralRequiredHypothesis
  requiresVacuumAndNonVacuumSector :
    PressureBelow15SpectralRequiredHypothesis
  requiresVacuumOrthogonalityPredicate :
    PressureBelow15SpectralRequiredHypothesis
  requiresEnergyOrderAndPositiveGapUnit :
    PressureBelow15SpectralRequiredHypothesis
  requiresPressureEnergyCoercivity :
    PressureBelow15SpectralRequiredHypothesis
  requiresSubThresholdLowerBound :
    PressureBelow15SpectralRequiredHypothesis
  requiresCarrierUnitNormalization :
    PressureBelow15SpectralRequiredHypothesis

data S8PressureBelow15LocalTheoremField : Set where
  s8YangMillsHamiltonianCarrierField :
    S8PressureBelow15LocalTheoremField
  s8VacuumNonVacuumSectorField :
    S8PressureBelow15LocalTheoremField
  s8VacuumOrthogonalityField :
    S8PressureBelow15LocalTheoremField
  s8EnergyOrderAndPositiveGapUnitField :
    S8PressureBelow15LocalTheoremField
  s8PressureEnergyCoercivityWitnessField :
    S8PressureBelow15LocalTheoremField
  s8CarrierUnitNormalizationWitnessField :
    S8PressureBelow15LocalTheoremField
  s8LowerBoundTransportField :
    S8PressureBelow15LocalTheoremField
  s8SpectralWitnessIdentificationField :
    S8PressureBelow15LocalTheoremField

data S8PressureEnergyCoercivityPrimitiveField : Set where
  s8PressureNormSquaredField :
    S8PressureEnergyCoercivityPrimitiveField

  s8PressureOrderTransitivityField :
    S8PressureEnergyCoercivityPrimitiveField

  s8GapUnitDominatedByPressureNormField :
    S8PressureEnergyCoercivityPrimitiveField

  s8LaneHamiltonianDominatesPressureNormField :
    S8PressureEnergyCoercivityPrimitiveField

  s8PressureEnergyCoercivityCompilerField :
    S8PressureEnergyCoercivityPrimitiveField

data S8LaneHamiltonianDominanceDefinitionField : Set where
  s8YangMillsHamiltonianLaneDecompositionDefinitionField :
    S8LaneHamiltonianDominanceDefinitionField

  s8LaneOccupationNumberDefinitionField :
    S8LaneHamiltonianDominanceDefinitionField

  s8PressureNormSquaredLaneWeightDefinitionField :
    S8LaneHamiltonianDominanceDefinitionField

  s8MinimumNontrivialHolonomyDistanceDefinitionField :
    S8LaneHamiltonianDominanceDefinitionField

  s8LaneEnergyOrderCompatibilityDefinitionField :
    S8LaneHamiltonianDominanceDefinitionField

  s8LaneSumDominanceToGlobalDominanceCompilerField :
    S8LaneHamiltonianDominanceDefinitionField

data S8LaneSumDominanceCompilerMissingField : Set where
  s8P3WeightedLanePressureDominatedByLaneHamiltonianField :
    S8LaneSumDominanceCompilerMissingField

  s8P5WeightedLanePressureDominatedByLaneHamiltonianField :
    S8LaneSumDominanceCompilerMissingField

  s8P7WeightedLanePressureDominatedByLaneHamiltonianField :
    S8LaneSumDominanceCompilerMissingField

  s8PressureNormWeightedLaneSumExpansionField :
    S8LaneSumDominanceCompilerMissingField

  s8ThreeLaneWeightedPressureSumMonotonicityField :
    S8LaneSumDominanceCompilerMissingField

  s8HamiltonianActiveLaneSumTransportField :
    S8LaneSumDominanceCompilerMissingField

data S8LaneEnergyOrderCompatibilityMissingPrimitive : Set where
  s8WeightedPressureFiniteLaneOrderArithmeticCompatibilityPrimitive :
    S8LaneEnergyOrderCompatibilityMissingPrimitive

data S8PressureEnergyCoercivityCompilerMissingField : Set where
  s8PrimitiveInterfaceToPackagePressureEnergyCoerciveCompilerField :
    S8PressureEnergyCoercivityCompilerMissingField

canonicalS8PressureBelow15LocalTheoremFields :
  List S8PressureBelow15LocalTheoremField
canonicalS8PressureBelow15LocalTheoremFields =
  s8YangMillsHamiltonianCarrierField
  ∷ s8VacuumNonVacuumSectorField
  ∷ s8VacuumOrthogonalityField
  ∷ s8EnergyOrderAndPositiveGapUnitField
  ∷ s8PressureEnergyCoercivityWitnessField
  ∷ s8CarrierUnitNormalizationWitnessField
  ∷ s8LowerBoundTransportField
  ∷ s8SpectralWitnessIdentificationField
  ∷ []

canonicalS8PressureEnergyCoercivityPrimitiveFields :
  List S8PressureEnergyCoercivityPrimitiveField
canonicalS8PressureEnergyCoercivityPrimitiveFields =
  s8PressureNormSquaredField
  ∷ s8PressureOrderTransitivityField
  ∷ s8GapUnitDominatedByPressureNormField
  ∷ s8LaneHamiltonianDominatesPressureNormField
  ∷ s8PressureEnergyCoercivityCompilerField
  ∷ []

canonicalS8LaneHamiltonianDominanceDefinitionFields :
  List S8LaneHamiltonianDominanceDefinitionField
canonicalS8LaneHamiltonianDominanceDefinitionFields =
  s8YangMillsHamiltonianLaneDecompositionDefinitionField
  ∷ s8LaneOccupationNumberDefinitionField
  ∷ s8PressureNormSquaredLaneWeightDefinitionField
  ∷ s8MinimumNontrivialHolonomyDistanceDefinitionField
  ∷ s8LaneEnergyOrderCompatibilityDefinitionField
  ∷ s8LaneSumDominanceToGlobalDominanceCompilerField
  ∷ []

canonicalS8LaneSumDominanceCompilerMissingFields :
  List S8LaneSumDominanceCompilerMissingField
canonicalS8LaneSumDominanceCompilerMissingFields =
  s8P3WeightedLanePressureDominatedByLaneHamiltonianField
  ∷ s8P5WeightedLanePressureDominatedByLaneHamiltonianField
  ∷ s8P7WeightedLanePressureDominatedByLaneHamiltonianField
  ∷ s8PressureNormWeightedLaneSumExpansionField
  ∷ s8ThreeLaneWeightedPressureSumMonotonicityField
  ∷ s8HamiltonianActiveLaneSumTransportField
  ∷ []

canonicalS8LaneEnergyOrderCompatibilityMissingPrimitives :
  List S8LaneEnergyOrderCompatibilityMissingPrimitive
canonicalS8LaneEnergyOrderCompatibilityMissingPrimitives =
  s8WeightedPressureFiniteLaneOrderArithmeticCompatibilityPrimitive
  ∷ []

canonicalS8PressureEnergyCoercivityCompilerMissingFields :
  List S8PressureEnergyCoercivityCompilerMissingField
canonicalS8PressureEnergyCoercivityCompilerMissingFields =
  s8PrimitiveInterfaceToPackagePressureEnergyCoerciveCompilerField
  ∷ []

data S8PressurePackageMechanicalVerdict : Set where
  packageDoesNotMechanicallyYieldGapReceipt :
    S8PressurePackageMechanicalVerdict

data PressureBelow15SpectralObstructionSelection : Set where
  canonicalProbeSelected :
    PressureBelow15SpectralObstructionSelection
  sharpenedTheoremStatementSelected :
    PressureBelow15SpectralObstructionSelection

data PressureBelow15SpectralExactMissingTheorem : Set where
  s8PressureBelow15ToYangMillsSpectralGapTheoremMissing :
    PressureBelow15SpectralExactMissingTheorem

data PressureBelow15SpectralGapReceiptPolicy : Set where
  gapReceiptOnlyFromInhabitedS8Theorem :
    PressureBelow15SpectralGapReceiptPolicy

data S8GlobalYangMillsHamiltonianCarrierMissingTheorem : Set where
  missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient :
    S8GlobalYangMillsHamiltonianCarrierMissingTheorem

data S8GlobalYangMillsHamiltonianCarrierBlockerVerdict : Set where
  globalCarrierTheoremRequiredBeforeS8SpectralGap :
    S8GlobalYangMillsHamiltonianCarrierBlockerVerdict

data S8CarrierEvidenceKind : Set where
  boundedNatCarrierEvidence :
    S8CarrierEvidenceKind

  realPhysicalCarrierEvidence :
    S8CarrierEvidenceKind

data S8NonVacuumSpectralLowerBoundTarget : Set where
  infSigmaHYMGreaterThanZeroOnNonVacuumCarrier :
    S8NonVacuumSpectralLowerBoundTarget

data S8RealCarrierRequiredTheoremTarget : Set where
  selfAdjointYangMillsHamiltonianOnRealCarrierQuotientTarget :
    S8RealCarrierRequiredTheoremTarget

data S8RealCarrierHardExternalHalt : Set where
  uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient :
    S8RealCarrierHardExternalHalt

data S8RealNonNatCarrierStagingField : Set where
  realCarrierIsRealAnalysisCarrierField :
    S8RealNonNatCarrierStagingField

  realCarrierIsNotBoundedNatSliceField :
    S8RealNonNatCarrierStagingField

  realHamiltonianSelfAdjointTargetField :
    S8RealNonNatCarrierStagingField

  realNonVacuumLowerBoundTargetField :
    S8RealNonNatCarrierStagingField

  uniformBalabanOrAgawaExternalHaltField :
    S8RealNonNatCarrierStagingField

canonicalS8RealNonNatCarrierStagingFields :
  List S8RealNonNatCarrierStagingField
canonicalS8RealNonNatCarrierStagingFields =
  realCarrierIsRealAnalysisCarrierField
  ∷ realCarrierIsNotBoundedNatSliceField
  ∷ realHamiltonianSelfAdjointTargetField
  ∷ realNonVacuumLowerBoundTargetField
  ∷ uniformBalabanOrAgawaExternalHaltField
  ∷ []

data S8SelfAdjointHamiltonianBlockerField : Set where
  missingHamiltonianOperatorOnRealCarrierQuotientField :
    S8SelfAdjointHamiltonianBlockerField

  missingDenseDomainAndSymmetryField :
    S8SelfAdjointHamiltonianBlockerField

  missingSelfAdjointExtensionOrEssentialSelfAdjointnessField :
    S8SelfAdjointHamiltonianBlockerField

  missingStoneEvolutionCompatibilityField :
    S8SelfAdjointHamiltonianBlockerField

canonicalS8SelfAdjointHamiltonianBlockerFields :
  List S8SelfAdjointHamiltonianBlockerField
canonicalS8SelfAdjointHamiltonianBlockerFields =
  missingHamiltonianOperatorOnRealCarrierQuotientField
  ∷ missingDenseDomainAndSymmetryField
  ∷ missingSelfAdjointExtensionOrEssentialSelfAdjointnessField
  ∷ missingStoneEvolutionCompatibilityField
  ∷ []

s8RealPhysicalCarrier :
  Set
s8RealPhysicalCarrier =
  RA.ℝ

s8InfSigmaHYMGreaterThanZeroTarget :
  RA.ℝ →
  Set
s8InfSigmaHYMGreaterThanZeroTarget infSigmaHYM =
  RA._<ℝ_ RA.0ℝ infSigmaHYM

record S8RealNonNatCarrierStagingReceipt : Setω where
  field
    realCarrier :
      Set

    realCarrierIsS8RealPhysicalCarrier :
      realCarrier
      ≡
      s8RealPhysicalCarrier

    realCarrierKind :
      S8CarrierEvidenceKind

    realCarrierKindIsRealPhysical :
      realCarrierKind
      ≡
      realPhysicalCarrierEvidence

    boundedNatCarrierKind :
      S8CarrierEvidenceKind

    boundedNatCarrierKindIsBoundedNat :
      boundedNatCarrierKind
      ≡
      boundedNatCarrierEvidence

    stagingFields :
      List S8RealNonNatCarrierStagingField

    stagingFieldsAreCanonical :
      stagingFields
      ≡
      canonicalS8RealNonNatCarrierStagingFields

    requiredRealCarrierTheorem :
      S8RealCarrierRequiredTheoremTarget

    requiredRealCarrierTheoremIsSelfAdjointHamiltonianOnRealCarrier :
      requiredRealCarrierTheorem
      ≡
      selfAdjointYangMillsHamiltonianOnRealCarrierQuotientTarget

    nonVacuumLowerBoundTarget :
      S8NonVacuumSpectralLowerBoundTarget

    nonVacuumLowerBoundTargetIsInfSigmaPositive :
      nonVacuumLowerBoundTarget
      ≡
      infSigmaHYMGreaterThanZeroOnNonVacuumCarrier

    hardExternalHalt :
      S8RealCarrierHardExternalHalt

    hardExternalHaltIsUniformBalabanOrAgawa :
      hardExternalHalt
      ≡
      uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    realCarrierTheoremConstructed :
      Bool

    realCarrierTheoremConstructedIsFalse :
      realCarrierTheoremConstructed ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    stagingBoundary :
      List String

open S8RealNonNatCarrierStagingReceipt public

canonicalS8RealNonNatCarrierStagingReceipt :
  S8RealNonNatCarrierStagingReceipt
canonicalS8RealNonNatCarrierStagingReceipt =
  record
    { realCarrier =
        s8RealPhysicalCarrier
    ; realCarrierIsS8RealPhysicalCarrier =
        refl
    ; realCarrierKind =
        realPhysicalCarrierEvidence
    ; realCarrierKindIsRealPhysical =
        refl
    ; boundedNatCarrierKind =
        boundedNatCarrierEvidence
    ; boundedNatCarrierKindIsBoundedNat =
        refl
    ; stagingFields =
        canonicalS8RealNonNatCarrierStagingFields
    ; stagingFieldsAreCanonical =
        refl
    ; requiredRealCarrierTheorem =
        selfAdjointYangMillsHamiltonianOnRealCarrierQuotientTarget
    ; requiredRealCarrierTheoremIsSelfAdjointHamiltonianOnRealCarrier =
        refl
    ; nonVacuumLowerBoundTarget =
        infSigmaHYMGreaterThanZeroOnNonVacuumCarrier
    ; nonVacuumLowerBoundTargetIsInfSigmaPositive =
        refl
    ; hardExternalHalt =
        uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; hardExternalHaltIsUniformBalabanOrAgawa =
        refl
    ; realCarrierTheoremConstructed =
        false
    ; realCarrierTheoremConstructedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; stagingBoundary =
        "The real/non-Nat carrier is staged as RealAnalysisAxioms.R, not as the bounded Nat witness slice"
        ∷ "The required theorem target is self-adjoint Yang-Mills Hamiltonian on the real carrier quotient"
        ∷ "The lower-bound target is inf sigma(H_YM)>0 on the non-vacuum real carrier"
        ∷ "The hard external halt remains UniformBalaban-or-AgawaIRFixedPoint"
        ∷ "No real-carrier theorem or terminal promotion is constructed by this staging receipt"
        ∷ []
    }

record S8SelfAdjointHamiltonianBlockerReceipt : Setω where
  field
    firstMissingTheorem :
      S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    firstMissingTheoremIsSelfAdjointYangMillsHamiltonian :
      firstMissingTheorem
      ≡
      missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    requiredTheoremTarget :
      S8RealCarrierRequiredTheoremTarget

    requiredTheoremTargetIsRealSelfAdjointHamiltonian :
      requiredTheoremTarget
      ≡
      selfAdjointYangMillsHamiltonianOnRealCarrierQuotientTarget

    blockerFields :
      List S8SelfAdjointHamiltonianBlockerField

    blockerFieldsAreCanonical :
      blockerFields
      ≡
      canonicalS8SelfAdjointHamiltonianBlockerFields

    firstBlockerField :
      S8SelfAdjointHamiltonianBlockerField

    firstBlockerFieldIsHamiltonianOperatorOnRealCarrier :
      firstBlockerField
      ≡
      missingHamiltonianOperatorOnRealCarrierQuotientField

    stoneCompatibilityBlocker :
      S8SelfAdjointHamiltonianBlockerField

    stoneCompatibilityBlockerIsCanonical :
      stoneCompatibilityBlocker
      ≡
      missingStoneEvolutionCompatibilityField

    externalHalt :
      S8RealCarrierHardExternalHalt

    externalHaltIsUniformBalabanOrAgawa :
      externalHalt
      ≡
      uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    blockerDischarged :
      Bool

    blockerDischargedIsFalse :
      blockerDischarged ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    blockerBoundary :
      List String

open S8SelfAdjointHamiltonianBlockerReceipt public

canonicalS8SelfAdjointHamiltonianBlockerReceipt :
  S8SelfAdjointHamiltonianBlockerReceipt
canonicalS8SelfAdjointHamiltonianBlockerReceipt =
  record
    { firstMissingTheorem =
        missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; firstMissingTheoremIsSelfAdjointYangMillsHamiltonian =
        refl
    ; requiredTheoremTarget =
        selfAdjointYangMillsHamiltonianOnRealCarrierQuotientTarget
    ; requiredTheoremTargetIsRealSelfAdjointHamiltonian =
        refl
    ; blockerFields =
        canonicalS8SelfAdjointHamiltonianBlockerFields
    ; blockerFieldsAreCanonical =
        refl
    ; firstBlockerField =
        missingHamiltonianOperatorOnRealCarrierQuotientField
    ; firstBlockerFieldIsHamiltonianOperatorOnRealCarrier =
        refl
    ; stoneCompatibilityBlocker =
        missingStoneEvolutionCompatibilityField
    ; stoneCompatibilityBlockerIsCanonical =
        refl
    ; externalHalt =
        uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; externalHaltIsUniformBalabanOrAgawa =
        refl
    ; blockerDischarged =
        false
    ; blockerDischargedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; blockerBoundary =
        "The self-adjoint/Hamiltonian blocker is recorded as an exact receipt, not discharged"
        ∷ "The first missing field is a Hamiltonian operator on the real carrier quotient with domain and self-adjointness data"
        ∷ "Stone evolution compatibility is a downstream blocker, not a promoted consequence"
        ∷ "UniformBalaban-or-AgawaIRFixedPoint is the hard halt for the real-carrier route"
        ∷ "No spectral-gap receipt or terminal promotion is constructed"
        ∷ []
    }

data S8RealYMCarrierQuotientImplementationBlocker : Set where
  missingRealYMConnectionCarrierField :
    S8RealYMCarrierQuotientImplementationBlocker

  missingGaugeEquivalenceRelationOnRealConnectionsField :
    S8RealYMCarrierQuotientImplementationBlocker

  missingRealCarrierQuotientNormField :
    S8RealYMCarrierQuotientImplementationBlocker

  missingConnectionLaplacianFromSFGCCurvatureField :
    S8RealYMCarrierQuotientImplementationBlocker

  missingPlaquettePotentialOperatorField :
    S8RealYMCarrierQuotientImplementationBlocker

  missingDenseSelfAdjointDomainForHYMField :
    S8RealYMCarrierQuotientImplementationBlocker

  missingFiniteCarrierGapTransportToRealHYMField :
    S8RealYMCarrierQuotientImplementationBlocker

canonicalS8RealYMCarrierQuotientImplementationBlockers :
  List S8RealYMCarrierQuotientImplementationBlocker
canonicalS8RealYMCarrierQuotientImplementationBlockers =
  missingRealYMConnectionCarrierField
  ∷ missingGaugeEquivalenceRelationOnRealConnectionsField
  ∷ missingRealCarrierQuotientNormField
  ∷ missingConnectionLaplacianFromSFGCCurvatureField
  ∷ missingPlaquettePotentialOperatorField
  ∷ missingDenseSelfAdjointDomainForHYMField
  ∷ missingFiniteCarrierGapTransportToRealHYMField
  ∷ []

data S8FiniteCarrierSpectralBoundUse : Set where
  finiteCarrierBoundAvailableOnlyAsLocalNonContinuumReceipt :
    S8FiniteCarrierSpectralBoundUse

record S8RealYMCarrierQuotientImplementationAudit : Setω where
  field
    requestedCarrierName :
      String

    requestedCarrierNameIsRealYMCarrierQuotient :
      requestedCarrierName
      ≡
      "RealYMCarrierQuotient"

    quotientBaseCarrier :
      Set

    quotientBaseCarrierIsS8RealPhysicalCarrier :
      quotientBaseCarrier
      ≡
      s8RealPhysicalCarrier

    requestedHamiltonianName :
      String

    requestedHamiltonianNameIsHYM :
      requestedHamiltonianName
      ≡
      "H_YM = -Delta_A + V_YM"

    blockerFields :
      List S8RealYMCarrierQuotientImplementationBlocker

    blockerFieldsAreCanonical :
      blockerFields
      ≡
      canonicalS8RealYMCarrierQuotientImplementationBlockers

    firstBlocker :
      S8RealYMCarrierQuotientImplementationBlocker

    firstBlockerIsRealYMConnectionCarrier :
      firstBlocker
      ≡
      missingRealYMConnectionCarrierField

    selfAdjointCarrierTheorem :
      S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    selfAdjointCarrierTheoremIsMissing :
      selfAdjointCarrierTheorem
      ≡
      missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    finiteCarrierSpectralBoundUse :
      S8FiniteCarrierSpectralBoundUse

    finiteCarrierSpectralBoundUseIsLocalOnly :
      finiteCarrierSpectralBoundUse
      ≡
      finiteCarrierBoundAvailableOnlyAsLocalNonContinuumReceipt

    exactCasimirOverBetaBoundAvailable :
      Bool

    exactCasimirOverBetaBoundAvailableIsFalse :
      exactCasimirOverBetaBoundAvailable ≡ false

    realHamiltonianConstructed :
      Bool

    realHamiltonianConstructedIsFalse :
      realHamiltonianConstructed ≡ false

    selfAdjointDomainConstructed :
      Bool

    selfAdjointDomainConstructedIsFalse :
      selfAdjointDomainConstructed ≡ false

    symmetryProofConstructed :
      Bool

    symmetryProofConstructedIsFalse :
      symmetryProofConstructed ≡ false

    finiteCarrierBoundTransportedToRealHYM :
      Bool

    finiteCarrierBoundTransportedToRealHYMIsFalse :
      finiteCarrierBoundTransportedToRealHYM ≡ false

    hardExternalHalt :
      S8RealCarrierHardExternalHalt

    hardExternalHaltIsUniformBalabanOrAgawa :
      hardExternalHalt
      ≡
      uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    continuumPromotion :
      Bool

    continuumPromotionIsFalse :
      continuumPromotion ≡ false

    auditEvidence :
      List String

open S8RealYMCarrierQuotientImplementationAudit public

canonicalS8RealYMCarrierQuotientImplementationAudit :
  S8RealYMCarrierQuotientImplementationAudit
canonicalS8RealYMCarrierQuotientImplementationAudit =
  record
    { requestedCarrierName =
        "RealYMCarrierQuotient"
    ; requestedCarrierNameIsRealYMCarrierQuotient =
        refl
    ; quotientBaseCarrier =
        s8RealPhysicalCarrier
    ; quotientBaseCarrierIsS8RealPhysicalCarrier =
        refl
    ; requestedHamiltonianName =
        "H_YM = -Delta_A + V_YM"
    ; requestedHamiltonianNameIsHYM =
        refl
    ; blockerFields =
        canonicalS8RealYMCarrierQuotientImplementationBlockers
    ; blockerFieldsAreCanonical =
        refl
    ; firstBlocker =
        missingRealYMConnectionCarrierField
    ; firstBlockerIsRealYMConnectionCarrier =
        refl
    ; selfAdjointCarrierTheorem =
        missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; selfAdjointCarrierTheoremIsMissing =
        refl
    ; finiteCarrierSpectralBoundUse =
        finiteCarrierBoundAvailableOnlyAsLocalNonContinuumReceipt
    ; finiteCarrierSpectralBoundUseIsLocalOnly =
        refl
    ; exactCasimirOverBetaBoundAvailable =
        false
    ; exactCasimirOverBetaBoundAvailableIsFalse =
        refl
    ; realHamiltonianConstructed =
        false
    ; realHamiltonianConstructedIsFalse =
        refl
    ; selfAdjointDomainConstructed =
        false
    ; selfAdjointDomainConstructedIsFalse =
        refl
    ; symmetryProofConstructed =
        false
    ; symmetryProofConstructedIsFalse =
        refl
    ; finiteCarrierBoundTransportedToRealHYM =
        false
    ; finiteCarrierBoundTransportedToRealHYMIsFalse =
        refl
    ; hardExternalHalt =
        uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; hardExternalHaltIsUniformBalabanOrAgawa =
        refl
    ; continuumPromotion =
        false
    ; continuumPromotionIsFalse =
        refl
    ; auditEvidence =
        "PressureBelow15SpectralTheoremObstruction.agda defines SelfAdjointYangMillsHamiltonianOnCarrierQuotient as the exact required theorem interface, but no RealYMCarrierQuotient inhabitant is available"
        ∷ "PressureBelow15SpectralNatWitnessSlice.agda supplies only the bounded Nat/FactorVec identity-Hamiltonian inhabitant; it is classified as boundedNatCarrierEvidence"
        ∷ "YangMillsFieldEquationObstruction.agda retains the strict non-flat connection carrier as a user-supplied request, not an implemented real YMConnectionCarrier"
        ∷ "BalabanRGMassGapReceiptSurface.agda records local finite-carrier spectral-gap receipts, but not an exact C2/(3 beta) theorem transported to the real H_YM operator"
        ∷ "The requested operator -Delta_A + V_YM still lacks connection-Laplacian, plaquette-potential, dense-domain, and self-adjointness inhabitants over the real quotient"
        ∷ "UniformBalaban-or-AgawaIRFixedPoint remains the hard halt for continuum/real-carrier promotion"
        ∷ []
    }

record L6RealCarrierQuotientFailClosedReceipt : Setω where
  field
    implementationAudit :
      S8RealYMCarrierQuotientImplementationAudit

    requestedConnectionCarrierName :
      String

    requestedConnectionCarrierNameIsYMConnectionCarrier :
      requestedConnectionCarrierName
      ≡
      "YMConnectionCarrier"

    requestedQuotientShapeName :
      String

    requestedQuotientShapeNameIsRealYMConnectionCarrierModuloGauge :
      requestedQuotientShapeName
      ≡
      "RealYMCarrierQuotient = YMConnectionCarrier / gauge-equivalence"

    firstImplementationBlocker :
      S8RealYMCarrierQuotientImplementationBlocker

    firstImplementationBlockerIsMissingYMConnectionCarrier :
      firstImplementationBlocker
      ≡
      missingRealYMConnectionCarrierField

    exactFunctionalAnalyticBlocker :
      S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    exactFunctionalAnalyticBlockerIsMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient :
      exactFunctionalAnalyticBlocker
      ≡
      missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    hardExternalHalt :
      S8RealCarrierHardExternalHalt

    hardExternalHaltIsUniformBalabanOrAgawa :
      hardExternalHalt
      ≡
      uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    hardExternalHaltName :
      String

    hardExternalHaltNameIsUniformBalabanOrAgawaIRFixedPoint :
      hardExternalHaltName
      ≡
      "UniformBalaban-or-AgawaIRFixedPoint"

    ymConnectionCarrierConstructed :
      Bool

    ymConnectionCarrierConstructedIsFalse :
      ymConnectionCarrierConstructed ≡ false

    realCarrierQuotientConstructed :
      Bool

    realCarrierQuotientConstructedIsFalse :
      realCarrierQuotientConstructed ≡ false

    selfAdjointYangMillsHamiltonianConstructed :
      Bool

    selfAdjointYangMillsHamiltonianConstructedIsFalse :
      selfAdjointYangMillsHamiltonianConstructed ≡ false

    continuumPromotion :
      Bool

    continuumPromotionIsFalse :
      continuumPromotion ≡ false

    l6FailClosedBoundary :
      List String

open L6RealCarrierQuotientFailClosedReceipt public

canonicalL6RealCarrierQuotientFailClosedReceipt :
  L6RealCarrierQuotientFailClosedReceipt
canonicalL6RealCarrierQuotientFailClosedReceipt =
  record
    { implementationAudit =
        canonicalS8RealYMCarrierQuotientImplementationAudit
    ; requestedConnectionCarrierName =
        "YMConnectionCarrier"
    ; requestedConnectionCarrierNameIsYMConnectionCarrier =
        refl
    ; requestedQuotientShapeName =
        "RealYMCarrierQuotient = YMConnectionCarrier / gauge-equivalence"
    ; requestedQuotientShapeNameIsRealYMConnectionCarrierModuloGauge =
        refl
    ; firstImplementationBlocker =
        missingRealYMConnectionCarrierField
    ; firstImplementationBlockerIsMissingYMConnectionCarrier =
        refl
    ; exactFunctionalAnalyticBlocker =
        missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; exactFunctionalAnalyticBlockerIsMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient =
        refl
    ; hardExternalHalt =
        uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; hardExternalHaltIsUniformBalabanOrAgawa =
        refl
    ; hardExternalHaltName =
        "UniformBalaban-or-AgawaIRFixedPoint"
    ; hardExternalHaltNameIsUniformBalabanOrAgawaIRFixedPoint =
        refl
    ; ymConnectionCarrierConstructed =
        false
    ; ymConnectionCarrierConstructedIsFalse =
        refl
    ; realCarrierQuotientConstructed =
        false
    ; realCarrierQuotientConstructedIsFalse =
        refl
    ; selfAdjointYangMillsHamiltonianConstructed =
        false
    ; selfAdjointYangMillsHamiltonianConstructedIsFalse =
        refl
    ; continuumPromotion =
        false
    ; continuumPromotionIsFalse =
        refl
    ; l6FailClosedBoundary =
        "l6 names the requested carrier quotient as YMConnectionCarrier modulo gauge equivalence"
        ∷ "The first implementation blocker is still the missing real YMConnectionCarrier field"
        ∷ "The exact functional-analytic blocker is missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient"
        ∷ "The hard external halt is UniformBalaban-or-AgawaIRFixedPoint"
        ∷ "No self-adjoint real Yang-Mills Hamiltonian, continuum theorem, Clay token, or terminal promotion is fabricated"
        ∷ []
    }

record YMConnectionCarrier : Set₁ where
  field
    Site :
      Set

    Edge :
      Set

    Plaquette :
      Set

    GaugePhase :
      Set

    GaugeTransform :
      Set

    LieCarrier :
      Set

    Connection :
      Set

    edgeSource :
      Edge →
      Site

    edgeTarget :
      Edge →
      Site

    plaquetteBottomEdge :
      Plaquette →
      Edge

    plaquetteRightEdge :
      Plaquette →
      Edge

    plaquetteTopEdge :
      Plaquette →
      Edge

    plaquetteLeftEdge :
      Plaquette →
      Edge

    gaugeAction :
      GaugeTransform →
      Connection →
      Connection

    Curvature :
      Set

    connectionCurvature :
      Connection →
      Curvature

    FieldStrength :
      Set

    curvatureToFieldStrength :
      Curvature →
      FieldStrength

    finiteOnly :
      Bool

    finiteOnlyIsTrue :
      finiteOnly ≡ true

    strictRealYMConnectionConstructed :
      Bool

    strictRealYMConnectionConstructedIsFalse :
      strictRealYMConnectionConstructed ≡ false

    carrierBoundary :
      List String

open YMConnectionCarrier public

canonicalFiniteSFGCSite2DYMConnectionCarrier :
  YMConnectionCarrier
canonicalFiniteSFGCSite2DYMConnectionCarrier =
  record
    { Site =
        SFGC.SFGCSite2D
    ; Edge =
        SFGC.SFGCSite2DEdge
    ; Plaquette =
        SFGC.SFGCSite2DPlaquette
    ; GaugePhase =
        SPTI4.Phase4
    ; GaugeTransform =
        SFGS.GaugeTransform
    ; LieCarrier =
        YM.YMSFGCLocalFiniteLie3Carrier
    ; Connection =
        SFGC.SFGCSite2DDiscrete1Form
    ; edgeSource =
        SFGC.sfgcSite2DEdgeSourceTotal
    ; edgeTarget =
        SFGC.sfgcSite2DEdgeTargetTotal
    ; plaquetteBottomEdge =
        SFGC.sfgcSite2DPlaquetteBottomEdge
    ; plaquetteRightEdge =
        SFGC.sfgcSite2DPlaquetteRightEdge
    ; plaquetteTopEdge =
        SFGC.sfgcSite2DPlaquetteTopEdge
    ; plaquetteLeftEdge =
        SFGC.sfgcSite2DPlaquetteLeftEdge
    ; gaugeAction =
        YM.sfgcFiniteC4ConnectionGaugeTransformCandidate
    ; Curvature =
        SFGC.SFGCSite2DDiscrete2Form
    ; connectionCurvature =
        SFGC.sfgcSite2Dδ₁
    ; FieldStrength =
        SFGC.SFGCSite2DFieldStrengthBridge
    ; curvatureToFieldStrength =
        SFGC.sfgcSite2DFieldStrengthFromCurvature
    ; finiteOnly =
        true
    ; finiteOnlyIsTrue =
        refl
    ; strictRealYMConnectionConstructed =
        false
    ; strictRealYMConnectionConstructedIsFalse =
        refl
    ; carrierBoundary =
        "Inhabited finite lower shape: SFGCSite2D sites, directed p2/p3 edges, plaquettes, Phase4 gauge phases, local finite Lie3, and SFGCSite2DDiscrete1Form connections"
        ∷ "Gauge action is the finite C4 connection-transform candidate from YangMillsFieldEquationObstruction"
        ∷ "Curvature is SFGC.sfgcSite2Ddelta1 and field strength is SFGC.sfgcSite2DFieldStrengthFromCurvature"
        ∷ "This is finite SFGC carrier data only; it is not a strict real YMConnectionCarrier"
        ∷ []
    }

data S8RealYMCarrierQuotientShapeMissingAPI : Set where
  missingContinuousGaugeTransformCarrierAPI :
    S8RealYMCarrierQuotientShapeMissingAPI

  missingRealConnectionCarrierFromFiniteSFGCSite2DAPI :
    S8RealYMCarrierQuotientShapeMissingAPI

  missingGaugeOrbitEquivalenceRelationOnRealConnectionsAPI :
    S8RealYMCarrierQuotientShapeMissingAPI

  missingGaugeInvariantRealQuotientNormAPI :
    S8RealYMCarrierQuotientShapeMissingAPI

  missingRealYangMillsActionFunctionalAPI :
    S8RealYMCarrierQuotientShapeMissingAPI

  missingRealDenseHamiltonianDomainAPI :
    S8RealYMCarrierQuotientShapeMissingAPI

  missingRealHamiltonianSymmetryOnDomainAPI :
    S8RealYMCarrierQuotientShapeMissingAPI

  missingSelfAdjointExtensionOrEssentialSelfAdjointnessAPI :
    S8RealYMCarrierQuotientShapeMissingAPI

canonicalS8RealYMCarrierQuotientShapeMissingAPIs :
  List S8RealYMCarrierQuotientShapeMissingAPI
canonicalS8RealYMCarrierQuotientShapeMissingAPIs =
  missingContinuousGaugeTransformCarrierAPI
  ∷ missingRealConnectionCarrierFromFiniteSFGCSite2DAPI
  ∷ missingGaugeOrbitEquivalenceRelationOnRealConnectionsAPI
  ∷ missingGaugeInvariantRealQuotientNormAPI
  ∷ missingRealYangMillsActionFunctionalAPI
  ∷ missingRealDenseHamiltonianDomainAPI
  ∷ missingRealHamiltonianSymmetryOnDomainAPI
  ∷ missingSelfAdjointExtensionOrEssentialSelfAdjointnessAPI
  ∷ []

record RealYMCarrierQuotient : Setω where
  field
    finiteConnectionCarrier :
      YMConnectionCarrier

    finiteSFGCSite2DSchema :
      G2SFGCS.DirectionIndexedSFGCGaugeFieldSchema SFGC.GaugeField

    finiteStrictPromotionDecision :
      YM.YMSFGCGate3Wave3StrictPromotionDecisionReceipt

    realCarrier :
      Set

    realCarrierIsRealAnalysisℝ :
      realCarrier
      ≡
      s8RealPhysicalCarrier

    gaugeActionTarget :
      Set

    gaugeActionTargetIsFiniteGaugeActionOnRealCarrierType :
      gaugeActionTarget
      ≡
      (SFGS.GaugeTransform → realCarrier → realCarrier)

    gaugeOrbitRelationTarget :
      Set₁

    gaugeOrbitRelationTargetIsBinaryRelationOnRealCarrier :
      gaugeOrbitRelationTarget
      ≡
      (realCarrier → realCarrier → Set)

    quotientNormTarget :
      Set

    quotientNormTargetIsRealNormOnQuotientCarrier :
      quotientNormTarget
      ≡
      (realCarrier → RA.ℝ)

    quotientConstructed :
      Bool

    quotientConstructedIsFalse :
      quotientConstructed ≡ false

    realGaugeActionConstructed :
      Bool

    realGaugeActionConstructedIsFalse :
      realGaugeActionConstructed ≡ false

    quotientNormConstructed :
      Bool

    quotientNormConstructedIsFalse :
      quotientNormConstructed ≡ false

    missingAPIs :
      List S8RealYMCarrierQuotientShapeMissingAPI

    missingAPIsAreCanonical :
      missingAPIs
      ≡
      canonicalS8RealYMCarrierQuotientShapeMissingAPIs

    firstMissingAPI :
      S8RealYMCarrierQuotientShapeMissingAPI

    firstMissingAPIIsContinuousGaugeTransformCarrier :
      firstMissingAPI
      ≡
      missingContinuousGaugeTransformCarrierAPI

    quotientBoundary :
      List String

open RealYMCarrierQuotient public

canonicalRealYMCarrierQuotient :
  RealYMCarrierQuotient
canonicalRealYMCarrierQuotient =
  record
    { finiteConnectionCarrier =
        canonicalFiniteSFGCSite2DYMConnectionCarrier
    ; finiteSFGCSite2DSchema =
        G2SFGCS.canonicalSFGCSite2DGaugeFieldSchema
    ; finiteStrictPromotionDecision =
        YM.canonicalYMSFGCGate3Wave3StrictPromotionDecisionReceipt
    ; realCarrier =
        s8RealPhysicalCarrier
    ; realCarrierIsRealAnalysisℝ =
        refl
    ; gaugeActionTarget =
        SFGS.GaugeTransform →
        s8RealPhysicalCarrier →
        s8RealPhysicalCarrier
    ; gaugeActionTargetIsFiniteGaugeActionOnRealCarrierType =
        refl
    ; gaugeOrbitRelationTarget =
        s8RealPhysicalCarrier →
        s8RealPhysicalCarrier →
        Set
    ; gaugeOrbitRelationTargetIsBinaryRelationOnRealCarrier =
        refl
    ; quotientNormTarget =
        s8RealPhysicalCarrier →
        RA.ℝ
    ; quotientNormTargetIsRealNormOnQuotientCarrier =
        refl
    ; quotientConstructed =
        false
    ; quotientConstructedIsFalse =
        refl
    ; realGaugeActionConstructed =
        false
    ; realGaugeActionConstructedIsFalse =
        refl
    ; quotientNormConstructed =
        false
    ; quotientNormConstructedIsFalse =
        refl
    ; missingAPIs =
        canonicalS8RealYMCarrierQuotientShapeMissingAPIs
    ; missingAPIsAreCanonical =
        refl
    ; firstMissingAPI =
        missingContinuousGaugeTransformCarrierAPI
    ; firstMissingAPIIsContinuousGaugeTransformCarrier =
        refl
    ; quotientBoundary =
        "Finite carrier shape is now inhabited from SFGCSite2D/Phase4/local-Lie3 surfaces"
        ∷ "The real quotient is only a target shape over RealAnalysisAxioms.R"
        ∷ "The available SFGS.GaugeTransform is a finite Phase4 transform on ShiftPressurePoint, not a continuous real gauge group"
        ∷ "No gauge-orbit equivalence relation or gauge-invariant quotient norm is constructed"
        ∷ "The YangMillsFieldEquationObstruction strict-promotion decision remains false"
        ∷ []
    }

record SelfAdjointYangMillsHamiltonianOnCarrierQuotientCarrierShape : Setω where
  field
    carrierQuotient :
      RealYMCarrierQuotient

    hilbertSpaceTarget :
      Set₁

    hilbertSpaceTargetIsUnifierHilbertSpace :
      hilbertSpaceTarget
      ≡
      U.HilbertSpace

    domainPredicateTarget :
      Set₁

    domainPredicateTargetIsPredicateOnRealCarrier :
      domainPredicateTarget
      ≡
      (RealYMCarrierQuotient.realCarrier carrierQuotient → Set)

    hamiltonianActionTarget :
      Set

    hamiltonianActionTargetIsEndomapOnRealCarrier :
      hamiltonianActionTarget
      ≡
      (RealYMCarrierQuotient.realCarrier carrierQuotient →
       RealYMCarrierQuotient.realCarrier carrierQuotient)

    symmetryOnDomainTarget :
      Set₁

    symmetryOnDomainTargetIsBinaryPredicateOnRealCarrier :
      symmetryOnDomainTarget
      ≡
      ((left right : RealYMCarrierQuotient.realCarrier carrierQuotient) → Set)

    selfAdjointnessTarget :
      S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    selfAdjointnessTargetIsCanonical :
      selfAdjointnessTarget
      ≡
      missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    domainConstructed :
      Bool

    domainConstructedIsFalse :
      domainConstructed ≡ false

    hamiltonianActionConstructed :
      Bool

    hamiltonianActionConstructedIsFalse :
      hamiltonianActionConstructed ≡ false

    symmetryConstructed :
      Bool

    symmetryConstructedIsFalse :
      symmetryConstructed ≡ false

    selfAdjointHamiltonianConstructed :
      Bool

    selfAdjointHamiltonianConstructedIsFalse :
      selfAdjointHamiltonianConstructed ≡ false

    carrierShapeBoundary :
      List String

open SelfAdjointYangMillsHamiltonianOnCarrierQuotientCarrierShape public

canonicalSelfAdjointYangMillsHamiltonianOnCarrierQuotientCarrierShape :
  SelfAdjointYangMillsHamiltonianOnCarrierQuotientCarrierShape
canonicalSelfAdjointYangMillsHamiltonianOnCarrierQuotientCarrierShape =
  record
    { carrierQuotient =
        canonicalRealYMCarrierQuotient
    ; hilbertSpaceTarget =
        U.HilbertSpace
    ; hilbertSpaceTargetIsUnifierHilbertSpace =
        refl
    ; domainPredicateTarget =
        s8RealPhysicalCarrier → Set
    ; domainPredicateTargetIsPredicateOnRealCarrier =
        refl
    ; hamiltonianActionTarget =
        s8RealPhysicalCarrier → s8RealPhysicalCarrier
    ; hamiltonianActionTargetIsEndomapOnRealCarrier =
        refl
    ; symmetryOnDomainTarget =
        (left right : s8RealPhysicalCarrier) → Set
    ; symmetryOnDomainTargetIsBinaryPredicateOnRealCarrier =
        refl
    ; selfAdjointnessTarget =
        missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; selfAdjointnessTargetIsCanonical =
        refl
    ; domainConstructed =
        false
    ; domainConstructedIsFalse =
        refl
    ; hamiltonianActionConstructed =
        false
    ; hamiltonianActionConstructedIsFalse =
        refl
    ; symmetryConstructed =
        false
    ; symmetryConstructedIsFalse =
        refl
    ; selfAdjointHamiltonianConstructed =
        false
    ; selfAdjointHamiltonianConstructedIsFalse =
        refl
    ; carrierShapeBoundary =
        "The carrier quotient target now names Hilbert-space, domain, Hamiltonian-action, and symmetry target types"
        ∷ "No dense domain, real Hamiltonian action, symmetry proof, or self-adjoint extension is inhabited"
        ∷ "This shape does not inhabit SelfAdjointYangMillsHamiltonianOnCarrierQuotient for a real PressureToSpectralGapHypothesisPackage"
        ∷ []
    }

record S8RealYMCarrierQuotientShapeAuditReceipt : Setω where
  field
    finiteYMConnectionCarrier :
      YMConnectionCarrier

    finiteYMConnectionCarrierIsCanonical :
      finiteYMConnectionCarrier
      ≡
      canonicalFiniteSFGCSite2DYMConnectionCarrier

    realYMCarrierQuotientShape :
      RealYMCarrierQuotient

    realYMCarrierQuotientShapeIsCanonical :
      Bool

    realYMCarrierQuotientShapeIsCanonical-v :
      realYMCarrierQuotientShapeIsCanonical ≡ true

    hamiltonianCarrierShape :
      SelfAdjointYangMillsHamiltonianOnCarrierQuotientCarrierShape

    hamiltonianCarrierShapeIsCanonical :
      Bool

    hamiltonianCarrierShapeIsCanonical-v :
      hamiltonianCarrierShapeIsCanonical ≡ true

    missingAPIs :
      List S8RealYMCarrierQuotientShapeMissingAPI

    missingAPIsAreCanonical :
      missingAPIs
      ≡
      canonicalS8RealYMCarrierQuotientShapeMissingAPIs

    finiteCarrierShapeInhabited :
      Bool

    finiteCarrierShapeInhabitedIsTrue :
      finiteCarrierShapeInhabited ≡ true

    realCarrierQuotientConstructed :
      Bool

    realCarrierQuotientConstructedIsFalse :
      realCarrierQuotientConstructed ≡ false

    selfAdjointYangMillsHamiltonianConstructed :
      Bool

    selfAdjointYangMillsHamiltonianConstructedIsFalse :
      selfAdjointYangMillsHamiltonianConstructed ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    auditBoundary :
      List String

open S8RealYMCarrierQuotientShapeAuditReceipt public

canonicalS8RealYMCarrierQuotientShapeAuditReceipt :
  S8RealYMCarrierQuotientShapeAuditReceipt
canonicalS8RealYMCarrierQuotientShapeAuditReceipt =
  record
    { finiteYMConnectionCarrier =
        canonicalFiniteSFGCSite2DYMConnectionCarrier
    ; finiteYMConnectionCarrierIsCanonical =
        refl
    ; realYMCarrierQuotientShape =
        canonicalRealYMCarrierQuotient
    ; realYMCarrierQuotientShapeIsCanonical =
        true
    ; realYMCarrierQuotientShapeIsCanonical-v =
        refl
    ; hamiltonianCarrierShape =
        canonicalSelfAdjointYangMillsHamiltonianOnCarrierQuotientCarrierShape
    ; hamiltonianCarrierShapeIsCanonical =
        true
    ; hamiltonianCarrierShapeIsCanonical-v =
        refl
    ; missingAPIs =
        canonicalS8RealYMCarrierQuotientShapeMissingAPIs
    ; missingAPIsAreCanonical =
        refl
    ; finiteCarrierShapeInhabited =
        true
    ; finiteCarrierShapeInhabitedIsTrue =
        refl
    ; realCarrierQuotientConstructed =
        false
    ; realCarrierQuotientConstructedIsFalse =
        refl
    ; selfAdjointYangMillsHamiltonianConstructed =
        false
    ; selfAdjointYangMillsHamiltonianConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; auditBoundary =
        "First-missing primitive attempt result: finite SFGCSite2D YMConnectionCarrier shape is inhabited"
        ∷ "RealYMCarrierQuotient remains a target shape, not a constructed quotient"
        ∷ "Exact missing APIs: continuous gauge transform carrier, real connection carrier bridge from finite SFGCSite2D, gauge orbit equivalence relation, gauge-invariant quotient norm, real YM action functional, dense Hamiltonian domain, Hamiltonian symmetry on domain, and self-adjoint extension or essential self-adjointness"
        ∷ "All real quotient, self-adjoint Hamiltonian, spectral-gap, and terminal promotion flags remain false"
        ∷ []
    }

record YMGaugeOrbitRelationShape
  (carrier : YMConnectionCarrier)
  : Setω where
  field
    baseConn :
      YMConnectionCarrier.Connection carrier

    finiteGaugeTransform :
      YMConnectionCarrier.GaugeTransform carrier

    conjugatedConnection :
      YMConnectionCarrier.Connection carrier

    conjugatedConnectionIsGaugeAction :
      conjugatedConnection
      ≡
      YMConnectionCarrier.gaugeAction carrier finiteGaugeTransform baseConn

    orbitRelationTarget :
      Set₁

    orbitRelationTargetIsBinaryRelationOnConnections :
      orbitRelationTarget
      ≡
      (YMConnectionCarrier.Connection carrier →
       YMConnectionCarrier.Connection carrier →
       Set)

    typedFiniteActionWitnessTarget :
      Set

    typedFiniteActionWitnessTargetIsConjugationEquality :
      typedFiniteActionWitnessTarget
      ≡
      (conjugatedConnection
       ≡
       YMConnectionCarrier.gaugeAction carrier finiteGaugeTransform baseConn)

    finiteGaugeActionWitnessConstructed :
      Bool

    finiteGaugeActionWitnessConstructedIsTrue :
      finiteGaugeActionWitnessConstructed ≡ true

    realGaugeOrbitEquivalenceConstructed :
      Bool

    realGaugeOrbitEquivalenceConstructedIsFalse :
      realGaugeOrbitEquivalenceConstructed ≡ false

    orbitBoundary :
      List String

open YMGaugeOrbitRelationShape public

canonicalFiniteSFGCSite2DYMGaugeOrbitRelationShape :
  YMGaugeOrbitRelationShape canonicalFiniteSFGCSite2DYMConnectionCarrier
canonicalFiniteSFGCSite2DYMGaugeOrbitRelationShape =
  record
    { baseConn =
        SFGC.sfgcSite2DConnectionTo1Form SFGC.vacuumGaugeField
    ; finiteGaugeTransform =
        SFGS.constantGaugeTransform SPTI4.φ0
    ; conjugatedConnection =
        YMConnectionCarrier.gaugeAction
          canonicalFiniteSFGCSite2DYMConnectionCarrier
          (SFGS.constantGaugeTransform SPTI4.φ0)
          (SFGC.sfgcSite2DConnectionTo1Form SFGC.vacuumGaugeField)
    ; conjugatedConnectionIsGaugeAction =
        refl
    ; orbitRelationTarget =
        SFGC.SFGCSite2DDiscrete1Form →
        SFGC.SFGCSite2DDiscrete1Form →
        Set
    ; orbitRelationTargetIsBinaryRelationOnConnections =
        refl
    ; typedFiniteActionWitnessTarget =
        YMConnectionCarrier.gaugeAction
          canonicalFiniteSFGCSite2DYMConnectionCarrier
          (SFGS.constantGaugeTransform SPTI4.φ0)
          (SFGC.sfgcSite2DConnectionTo1Form SFGC.vacuumGaugeField)
        ≡
        YMConnectionCarrier.gaugeAction
          canonicalFiniteSFGCSite2DYMConnectionCarrier
          (SFGS.constantGaugeTransform SPTI4.φ0)
          (SFGC.sfgcSite2DConnectionTo1Form SFGC.vacuumGaugeField)
    ; typedFiniteActionWitnessTargetIsConjugationEquality =
        refl
    ; finiteGaugeActionWitnessConstructed =
        true
    ; finiteGaugeActionWitnessConstructedIsTrue =
        refl
    ; realGaugeOrbitEquivalenceConstructed =
        false
    ; realGaugeOrbitEquivalenceConstructedIsFalse =
        refl
    ; orbitBoundary =
        "upper6-u1 finite orbit shape: base connection is the SFGCSite2D vacuum 1-form"
        ∷ "The action witness is typed against YMConnectionCarrier.gaugeAction and the finite constant Phase4 gauge transform"
        ∷ "This only stages a binary relation target on finite SFGCSite2DDiscrete1Form connections"
        ∷ "No continuous real gauge-orbit equivalence relation is constructed"
        ∷ []
    }

record YMQuotientCarrierShape
  (carrier : YMConnectionCarrier)
  : Setω where
  field
    representative :
      YMConnectionCarrier.Connection carrier

    orbitMembership :
      YMGaugeOrbitRelationShape carrier

    orbitMembershipIsCanonicalFiniteShape :
      Bool

    orbitMembershipIsCanonicalFiniteShape-v :
      orbitMembershipIsCanonicalFiniteShape ≡ true

    quotientCarrierTarget :
      Set₁

    quotientCarrierTargetIsOrbitPredicateShape :
      quotientCarrierTarget
      ≡
      (YMConnectionCarrier.Connection carrier → Set)

    normEvidenceTarget :
      Set

    normEvidenceTargetIsRealNormOnRepresentatives :
      normEvidenceTarget
      ≡
      (YMConnectionCarrier.Connection carrier → RA.ℝ)

    quotientCarrierConstructed :
      Bool

    quotientCarrierConstructedIsFalse :
      quotientCarrierConstructed ≡ false

    gaugeInvariantNormConstructed :
      Bool

    gaugeInvariantNormConstructedIsFalse :
      gaugeInvariantNormConstructed ≡ false

    quotientBoundary :
      List String

open YMQuotientCarrierShape public

canonicalFiniteSFGCSite2DYMQuotientCarrierShape :
  YMQuotientCarrierShape canonicalFiniteSFGCSite2DYMConnectionCarrier
canonicalFiniteSFGCSite2DYMQuotientCarrierShape =
  record
    { representative =
        SFGC.sfgcSite2DConnectionTo1Form SFGC.vacuumGaugeField
    ; orbitMembership =
        canonicalFiniteSFGCSite2DYMGaugeOrbitRelationShape
    ; orbitMembershipIsCanonicalFiniteShape =
        true
    ; orbitMembershipIsCanonicalFiniteShape-v =
        refl
    ; quotientCarrierTarget =
        SFGC.SFGCSite2DDiscrete1Form → Set
    ; quotientCarrierTargetIsOrbitPredicateShape =
        refl
    ; normEvidenceTarget =
        SFGC.SFGCSite2DDiscrete1Form → RA.ℝ
    ; normEvidenceTargetIsRealNormOnRepresentatives =
        refl
    ; quotientCarrierConstructed =
        false
    ; quotientCarrierConstructedIsFalse =
        refl
    ; gaugeInvariantNormConstructed =
        false
    ; gaugeInvariantNormConstructedIsFalse =
        refl
    ; quotientBoundary =
        "upper6-u1 quotient shape records a representative and orbit-membership witness over the finite carrier"
        ∷ "The carrier target is an orbit predicate shape, not a quotient type with setoid laws"
        ∷ "The norm field is only a target type for real-valued representative norms"
        ∷ "No gauge-invariant quotient norm or real quotient carrier is constructed"
        ∷ []
    }

record YMHamiltonianShape
  (carrier : YMConnectionCarrier)
  (quotient : YMQuotientCarrierShape carrier)
  : Setω where
  field
    quotientCarrier :
      YMQuotientCarrierShape carrier

    quotientCarrierIsCanonicalFiniteShape :
      Bool

    quotientCarrierIsCanonicalFiniteShape-v :
      quotientCarrierIsCanonicalFiniteShape ≡ true

    finiteLaplacianPlaceholderTarget :
      Set

    finiteLaplacianPlaceholderTargetIsConnectionEndomap :
      finiteLaplacianPlaceholderTarget
      ≡
      (YMConnectionCarrier.Connection carrier →
       YMConnectionCarrier.Connection carrier)

    potentialPlaceholderTarget :
      Set

    potentialPlaceholderTargetIsRealPotentialOnConnections :
      potentialPlaceholderTarget
      ≡
      (YMConnectionCarrier.Connection carrier → RA.ℝ)

    actionPlaceholderTarget :
      Set

    actionPlaceholderTargetIsRealActionOnConnections :
      actionPlaceholderTarget
      ≡
      (YMConnectionCarrier.Connection carrier → RA.ℝ)

    definitionalHamiltonianTarget :
      Set₁

    definitionalHamiltonianTargetIsLaplacianPotentialActionPackage :
      definitionalHamiltonianTarget
      ≡
      (finiteLaplacianPlaceholderTarget →
       potentialPlaceholderTarget →
       actionPlaceholderTarget →
       Set)

    finiteLaplacianConstructed :
      Bool

    finiteLaplacianConstructedIsFalse :
      finiteLaplacianConstructed ≡ false

    potentialConstructed :
      Bool

    potentialConstructedIsFalse :
      potentialConstructed ≡ false

    yangMillsActionConstructed :
      Bool

    yangMillsActionConstructedIsFalse :
      yangMillsActionConstructed ≡ false

    selfAdjointHamiltonianConstructed :
      Bool

    selfAdjointHamiltonianConstructedIsFalse :
      selfAdjointHamiltonianConstructed ≡ false

    hamiltonianBoundary :
      List String

open YMHamiltonianShape public

canonicalFiniteSFGCSite2DYMHamiltonianShape :
  YMHamiltonianShape
    canonicalFiniteSFGCSite2DYMConnectionCarrier
    canonicalFiniteSFGCSite2DYMQuotientCarrierShape
canonicalFiniteSFGCSite2DYMHamiltonianShape =
  record
    { quotientCarrier =
        canonicalFiniteSFGCSite2DYMQuotientCarrierShape
    ; quotientCarrierIsCanonicalFiniteShape =
        true
    ; quotientCarrierIsCanonicalFiniteShape-v =
        refl
    ; finiteLaplacianPlaceholderTarget =
        SFGC.SFGCSite2DDiscrete1Form →
        SFGC.SFGCSite2DDiscrete1Form
    ; finiteLaplacianPlaceholderTargetIsConnectionEndomap =
        refl
    ; potentialPlaceholderTarget =
        SFGC.SFGCSite2DDiscrete1Form → RA.ℝ
    ; potentialPlaceholderTargetIsRealPotentialOnConnections =
        refl
    ; actionPlaceholderTarget =
        SFGC.SFGCSite2DDiscrete1Form → RA.ℝ
    ; actionPlaceholderTargetIsRealActionOnConnections =
        refl
    ; definitionalHamiltonianTarget =
        (SFGC.SFGCSite2DDiscrete1Form →
         SFGC.SFGCSite2DDiscrete1Form) →
        (SFGC.SFGCSite2DDiscrete1Form → RA.ℝ) →
        (SFGC.SFGCSite2DDiscrete1Form → RA.ℝ) →
        Set
    ; definitionalHamiltonianTargetIsLaplacianPotentialActionPackage =
        refl
    ; finiteLaplacianConstructed =
        false
    ; finiteLaplacianConstructedIsFalse =
        refl
    ; potentialConstructed =
        false
    ; potentialConstructedIsFalse =
        refl
    ; yangMillsActionConstructed =
        false
    ; yangMillsActionConstructedIsFalse =
        refl
    ; selfAdjointHamiltonianConstructed =
        false
    ; selfAdjointHamiltonianConstructedIsFalse =
        refl
    ; hamiltonianBoundary =
        "upper6-u1 Hamiltonian shape connects the finite quotient shape to laplacian, potential, and action target types"
        ∷ "The definitional Hamiltonian field is only a package target over those placeholders"
        ∷ "No finite Laplacian, Yang-Mills action functional, dense domain, or self-adjoint Hamiltonian is constructed"
        ∷ "UniformBalaban-or-AgawaIRFixedPoint remains the hard external blocker for real promotion"
        ∷ []
    }

record S8Upper6RealYMQuotientCarrierHamiltonianShapeAuditReceipt : Setω where
  field
    finiteYMConnectionCarrier :
      YMConnectionCarrier

    finiteYMConnectionCarrierIsCanonical :
      finiteYMConnectionCarrier
      ≡
      canonicalFiniteSFGCSite2DYMConnectionCarrier

    gaugeOrbitShape :
      YMGaugeOrbitRelationShape finiteYMConnectionCarrier

    gaugeOrbitShapeIsCanonicalFinite :
      Bool

    gaugeOrbitShapeIsCanonicalFinite-v :
      gaugeOrbitShapeIsCanonicalFinite ≡ true

    quotientCarrierShape :
      YMQuotientCarrierShape finiteYMConnectionCarrier

    quotientCarrierShapeIsCanonicalFinite :
      Bool

    quotientCarrierShapeIsCanonicalFinite-v :
      quotientCarrierShapeIsCanonicalFinite ≡ true

    hamiltonianShape :
      YMHamiltonianShape finiteYMConnectionCarrier quotientCarrierShape

    hamiltonianShapeIsCanonicalFinite :
      Bool

    hamiltonianShapeIsCanonicalFinite-v :
      hamiltonianShapeIsCanonicalFinite ≡ true

    hardExternalHalt :
      S8RealCarrierHardExternalHalt

    hardExternalHaltIsUniformBalabanOrAgawa :
      hardExternalHalt
      ≡
      uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    realQuotientConstructed :
      Bool

    realQuotientConstructedIsFalse :
      realQuotientConstructed ≡ false

    realHamiltonianConstructed :
      Bool

    realHamiltonianConstructedIsFalse :
      realHamiltonianConstructed ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    auditBoundary :
      List String

open S8Upper6RealYMQuotientCarrierHamiltonianShapeAuditReceipt public

canonicalS8Upper6RealYMQuotientCarrierHamiltonianShapeAuditReceipt :
  S8Upper6RealYMQuotientCarrierHamiltonianShapeAuditReceipt
canonicalS8Upper6RealYMQuotientCarrierHamiltonianShapeAuditReceipt =
  record
    { finiteYMConnectionCarrier =
        canonicalFiniteSFGCSite2DYMConnectionCarrier
    ; finiteYMConnectionCarrierIsCanonical =
        refl
    ; gaugeOrbitShape =
        canonicalFiniteSFGCSite2DYMGaugeOrbitRelationShape
    ; gaugeOrbitShapeIsCanonicalFinite =
        true
    ; gaugeOrbitShapeIsCanonicalFinite-v =
        refl
    ; quotientCarrierShape =
        canonicalFiniteSFGCSite2DYMQuotientCarrierShape
    ; quotientCarrierShapeIsCanonicalFinite =
        true
    ; quotientCarrierShapeIsCanonicalFinite-v =
        refl
    ; hamiltonianShape =
        canonicalFiniteSFGCSite2DYMHamiltonianShape
    ; hamiltonianShapeIsCanonicalFinite =
        true
    ; hamiltonianShapeIsCanonicalFinite-v =
        refl
    ; hardExternalHalt =
        uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; hardExternalHaltIsUniformBalabanOrAgawa =
        refl
    ; realQuotientConstructed =
        false
    ; realQuotientConstructedIsFalse =
        refl
    ; realHamiltonianConstructed =
        false
    ; realHamiltonianConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; auditBoundary =
        "upper6-u1 adds finite gauge-orbit, quotient-carrier, and Hamiltonian-shape audit records over YMConnectionCarrier"
        ∷ "Canonical equality over dependent Setω records is avoided by Bool audit flags"
        ∷ "The construction is fail-closed: real quotient, real Hamiltonian, spectral gap, and terminal promotion remain false"
        ∷ "UniformBalaban-or-AgawaIRFixedPoint remains the blocker before any real self-adjoint Yang-Mills Hamiltonian claim"
        ∷ []
    }

data S8GlobalYangMillsHamiltonianCarrierTheoremField : Set where
  s8CarrierQuotientStateField :
    S8GlobalYangMillsHamiltonianCarrierTheoremField

  s8SelfAdjointHamiltonianOnCarrierQuotientField :
    S8GlobalYangMillsHamiltonianCarrierTheoremField

  s8VacuumSectorField :
    S8GlobalYangMillsHamiltonianCarrierTheoremField

  s8NonVacuumSectorPredicateField :
    S8GlobalYangMillsHamiltonianCarrierTheoremField

  s8VacuumOrthogonalityPredicateField :
    S8GlobalYangMillsHamiltonianCarrierTheoremField

  s8EnergyOrderAndPositiveGapUnitField :
    S8GlobalYangMillsHamiltonianCarrierTheoremField

  s8SubThresholdLowerBoundTransportField :
    S8GlobalYangMillsHamiltonianCarrierTheoremField

  s8PressureEnergyCoercivityWitnessField :
    S8GlobalYangMillsHamiltonianCarrierTheoremField

  s8CarrierUnitNormalizationField :
    S8GlobalYangMillsHamiltonianCarrierTheoremField

canonicalS8GlobalYangMillsHamiltonianCarrierTheoremFields :
  List S8GlobalYangMillsHamiltonianCarrierTheoremField
canonicalS8GlobalYangMillsHamiltonianCarrierTheoremFields =
  s8CarrierQuotientStateField
  ∷ s8SelfAdjointHamiltonianOnCarrierQuotientField
  ∷ s8VacuumSectorField
  ∷ s8NonVacuumSectorPredicateField
  ∷ s8VacuumOrthogonalityPredicateField
  ∷ s8EnergyOrderAndPositiveGapUnitField
  ∷ s8SubThresholdLowerBoundTransportField
  ∷ s8PressureEnergyCoercivityWitnessField
  ∷ s8CarrierUnitNormalizationField
  ∷ []

canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterSelfAdjoint :
  List S8GlobalYangMillsHamiltonianCarrierTheoremField
canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterSelfAdjoint =
  s8VacuumSectorField
  ∷ s8NonVacuumSectorPredicateField
  ∷ s8VacuumOrthogonalityPredicateField
  ∷ s8EnergyOrderAndPositiveGapUnitField
  ∷ s8SubThresholdLowerBoundTransportField
  ∷ s8PressureEnergyCoercivityWitnessField
  ∷ s8CarrierUnitNormalizationField
  ∷ []

canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterVacuum :
  List S8GlobalYangMillsHamiltonianCarrierTheoremField
canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterVacuum =
  s8NonVacuumSectorPredicateField
  ∷ s8VacuumOrthogonalityPredicateField
  ∷ s8EnergyOrderAndPositiveGapUnitField
  ∷ s8SubThresholdLowerBoundTransportField
  ∷ s8PressureEnergyCoercivityWitnessField
  ∷ s8CarrierUnitNormalizationField
  ∷ []

canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterNonVacuum :
  List S8GlobalYangMillsHamiltonianCarrierTheoremField
canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterNonVacuum =
  s8VacuumOrthogonalityPredicateField
  ∷ s8EnergyOrderAndPositiveGapUnitField
  ∷ s8SubThresholdLowerBoundTransportField
  ∷ s8PressureEnergyCoercivityWitnessField
  ∷ s8CarrierUnitNormalizationField
  ∷ []

canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterVacuumOrthogonality :
  List S8GlobalYangMillsHamiltonianCarrierTheoremField
canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterVacuumOrthogonality =
  s8EnergyOrderAndPositiveGapUnitField
  ∷ s8SubThresholdLowerBoundTransportField
  ∷ s8PressureEnergyCoercivityWitnessField
  ∷ s8CarrierUnitNormalizationField
  ∷ []

canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterEnergyOrderAndPositiveGapUnit :
  List S8GlobalYangMillsHamiltonianCarrierTheoremField
canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterEnergyOrderAndPositiveGapUnit =
  s8SubThresholdLowerBoundTransportField
  ∷ s8PressureEnergyCoercivityWitnessField
  ∷ s8CarrierUnitNormalizationField
  ∷ []

canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterSubThresholdLowerBoundTransport :
  List S8GlobalYangMillsHamiltonianCarrierTheoremField
canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterSubThresholdLowerBoundTransport =
  s8PressureEnergyCoercivityWitnessField
  ∷ s8CarrierUnitNormalizationField
  ∷ []

canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterPressureEnergyCoercivity :
  List S8GlobalYangMillsHamiltonianCarrierTheoremField
canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterPressureEnergyCoercivity =
  s8CarrierUnitNormalizationField
  ∷ []

canonicalPressureBelow15SpectralRequiredHypotheses :
  List PressureBelow15SpectralRequiredHypothesis
canonicalPressureBelow15SpectralRequiredHypotheses =
  requiresYangMillsHamiltonianCarrier
  ∷ requiresVacuumAndNonVacuumSector
  ∷ requiresVacuumOrthogonalityPredicate
  ∷ requiresEnergyOrderAndPositiveGapUnit
  ∷ requiresPressureEnergyCoercivity
  ∷ requiresSubThresholdLowerBound
  ∷ requiresCarrierUnitNormalization
  ∷ []

record PressureToSpectralGapHypothesisPackage : Setω where
  field
    State :
      Set

    Energy :
      Set

    vacuum :
      State

    nonVacuum :
      State →
      Set

    orthogonalToVacuum :
      State →
      Set

    hamiltonianEnergy :
      State →
      Energy

    _≤E_ :
      Energy →
      Energy →
      Set

    gapUnit :
      Energy

    gapUnitPositive :
      Set

    pressureEnergyCoercive :
      Set

    subThresholdLowerBound :
      (pressureBound : Nat) →
      (canonicalDim : Nat) →
      pressureBound < canonicalDim →
      (ψ : State) →
      nonVacuum ψ →
      orthogonalToVacuum ψ →
      gapUnit ≤E hamiltonianEnergy ψ

    carrierUnitNormalization :
      (pressureBound : Nat) →
      (canonicalDim : Nat) →
      canonicalDim ∸ pressureBound ≡ 1 →
      Set

open PressureToSpectralGapHypothesisPackage public

data S8ActiveYangMillsLane : Set where
  s8-p3-lane :
    S8ActiveYangMillsLane

  s8-p5-lane :
    S8ActiveYangMillsLane

  s8-p7-lane :
    S8ActiveYangMillsLane

s8ActiveYangMillsLanePrime :
  S8ActiveYangMillsLane →
  SSP
s8ActiveYangMillsLanePrime s8-p3-lane =
  p3
s8ActiveYangMillsLanePrime s8-p5-lane =
  p5
s8ActiveYangMillsLanePrime s8-p7-lane =
  p7

canonicalS8ActiveYangMillsLanes :
  List S8ActiveYangMillsLane
canonicalS8ActiveYangMillsLanes =
  s8-p3-lane
  ∷ s8-p5-lane
  ∷ s8-p7-lane
  ∷ []

s8LaneBaseEnergy :
  S8ActiveYangMillsLane →
  Nat
s8LaneBaseEnergy s8-p3-lane =
  3
s8LaneBaseEnergy s8-p5-lane =
  8
s8LaneBaseEnergy s8-p7-lane =
  3

s8LaneBaseEnergyIsLieAlgebraDimensionConvention :
  List String
s8LaneBaseEnergyIsLieAlgebraDimensionConvention =
  "Carrier-natural S8 convention: one FactorVec bump is one complete gauge plaquette traversal"
  ∷ "The p3 and p7 SU(2) lanes contribute dim(su2)=3 base energy units per bump"
  ∷ "The p5 SU(3) lane contributes dim(su3)=8 base energy units per bump"
  ∷ "This convention makes the pressure weight part of the electric-energy unit, rather than a later analytic inequality"
  ∷ []

record YangMillsHamiltonianLaneDecomposition
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    activeLanes :
      List S8ActiveYangMillsLane

    activeLanesAreCanonical :
      activeLanes
      ≡
      canonicalS8ActiveYangMillsLanes

    laneSupport :
      S8ActiveYangMillsLane →
      State hypotheses →
      FactorVec

    factorVecSupportsDisjoint :
      FactorVec →
      FactorVec →
      Set

    p3p5SupportsDisjoint :
      (ψ : State hypotheses) →
      factorVecSupportsDisjoint
        (laneSupport s8-p3-lane ψ)
        (laneSupport s8-p5-lane ψ)

    p3p7SupportsDisjoint :
      (ψ : State hypotheses) →
      factorVecSupportsDisjoint
        (laneSupport s8-p3-lane ψ)
        (laneSupport s8-p7-lane ψ)

    p5p7SupportsDisjoint :
      (ψ : State hypotheses) →
      factorVecSupportsDisjoint
        (laneSupport s8-p5-lane ψ)
        (laneSupport s8-p7-lane ψ)

    electricLaneEnergy :
      S8ActiveYangMillsLane →
      State hypotheses →
      Energy hypotheses

    magneticLaneEnergy :
      S8ActiveYangMillsLane →
      State hypotheses →
      Energy hypotheses

    electricPlusMagneticEnergy :
      Energy hypotheses →
      Energy hypotheses →
      Energy hypotheses

    laneHamiltonianEnergy :
      S8ActiveYangMillsLane →
      State hypotheses →
      Energy hypotheses

    laneHamiltonianEnergyIsElectricPlusMagnetic :
      (lane : S8ActiveYangMillsLane) →
      (ψ : State hypotheses) →
      laneHamiltonianEnergy lane ψ
      ≡
      electricPlusMagneticEnergy
        (electricLaneEnergy lane ψ)
        (magneticLaneEnergy lane ψ)

    activeLaneHamiltonianSum :
      Energy hypotheses →
      Energy hypotheses →
      Energy hypotheses →
      Energy hypotheses

    hamiltonianEnergyIsActiveLaneSum :
      (ψ : State hypotheses) →
      hamiltonianEnergy hypotheses ψ
      ≡
      activeLaneHamiltonianSum
        (laneHamiltonianEnergy s8-p3-lane ψ)
        (laneHamiltonianEnergy s8-p5-lane ψ)
        (laneHamiltonianEnergy s8-p7-lane ψ)

open YangMillsHamiltonianLaneDecomposition public

record S8LaneOccupationNumberSurface
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses)
  : Setω where
  field
    laneOccupationNumber :
      S8ActiveYangMillsLane →
      State hypotheses →
      Nat

    laneOccupationReadsSupport :
      (lane : S8ActiveYangMillsLane) →
      (ψ : State hypotheses) →
      Set

    occupiedLane :
      S8ActiveYangMillsLane →
      State hypotheses →
      Set

    occupiedLaneIsNonzeroOccupation :
      (lane : S8ActiveYangMillsLane) →
      (ψ : State hypotheses) →
      occupiedLane lane ψ →
      Set

open S8LaneOccupationNumberSurface public

s8LaneOccupationNumberSurfaceFromFields :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (laneOccupationNumber :
    S8ActiveYangMillsLane →
    State hypotheses →
    Nat) →
  (laneOccupationReadsSupport :
    (lane : S8ActiveYangMillsLane) →
    (ψ : State hypotheses) →
    Set) →
  (occupiedLane :
    S8ActiveYangMillsLane →
    State hypotheses →
    Set) →
  ((lane : S8ActiveYangMillsLane) →
    (ψ : State hypotheses) →
    occupiedLane lane ψ →
    Set) →
  S8LaneOccupationNumberSurface hypotheses decomposition
s8LaneOccupationNumberSurfaceFromFields
  hypotheses
  decomposition
  laneOccupationNumberWitness
  laneOccupationReadsSupportWitness
  occupiedLaneWitness
  occupiedLaneIsNonzeroOccupationWitness =
  record
    { laneOccupationNumber =
        laneOccupationNumberWitness
    ; laneOccupationReadsSupport =
        laneOccupationReadsSupportWitness
    ; occupiedLane =
        occupiedLaneWitness
    ; occupiedLaneIsNonzeroOccupation =
        occupiedLaneIsNonzeroOccupationWitness
    }

record S8MinimumNontrivialHolonomyDistanceSurface : Setω where
  field
    Holonomy :
      Set

    neutralHolonomy :
      Holonomy

    holonomyDistance :
      Holonomy →
      Holonomy →
      Nat

    nontrivialHolonomy :
      Holonomy →
      Set

    minimumNontrivialHolonomyDistance :
      Nat

    minimumNontrivialHolonomyDistanceIsCarrierUnit :
      minimumNontrivialHolonomyDistance
      ≡
      Probe.canonicalPressureDeficit

    nontrivialHolonomyDistanceLowerBound :
      (h : Holonomy) →
      nontrivialHolonomy h →
      Set

open S8MinimumNontrivialHolonomyDistanceSurface public

s8MinimumNontrivialHolonomyDistanceSurfaceFromFields :
  (Holonomy : Set) →
  Holonomy →
  (Holonomy → Holonomy → Nat) →
  (nontrivialHolonomy : Holonomy → Set) →
  (minimumNontrivialHolonomyDistance : Nat) →
  minimumNontrivialHolonomyDistance
  ≡
  Probe.canonicalPressureDeficit →
  ((h : Holonomy) →
    nontrivialHolonomy h →
    Set) →
  S8MinimumNontrivialHolonomyDistanceSurface
s8MinimumNontrivialHolonomyDistanceSurfaceFromFields
  HolonomyWitness
  neutralHolonomyWitness
  holonomyDistanceWitness
  nontrivialHolonomyWitness
  minimumNontrivialHolonomyDistanceWitness
  minimumNontrivialHolonomyDistanceIsCarrierUnitWitness
  nontrivialHolonomyDistanceLowerBoundWitness =
  record
    { Holonomy =
        HolonomyWitness
    ; neutralHolonomy =
        neutralHolonomyWitness
    ; holonomyDistance =
        holonomyDistanceWitness
    ; nontrivialHolonomy =
        nontrivialHolonomyWitness
    ; minimumNontrivialHolonomyDistance =
        minimumNontrivialHolonomyDistanceWitness
    ; minimumNontrivialHolonomyDistanceIsCarrierUnit =
        minimumNontrivialHolonomyDistanceIsCarrierUnitWitness
    ; nontrivialHolonomyDistanceLowerBound =
        nontrivialHolonomyDistanceLowerBoundWitness
    }

record S8PressureNormSquaredLaneWeightSurface
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  {decomposition : YangMillsHamiltonianLaneDecomposition hypotheses}
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition)
  : Setω where
  field
    holonomyDistanceSurface :
      S8MinimumNontrivialHolonomyDistanceSurface

    lanePressureWeight :
      S8ActiveYangMillsLane →
      Nat

    weightedLanePressureEnergy :
      S8ActiveYangMillsLane →
      State hypotheses →
      Energy hypotheses

    pressureNorm² :
      State hypotheses →
      Energy hypotheses

    pressureNormSquaredIsWeightedOccupationSum :
      (ψ : State hypotheses) →
      Set

    holonomyDistanceWeightsNontrivialOccupation :
      (lane : S8ActiveYangMillsLane) →
      (ψ : State hypotheses) →
      occupiedLane occupation lane ψ →
      Set

open S8PressureNormSquaredLaneWeightSurface public

s8PressureNormSquaredLaneWeightSurfaceFromFields :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  {decomposition : YangMillsHamiltonianLaneDecomposition hypotheses} →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  S8MinimumNontrivialHolonomyDistanceSurface →
  (S8ActiveYangMillsLane → Nat) →
  (S8ActiveYangMillsLane →
    State hypotheses →
    Energy hypotheses) →
  (State hypotheses →
    Energy hypotheses) →
  ((ψ : State hypotheses) →
    Set) →
  ((lane : S8ActiveYangMillsLane) →
    (ψ : State hypotheses) →
    occupiedLane occupation lane ψ →
    Set) →
  S8PressureNormSquaredLaneWeightSurface hypotheses occupation
s8PressureNormSquaredLaneWeightSurfaceFromFields
  hypotheses
  occupationWitness
  holonomyDistanceSurfaceWitness
  lanePressureWeightWitness
  weightedLanePressureEnergyWitness
  pressureNormSquaredWitness
  pressureNormSquaredIsWeightedOccupationSumWitness
  holonomyDistanceWeightsNontrivialOccupationWitness =
  record
    { holonomyDistanceSurface =
        holonomyDistanceSurfaceWitness
    ; lanePressureWeight =
        lanePressureWeightWitness
    ; weightedLanePressureEnergy =
        weightedLanePressureEnergyWitness
    ; pressureNorm² =
        pressureNormSquaredWitness
    ; pressureNormSquaredIsWeightedOccupationSum =
        pressureNormSquaredIsWeightedOccupationSumWitness
    ; holonomyDistanceWeightsNontrivialOccupation =
        holonomyDistanceWeightsNontrivialOccupationWitness
    }

S8LowerBoundTransport :
  PressureToSpectralGapHypothesisPackage →
  Set
S8LowerBoundTransport hypotheses =
  (ψ : State hypotheses) →
  nonVacuum hypotheses ψ →
  orthogonalToVacuum hypotheses ψ →
  _≤E_ hypotheses
    (gapUnit hypotheses)
    (hamiltonianEnergy hypotheses ψ)

record S8PressureEnergyCoercivityPrimitiveInterface
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    pressureNorm² :
      State hypotheses →
      Energy hypotheses

    pressureOrderTransitive :
      (a b c : Energy hypotheses) →
      _≤E_ hypotheses a b →
      _≤E_ hypotheses b c →
      _≤E_ hypotheses a c

    gapUnitDominatedByPressureNorm :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      _≤E_ hypotheses
        (gapUnit hypotheses)
        (pressureNorm² ψ)

    laneHamiltonianDominatesPressureNorm :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      _≤E_ hypotheses
        (pressureNorm² ψ)
        (hamiltonianEnergy hypotheses ψ)

open S8PressureEnergyCoercivityPrimitiveInterface public

record S8LaneEnergyOrderCompatibility
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses)
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition)
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation)
  : Setω where
  field
    s8LaneOrderTransitive :
      (a b c : Energy hypotheses) →
      _≤E_ hypotheses a b →
      _≤E_ hypotheses b c →
      _≤E_ hypotheses a c

    p3WeightedLanePressureDominatedByLaneHamiltonian :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      _≤E_ hypotheses
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p3-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p3-lane
          ψ)

    p5WeightedLanePressureDominatedByLaneHamiltonian :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      _≤E_ hypotheses
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p5-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p5-lane
          ψ)

    p7WeightedLanePressureDominatedByLaneHamiltonian :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      _≤E_ hypotheses
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p7-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p7-lane
          ψ)

    pressureNormWeightedLaneSumExpansion :
      (ψ : State hypotheses) →
      _≤E_ hypotheses
        (S8PressureNormSquaredLaneWeightSurface.pressureNorm²
          weighting
          ψ)
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
            weighting
            s8-p3-lane
            ψ)
          (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
            weighting
            s8-p5-lane
            ψ)
          (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
            weighting
            s8-p7-lane
            ψ))

    threeLaneWeightedPressureSumMonotonicity :
      (a3 a5 a7 b3 b5 b7 : Energy hypotheses) →
      _≤E_ hypotheses a3 b3 →
      _≤E_ hypotheses a5 b5 →
      _≤E_ hypotheses a7 b7 →
      _≤E_ hypotheses
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          a3
          a5
          a7)
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          b3
          b5
          b7)

    hamiltonianActiveLaneSumTransport :
      (ψ : State hypotheses) →
      _≤E_ hypotheses
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
            decomposition
            s8-p3-lane
            ψ)
          (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
            decomposition
            s8-p5-lane
            ψ)
          (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
            decomposition
            s8-p7-lane
            ψ))
        (hamiltonianEnergy hypotheses ψ)

open S8LaneEnergyOrderCompatibility public

data S8EnergyOrderNatBridgeSearchVerdict : Set where
  s8NoConstructiveNatOrderBridgeForOpaqueEnergyOrder :
    S8EnergyOrderNatBridgeSearchVerdict

data S8WrappedNatEnergySelectionVerdict : Set where
  s8WrappedNatEnergyNotSelectedFromOpaqueHypotheses :
    S8WrappedNatEnergySelectionVerdict

record S8WrappedLaneEnergy : Set where
  constructor s8-mkEnergy
  field
    wrappedLaneEnergyNat :
      Nat

open S8WrappedLaneEnergy public

_≤S8WrappedLaneEnergy_ :
  S8WrappedLaneEnergy →
  S8WrappedLaneEnergy →
  Set
left ≤S8WrappedLaneEnergy right =
  wrappedLaneEnergyNat left ≤ wrappedLaneEnergyNat right

s8WrappedLaneEnergyToNat :
  S8WrappedLaneEnergy →
  Nat
s8WrappedLaneEnergyToNat =
  wrappedLaneEnergyNat

s8WrappedLaneEnergyOrderPreservesNatOrder :
  (left right : S8WrappedLaneEnergy) →
  left ≤S8WrappedLaneEnergy right →
  s8WrappedLaneEnergyToNat left ≤ s8WrappedLaneEnergyToNat right
s8WrappedLaneEnergyOrderPreservesNatOrder left right left≤right =
  left≤right

s8WrappedLaneEnergyNatOrderReflectsEnergyOrder :
  (left right : S8WrappedLaneEnergy) →
  s8WrappedLaneEnergyToNat left ≤ s8WrappedLaneEnergyToNat right →
  left ≤S8WrappedLaneEnergy right
s8WrappedLaneEnergyNatOrderReflectsEnergyOrder left right left≤right =
  left≤right

record S8WrappedNatEnergyModelSelection
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    toWrappedLaneEnergy :
      Energy hypotheses →
      S8WrappedLaneEnergy

    selectedEnergyOrderPreservesWrappedNatOrder :
      (left right : Energy hypotheses) →
      _≤E_ hypotheses left right →
      s8WrappedLaneEnergyToNat (toWrappedLaneEnergy left)
      ≤
      s8WrappedLaneEnergyToNat (toWrappedLaneEnergy right)

    wrappedNatOrderReflectsSelectedEnergyOrder :
      (left right : Energy hypotheses) →
      s8WrappedLaneEnergyToNat (toWrappedLaneEnergy left)
      ≤
      s8WrappedLaneEnergyToNat (toWrappedLaneEnergy right) →
      _≤E_ hypotheses left right

    laneEnergyModelBoundary :
      List String

open S8WrappedNatEnergyModelSelection public

record S8UserSuppliedEnergy≃Nat
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    suppliedEnergyToNat :
      Energy hypotheses →
      Nat

    suppliedNatToEnergy :
      Nat →
      Energy hypotheses

    suppliedEnergyToNatAfterNatToEnergy :
      (n : Nat) →
      suppliedEnergyToNat (suppliedNatToEnergy n)
      ≡
      n

    suppliedNatToEnergyAfterEnergyToNat :
      (energy : Energy hypotheses) →
      suppliedNatToEnergy (suppliedEnergyToNat energy)
      ≡
      energy

    suppliedEnergyOrderPreservesNatOrder :
      (left right : Energy hypotheses) →
      _≤E_ hypotheses left right →
      suppliedEnergyToNat left
      ≤
      suppliedEnergyToNat right

    suppliedNatOrderReflectsEnergyOrder :
      (left right : Energy hypotheses) →
      suppliedEnergyToNat left
      ≤
      suppliedEnergyToNat right →
      _≤E_ hypotheses left right

    energyNatEquivalenceBoundary :
      List String

open S8UserSuppliedEnergy≃Nat public

s8WrappedNatEnergyModelSelectionFromUserSuppliedEnergy≃Nat :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8UserSuppliedEnergy≃Nat hypotheses →
  S8WrappedNatEnergyModelSelection hypotheses
s8WrappedNatEnergyModelSelectionFromUserSuppliedEnergy≃Nat
  hypotheses
  energy≃Nat =
  record
    { toWrappedLaneEnergy =
        λ energy →
          s8-mkEnergy
            (S8UserSuppliedEnergy≃Nat.suppliedEnergyToNat energy≃Nat energy)
    ; selectedEnergyOrderPreservesWrappedNatOrder =
        S8UserSuppliedEnergy≃Nat.suppliedEnergyOrderPreservesNatOrder energy≃Nat
    ; wrappedNatOrderReflectsSelectedEnergyOrder =
        S8UserSuppliedEnergy≃Nat.suppliedNatOrderReflectsEnergyOrder energy≃Nat
    ; laneEnergyModelBoundary =
        "Selected only from a user-supplied Energy≃Nat adapter for this concrete PressureToSpectralGapHypothesisPackage"
        ∷ "The adapter supplies Energy -> Nat, Nat -> Energy, inverse laws, and preservation/reflection for the package's _<=E_"
        ∷ "This constructor does not derive the adapter from the opaque package and does not construct pressureEnergyCoercive"
        ∷ []
    }

record S8UserSuppliedEnergy≃NatSelectionReport
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    targetSelectionName :
      String

    selectionVerdict :
      S8WrappedNatEnergySelectionVerdict

    selectionVerdictIsNotSelected :
      selectionVerdict
      ≡
      s8WrappedNatEnergyNotSelectedFromOpaqueHypotheses

    concreteWrappedNatPackageSelectedFromCurrentHypotheses :
      Bool

    concreteWrappedNatPackageSelectedFromCurrentHypothesesIsFalse :
      concreteWrappedNatPackageSelectedFromCurrentHypotheses
      ≡
      false

    userSuppliedAdapterRequired :
      String

    suppliedAdapterSurface :
      String

    adapterConstructedFromExistingDefinitions :
      Bool

    adapterConstructedFromExistingDefinitionsIsFalse :
      adapterConstructedFromExistingDefinitions
      ≡
      false

    pressureEnergyCoerciveConstructed :
      Bool

    pressureEnergyCoerciveConstructedIsFalse :
      pressureEnergyCoerciveConstructed
      ≡
      false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted
      ≡
      false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted
      ≡
      false

    selectionBoundary :
      List String

open S8UserSuppliedEnergy≃NatSelectionReport public

canonicalS8UserSuppliedEnergy≃NatSelectionReport :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8UserSuppliedEnergy≃NatSelectionReport hypotheses
canonicalS8UserSuppliedEnergy≃NatSelectionReport hypotheses =
  record
    { targetSelectionName =
        "S8WrappedNatEnergyModelSelection"
    ; selectionVerdict =
        s8WrappedNatEnergyNotSelectedFromOpaqueHypotheses
    ; selectionVerdictIsNotSelected =
        refl
    ; concreteWrappedNatPackageSelectedFromCurrentHypotheses =
        false
    ; concreteWrappedNatPackageSelectedFromCurrentHypothesesIsFalse =
        refl
    ; userSuppliedAdapterRequired =
        "S8UserSuppliedEnergy≃Nat hypotheses"
    ; suppliedAdapterSurface =
        "energyToNat, natToEnergy, inverse laws, energyOrderPreservesNatOrder, and natOrderReflectsEnergyOrder"
    ; adapterConstructedFromExistingDefinitions =
        false
    ; adapterConstructedFromExistingDefinitionsIsFalse =
        refl
    ; pressureEnergyCoerciveConstructed =
        false
    ; pressureEnergyCoerciveConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; selectionBoundary =
        "No concrete wrapped-Nat package can be selected from PressureToSpectralGapHypothesisPackage alone because Energy and _<=E_ are opaque fields"
        ∷ "The narrow admissible supply interface is S8UserSuppliedEnergy≃Nat: an Energy/Nat equivalence plus preservation and reflection for the package order"
        ∷ "Once supplied, s8WrappedNatEnergyModelSelectionFromUserSuppliedEnergy≃Nat selects the existing wrapped-Nat model without changing the package globally"
        ∷ "The selection report does not inhabit pressureEnergyCoercive and leaves every promotion flag false"
        ∷ []
    }

s8ConcreteWrappedNatPackageNotSelectedFromCurrentHypotheses :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8UserSuppliedEnergy≃NatSelectionReport.concreteWrappedNatPackageSelectedFromCurrentHypotheses
    (canonicalS8UserSuppliedEnergy≃NatSelectionReport hypotheses)
  ≡
  false
s8ConcreteWrappedNatPackageNotSelectedFromCurrentHypotheses hypotheses =
  refl

record S8WrappedNatEnergyModelRequest
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    requestedEnergyModelName :
      String

    requestedEnergyConstructor :
      String

    requestedOrderDefinition :
      String

    wrappedNatModelSelectedInHypotheses :
      Bool

    wrappedNatModelSelectedInHypothesesIsFalse :
      wrappedNatModelSelectedInHypotheses ≡ false

    bridgeConstructedOnlyAfterSelection :
      String

    noGapReceiptConstructedHere :
      Bool

    noGapReceiptConstructedHereIsFalse :
      noGapReceiptConstructedHere ≡ false

    modelBoundary :
      List String

open S8WrappedNatEnergyModelRequest public

canonicalS8WrappedNatEnergyModelRequest :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8WrappedNatEnergyModelRequest hypotheses
canonicalS8WrappedNatEnergyModelRequest hypotheses =
  record
    { requestedEnergyModelName =
        "S8WrappedLaneEnergy"
    ; requestedEnergyConstructor =
        "s8-mkEnergy : Nat -> S8WrappedLaneEnergy"
    ; requestedOrderDefinition =
        "left <=S8WrappedLaneEnergy right = wrappedLaneEnergyNat left <= wrappedLaneEnergyNat right"
    ; wrappedNatModelSelectedInHypotheses =
        false
    ; wrappedNatModelSelectedInHypothesesIsFalse =
        refl
    ; bridgeConstructedOnlyAfterSelection =
        "s8EnergyToNatOrderBridgeFromWrappedNatEnergyModel builds S8EnergyToNatOrderBridge once the package's opaque Energy/_<=E_ are related to S8WrappedLaneEnergy"
    ; noGapReceiptConstructedHere =
        false
    ; noGapReceiptConstructedHereIsFalse =
        refl
    ; modelBoundary =
        "The wrapped-Nat energy semantics requested for S8 is now explicit and has definitional preservation/reflection for its own order"
        ∷ "PressureToSpectralGapHypothesisPackage remains polymorphic in Energy and _<=E_, so this file cannot globally replace every package instance with S8WrappedLaneEnergy"
        ∷ "A selected S8WrappedNatEnergyModelSelection is the remaining mathematical/API commitment needed before the existing S8EnergyToNatOrderBridge compiler can run on a concrete package"
        ∷ "No spectral-gap receipt or promotion is constructed by defining the model"
        ∷ []
    }

record S8EnergyOrderNatBridgeSearchReport
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    searchedEnergyOrderField :
      String

    searchedNatBridgeTarget :
      String

    natOrderBridgeConstructed :
      Bool

    natOrderBridgeConstructedIsFalse :
      natOrderBridgeConstructed ≡ false

    energyOrderDefinableWithoutNewPostulates :
      Bool

    energyOrderDefinableWithoutNewPostulatesIsFalse :
      energyOrderDefinableWithoutNewPostulates ≡ false

    bridgeSearchVerdict :
      S8EnergyOrderNatBridgeSearchVerdict

    bridgeSearchVerdictIsNoConstructiveBridge :
      bridgeSearchVerdict
      ≡
      s8NoConstructiveNatOrderBridgeForOpaqueEnergyOrder

    bridgeBoundary :
      List String

open S8EnergyOrderNatBridgeSearchReport public

canonicalS8EnergyOrderNatBridgeSearchReport :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8EnergyOrderNatBridgeSearchReport hypotheses
canonicalS8EnergyOrderNatBridgeSearchReport hypotheses =
  record
    { searchedEnergyOrderField =
        "_<=E_ : Energy hypotheses -> Energy hypotheses -> Set"
    ; searchedNatBridgeTarget =
        "A definitional or constructive bridge from _<=E_ to Data.Nat._<=_ for the S8 pressure/energy lanes"
    ; natOrderBridgeConstructed =
        false
    ; natOrderBridgeConstructedIsFalse =
        refl
    ; energyOrderDefinableWithoutNewPostulates =
        false
    ; energyOrderDefinableWithoutNewPostulatesIsFalse =
        refl
    ; bridgeSearchVerdict =
        s8NoConstructiveNatOrderBridgeForOpaqueEnergyOrder
    ; bridgeSearchVerdictIsNoConstructiveBridge =
        refl
    ; bridgeBoundary =
        "The searched Nat-order code provides Nat preorders for MDL/EnergySpace instances, but not a coercion from this package's arbitrary Energy carrier into Nat"
        ∷ "PressureToSpectralGapHypothesisPackage exposes _<=E_ only as a Set-valued field; it has no Nat ranking map, reflexivity, transitivity, or equality-transport law"
        ∷ "The lane weighting surface exposes Nat lane weights, but weightedLanePressureEnergy, pressureNormSquared, laneHamiltonianEnergy, and hamiltonianEnergy all live in the opaque Energy carrier"
        ∷ "Without an Energy -> Nat interpretation plus a proof that _<=E_ is reflected or preserved by Nat order, the Nat-order route cannot construct the required lane inequalities"
        ∷ "The remaining conservative route is therefore an explicit external lemma interface for the six non-transitivity lane/sum/transport witnesses"
        ∷ []
    }

record S8EnergyToNatOrderBridge
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    energyToNat :
      Energy hypotheses →
      Nat

    energyOrderPreservesNatOrder :
      (a b : Energy hypotheses) →
      _≤E_ hypotheses a b →
      energyToNat a ≤ energyToNat b

    natOrderReflectsEnergyOrder :
      (a b : Energy hypotheses) →
      energyToNat a ≤ energyToNat b →
      _≤E_ hypotheses a b

open S8EnergyToNatOrderBridge public

s8EnergyToNatOrderBridgeFromWrappedNatEnergyModel :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8WrappedNatEnergyModelSelection hypotheses →
  S8EnergyToNatOrderBridge hypotheses
s8EnergyToNatOrderBridgeFromWrappedNatEnergyModel hypotheses selection =
  record
    { energyToNat =
        λ energy →
          s8WrappedLaneEnergyToNat
            (S8WrappedNatEnergyModelSelection.toWrappedLaneEnergy
              selection
              energy)
    ; energyOrderPreservesNatOrder =
        S8WrappedNatEnergyModelSelection.selectedEnergyOrderPreservesWrappedNatOrder
          selection
    ; natOrderReflectsEnergyOrder =
        S8WrappedNatEnergyModelSelection.wrappedNatOrderReflectsSelectedEnergyOrder
          selection
    }

s8EnergyToNatOrderBridgeFromUserSuppliedEnergy≃Nat :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8UserSuppliedEnergy≃Nat hypotheses →
  S8EnergyToNatOrderBridge hypotheses
s8EnergyToNatOrderBridgeFromUserSuppliedEnergy≃Nat
  hypotheses
  energy≃Nat =
  s8EnergyToNatOrderBridgeFromWrappedNatEnergyModel
    hypotheses
    (s8WrappedNatEnergyModelSelectionFromUserSuppliedEnergy≃Nat
      hypotheses
      energy≃Nat)

S8EnergyNatRank :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8EnergyToNatOrderBridge hypotheses →
  Energy hypotheses →
  Nat
S8EnergyNatRank hypotheses bridge =
  S8EnergyToNatOrderBridge.energyToNat bridge

s8EnergyToNatBridgeGivesEnergyOrderTransitive :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8EnergyToNatOrderBridge hypotheses →
  (a b c : Energy hypotheses) →
  _≤E_ hypotheses a b →
  _≤E_ hypotheses b c →
  _≤E_ hypotheses a c
s8EnergyToNatBridgeGivesEnergyOrderTransitive
  hypotheses
  bridge
  a
  b
  c
  a≤b
  b≤c =
  S8EnergyToNatOrderBridge.natOrderReflectsEnergyOrder bridge
    a
    c
    (NatP.≤-trans
      (S8EnergyToNatOrderBridge.energyOrderPreservesNatOrder bridge a b a≤b)
      (S8EnergyToNatOrderBridge.energyOrderPreservesNatOrder bridge b c b≤c))

record S8EnergyToNatLaneWitnessSurface
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses)
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition)
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation)
  (bridge : S8EnergyToNatOrderBridge hypotheses)
  : Setω where
  field
    p3WeightedLanePressureNatDominatedByLaneHamiltonian :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      S8EnergyNatRank hypotheses bridge
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p3-lane
          ψ)
      ≤
      S8EnergyNatRank hypotheses bridge
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p3-lane
          ψ)

    p5WeightedLanePressureNatDominatedByLaneHamiltonian :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      S8EnergyNatRank hypotheses bridge
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p5-lane
          ψ)
      ≤
      S8EnergyNatRank hypotheses bridge
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p5-lane
          ψ)

    p7WeightedLanePressureNatDominatedByLaneHamiltonian :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      S8EnergyNatRank hypotheses bridge
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p7-lane
          ψ)
      ≤
      S8EnergyNatRank hypotheses bridge
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p7-lane
          ψ)

    pressureNormNatWeightedLaneSumExpansion :
      (ψ : State hypotheses) →
      S8EnergyNatRank hypotheses bridge
        (S8PressureNormSquaredLaneWeightSurface.pressureNorm²
          weighting
          ψ)
      ≤
      S8EnergyNatRank hypotheses bridge
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
            weighting
            s8-p3-lane
            ψ)
          (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
            weighting
            s8-p5-lane
            ψ)
          (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
            weighting
            s8-p7-lane
            ψ))

    threeLaneNatWeightedPressureSumMonotonicity :
      (a3 a5 a7 b3 b5 b7 : Energy hypotheses) →
      S8EnergyNatRank hypotheses bridge a3 ≤
      S8EnergyNatRank hypotheses bridge b3 →
      S8EnergyNatRank hypotheses bridge a5 ≤
      S8EnergyNatRank hypotheses bridge b5 →
      S8EnergyNatRank hypotheses bridge a7 ≤
      S8EnergyNatRank hypotheses bridge b7 →
      S8EnergyNatRank hypotheses bridge
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          a3
          a5
          a7)
      ≤
      S8EnergyNatRank hypotheses bridge
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          b3
          b5
          b7)

    hamiltonianNatActiveLaneSumTransport :
      (ψ : State hypotheses) →
      S8EnergyNatRank hypotheses bridge
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
            decomposition
            s8-p3-lane
            ψ)
          (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
            decomposition
            s8-p5-lane
            ψ)
          (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
            decomposition
            s8-p7-lane
            ψ))
      ≤
      S8EnergyNatRank hypotheses bridge
        (hamiltonianEnergy hypotheses ψ)

open S8EnergyToNatLaneWitnessSurface public

record S8CarrierNaturalLaneEnergyUnitConvention
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses)
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition)
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation)
  (bridge : S8EnergyToNatOrderBridge hypotheses)
  : Setω where
  field
    laneBaseEnergy :
      S8ActiveYangMillsLane →
      Nat

    laneBaseEnergyIsCanonical :
      laneBaseEnergy
      ≡
      s8LaneBaseEnergy

    lanePressureWeightUsesBaseEnergy :
      (lane : S8ActiveYangMillsLane) →
      S8PressureNormSquaredLaneWeightSurface.lanePressureWeight
        weighting
        lane
      ≡
      laneBaseEnergy lane

    factorVecBumpIsCompletePlaquetteTraversal :
      List String

    p3FullPlaquetteModePackageNatBound :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      S8EnergyNatRank hypotheses bridge
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p3-lane
          ψ)
      ≤
      S8EnergyNatRank hypotheses bridge
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p3-lane
          ψ)

    p5FullPlaquetteModePackageNatBound :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      S8EnergyNatRank hypotheses bridge
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p5-lane
          ψ)
      ≤
      S8EnergyNatRank hypotheses bridge
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p5-lane
          ψ)

    p7FullPlaquetteModePackageNatBound :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      S8EnergyNatRank hypotheses bridge
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p7-lane
          ψ)
      ≤
      S8EnergyNatRank hypotheses bridge
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p7-lane
          ψ)

    pressureNormNatIsWeightedLaneSum :
      (ψ : State hypotheses) →
      S8EnergyNatRank hypotheses bridge
        (S8PressureNormSquaredLaneWeightSurface.pressureNorm²
          weighting
          ψ)
      ≤
      S8EnergyNatRank hypotheses bridge
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
            weighting
            s8-p3-lane
            ψ)
          (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
            weighting
            s8-p5-lane
            ψ)
          (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
            weighting
            s8-p7-lane
            ψ))

    threeLaneNatSumMonotone :
      (a3 a5 a7 b3 b5 b7 : Energy hypotheses) →
      S8EnergyNatRank hypotheses bridge a3 ≤
      S8EnergyNatRank hypotheses bridge b3 →
      S8EnergyNatRank hypotheses bridge a5 ≤
      S8EnergyNatRank hypotheses bridge b5 →
      S8EnergyNatRank hypotheses bridge a7 ≤
      S8EnergyNatRank hypotheses bridge b7 →
      S8EnergyNatRank hypotheses bridge
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          a3
          a5
          a7)
      ≤
      S8EnergyNatRank hypotheses bridge
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          b3
          b5
          b7)

    hamiltonianNatIsActiveLaneSum :
      (ψ : State hypotheses) →
      S8EnergyNatRank hypotheses bridge
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
            decomposition
            s8-p3-lane
            ψ)
          (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
            decomposition
            s8-p5-lane
            ψ)
          (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
            decomposition
            s8-p7-lane
            ψ))
      ≤
      S8EnergyNatRank hypotheses bridge
        (hamiltonianEnergy hypotheses ψ)

    conventionBoundary :
      List String

open S8CarrierNaturalLaneEnergyUnitConvention public

s8EnergyToNatLaneWitnessSurfaceFromCarrierNaturalUnitConvention :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  (bridge : S8EnergyToNatOrderBridge hypotheses) →
  S8CarrierNaturalLaneEnergyUnitConvention
    hypotheses
    decomposition
    occupation
    weighting
    bridge →
  S8EnergyToNatLaneWitnessSurface
    hypotheses
    decomposition
    occupation
    weighting
    bridge
s8EnergyToNatLaneWitnessSurfaceFromCarrierNaturalUnitConvention
  hypotheses
  decomposition
  occupation
  weighting
  bridge
  convention =
  record
    { p3WeightedLanePressureNatDominatedByLaneHamiltonian =
        S8CarrierNaturalLaneEnergyUnitConvention.p3FullPlaquetteModePackageNatBound
          convention
    ; p5WeightedLanePressureNatDominatedByLaneHamiltonian =
        S8CarrierNaturalLaneEnergyUnitConvention.p5FullPlaquetteModePackageNatBound
          convention
    ; p7WeightedLanePressureNatDominatedByLaneHamiltonian =
        S8CarrierNaturalLaneEnergyUnitConvention.p7FullPlaquetteModePackageNatBound
          convention
    ; pressureNormNatWeightedLaneSumExpansion =
        S8CarrierNaturalLaneEnergyUnitConvention.pressureNormNatIsWeightedLaneSum
          convention
    ; threeLaneNatWeightedPressureSumMonotonicity =
        S8CarrierNaturalLaneEnergyUnitConvention.threeLaneNatSumMonotone
          convention
    ; hamiltonianNatActiveLaneSumTransport =
        S8CarrierNaturalLaneEnergyUnitConvention.hamiltonianNatIsActiveLaneSum
          convention
    }

s8LaneEnergyOrderCompatibilityFromEnergyToNatBridge :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  (bridge : S8EnergyToNatOrderBridge hypotheses) →
  S8EnergyToNatLaneWitnessSurface
    hypotheses
    decomposition
    occupation
    weighting
    bridge →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting
s8LaneEnergyOrderCompatibilityFromEnergyToNatBridge
  hypotheses
  decomposition
  occupation
  weighting
  bridge
  natWitnesses =
  record
    { s8LaneOrderTransitive =
        s8EnergyToNatBridgeGivesEnergyOrderTransitive
          hypotheses
          bridge
    ; p3WeightedLanePressureDominatedByLaneHamiltonian =
        λ ψ ψNonVacuum ψOrthogonal →
          S8EnergyToNatOrderBridge.natOrderReflectsEnergyOrder bridge
            (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
              weighting
              s8-p3-lane
              ψ)
            (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
              decomposition
              s8-p3-lane
              ψ)
            (S8EnergyToNatLaneWitnessSurface.p3WeightedLanePressureNatDominatedByLaneHamiltonian
              natWitnesses
              ψ
              ψNonVacuum
              ψOrthogonal)
    ; p5WeightedLanePressureDominatedByLaneHamiltonian =
        λ ψ ψNonVacuum ψOrthogonal →
          S8EnergyToNatOrderBridge.natOrderReflectsEnergyOrder bridge
            (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
              weighting
              s8-p5-lane
              ψ)
            (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
              decomposition
              s8-p5-lane
              ψ)
            (S8EnergyToNatLaneWitnessSurface.p5WeightedLanePressureNatDominatedByLaneHamiltonian
              natWitnesses
              ψ
              ψNonVacuum
              ψOrthogonal)
    ; p7WeightedLanePressureDominatedByLaneHamiltonian =
        λ ψ ψNonVacuum ψOrthogonal →
          S8EnergyToNatOrderBridge.natOrderReflectsEnergyOrder bridge
            (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
              weighting
              s8-p7-lane
              ψ)
            (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
              decomposition
              s8-p7-lane
              ψ)
            (S8EnergyToNatLaneWitnessSurface.p7WeightedLanePressureNatDominatedByLaneHamiltonian
              natWitnesses
              ψ
              ψNonVacuum
              ψOrthogonal)
    ; pressureNormWeightedLaneSumExpansion =
        λ ψ →
          S8EnergyToNatOrderBridge.natOrderReflectsEnergyOrder bridge
            (S8PressureNormSquaredLaneWeightSurface.pressureNorm²
              weighting
              ψ)
            (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
              decomposition
              (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
                weighting
                s8-p3-lane
                ψ)
              (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
                weighting
                s8-p5-lane
                ψ)
              (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
                weighting
                s8-p7-lane
                ψ))
            (S8EnergyToNatLaneWitnessSurface.pressureNormNatWeightedLaneSumExpansion
              natWitnesses
              ψ)
    ; threeLaneWeightedPressureSumMonotonicity =
        λ a3 a5 a7 b3 b5 b7 a3≤b3 a5≤b5 a7≤b7 →
          S8EnergyToNatOrderBridge.natOrderReflectsEnergyOrder bridge
            (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
              decomposition
              a3
              a5
              a7)
            (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
              decomposition
              b3
              b5
              b7)
            (S8EnergyToNatLaneWitnessSurface.threeLaneNatWeightedPressureSumMonotonicity
              natWitnesses
              a3
              a5
              a7
              b3
              b5
              b7
              (S8EnergyToNatOrderBridge.energyOrderPreservesNatOrder bridge a3 b3 a3≤b3)
              (S8EnergyToNatOrderBridge.energyOrderPreservesNatOrder bridge a5 b5 a5≤b5)
              (S8EnergyToNatOrderBridge.energyOrderPreservesNatOrder bridge a7 b7 a7≤b7))
    ; hamiltonianActiveLaneSumTransport =
        λ ψ →
          S8EnergyToNatOrderBridge.natOrderReflectsEnergyOrder bridge
            (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
              decomposition
              (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
                decomposition
                s8-p3-lane
                ψ)
              (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
                decomposition
                s8-p5-lane
                ψ)
              (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
                decomposition
                s8-p7-lane
                ψ))
            (hamiltonianEnergy hypotheses ψ)
            (S8EnergyToNatLaneWitnessSurface.hamiltonianNatActiveLaneSumTransport
              natWitnesses
              ψ)
    }

s8LaneEnergyOrderCompatibilityFromCarrierNaturalUnitConvention :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  (bridge : S8EnergyToNatOrderBridge hypotheses) →
  S8CarrierNaturalLaneEnergyUnitConvention
    hypotheses
    decomposition
    occupation
    weighting
    bridge →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting
s8LaneEnergyOrderCompatibilityFromCarrierNaturalUnitConvention
  hypotheses
  decomposition
  occupation
  weighting
  bridge
  convention =
  s8LaneEnergyOrderCompatibilityFromEnergyToNatBridge
    hypotheses
    decomposition
    occupation
    weighting
    bridge
    (s8EnergyToNatLaneWitnessSurfaceFromCarrierNaturalUnitConvention
      hypotheses
      decomposition
      occupation
      weighting
      bridge
      convention)

s8LaneEnergyOrderCompatibilityFromUserSuppliedEnergy≃NatAndSixNatWitnesses :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  (energy≃Nat : S8UserSuppliedEnergy≃Nat hypotheses) →
  S8EnergyToNatLaneWitnessSurface
    hypotheses
    decomposition
    occupation
    weighting
    (s8EnergyToNatOrderBridgeFromUserSuppliedEnergy≃Nat
      hypotheses
      energy≃Nat) →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting
s8LaneEnergyOrderCompatibilityFromUserSuppliedEnergy≃NatAndSixNatWitnesses
  hypotheses
  decomposition
  occupation
  weighting
  energy≃Nat
  sixNatWitnesses =
  s8LaneEnergyOrderCompatibilityFromEnergyToNatBridge
    hypotheses
    decomposition
    occupation
    weighting
    (s8EnergyToNatOrderBridgeFromUserSuppliedEnergy≃Nat
      hypotheses
      energy≃Nat)
    sixNatWitnesses

data S8EnergyToNatOrderBridgeMissingLaw : Set where
  s8EnergyToNatInterpretationLawField :
    S8EnergyToNatOrderBridgeMissingLaw

  s8EnergyOrderPreservesNatOrderLawField :
    S8EnergyToNatOrderBridgeMissingLaw

  s8NatOrderReflectsEnergyOrderLawField :
    S8EnergyToNatOrderBridgeMissingLaw

  s8WeightedLanePressureNatDominanceLawField :
    S8EnergyToNatOrderBridgeMissingLaw

  s8PressureNormNatWeightedLaneSumExpansionLawField :
    S8EnergyToNatOrderBridgeMissingLaw

  s8ThreeLaneNatWeightedPressureSumMonotonicityLawField :
    S8EnergyToNatOrderBridgeMissingLaw

  s8HamiltonianNatActiveLaneSumTransportLawField :
    S8EnergyToNatOrderBridgeMissingLaw

canonicalS8EnergyToNatOrderBridgeMissingLaws :
  List S8EnergyToNatOrderBridgeMissingLaw
canonicalS8EnergyToNatOrderBridgeMissingLaws =
  s8EnergyToNatInterpretationLawField
  ∷ s8EnergyOrderPreservesNatOrderLawField
  ∷ s8NatOrderReflectsEnergyOrderLawField
  ∷ s8WeightedLanePressureNatDominanceLawField
  ∷ s8PressureNormNatWeightedLaneSumExpansionLawField
  ∷ s8ThreeLaneNatWeightedPressureSumMonotonicityLawField
  ∷ s8HamiltonianNatActiveLaneSumTransportLawField
  ∷ []

record S8EnergyToNatOrderBridgeRequest
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses)
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition)
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation)
  : Setω where
  field
    bridgeTargetName :
      String

    exactMissingBridgeLaws :
      List S8EnergyToNatOrderBridgeMissingLaw

    exactMissingBridgeLawsAreCanonical :
      exactMissingBridgeLaws
      ≡
      canonicalS8EnergyToNatOrderBridgeMissingLaws

    firstMissingBridgeLaw :
      S8EnergyToNatOrderBridgeMissingLaw

    firstMissingBridgeLawIsEnergyToNatInterpretation :
      firstMissingBridgeLaw
      ≡
      s8EnergyToNatInterpretationLawField

    requestedEnergyToNatType :
      String

    requestedEnergyOrderPreservationType :
      String

    requestedNatOrderReflectionType :
      String

    requestedNatWitnessSurfaceType :
      String

    bridgeConstructedFromExistingDefinitions :
      Bool

    bridgeConstructedFromExistingDefinitionsIsFalse :
      bridgeConstructedFromExistingDefinitions ≡ false

    anySixWitnessDerivedFromExistingDefinitions :
      Bool

    anySixWitnessDerivedFromExistingDefinitionsIsFalse :
      anySixWitnessDerivedFromExistingDefinitions ≡ false

    gapReceiptConstructed :
      Bool

    gapReceiptConstructedIsFalse :
      gapReceiptConstructed ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    bridgeRequestBoundary :
      List String

open S8EnergyToNatOrderBridgeRequest public

canonicalS8EnergyToNatOrderBridgeRequest :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8EnergyToNatOrderBridgeRequest
    hypotheses
    decomposition
    occupation
    weighting
canonicalS8EnergyToNatOrderBridgeRequest
  hypotheses
  decomposition
  occupation
  weighting =
  record
    { bridgeTargetName =
        "S8EnergyToNatOrderBridge plus S8EnergyToNatLaneWitnessSurface"
    ; exactMissingBridgeLaws =
        canonicalS8EnergyToNatOrderBridgeMissingLaws
    ; exactMissingBridgeLawsAreCanonical =
        refl
    ; firstMissingBridgeLaw =
        s8EnergyToNatInterpretationLawField
    ; firstMissingBridgeLawIsEnergyToNatInterpretation =
        refl
    ; requestedEnergyToNatType =
        "energyToNat : Energy hypotheses -> Nat"
    ; requestedEnergyOrderPreservationType =
        "energyOrderPreservesNatOrder : a <=E b -> energyToNat a <= energyToNat b"
    ; requestedNatOrderReflectionType =
        "natOrderReflectsEnergyOrder : energyToNat a <= energyToNat b -> a <=E b"
    ; requestedNatWitnessSurfaceType =
        "Nat-side p3/p5/p7 lane dominance, pressureNorm expansion, three-lane sum monotonicity, and Hamiltonian active-lane transport for energyToNat"
    ; bridgeConstructedFromExistingDefinitions =
        false
    ; bridgeConstructedFromExistingDefinitionsIsFalse =
        refl
    ; anySixWitnessDerivedFromExistingDefinitions =
        false
    ; anySixWitnessDerivedFromExistingDefinitionsIsFalse =
        refl
    ; gapReceiptConstructed =
        false
    ; gapReceiptConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; bridgeRequestBoundary =
        "The Nat route is typed: a supplied Energy -> Nat interpreter with preservation and reflection compiles Nat-side lane witnesses into S8LaneEnergyOrderCompatibility"
        ∷ "The inspected local Nat data are laneOccupationNumber, lanePressureWeight, holonomyDistance, and existing Nat preorder instances; none interprets this package's opaque Energy carrier"
        ∷ "The first missing bridge law is energyToNat : Energy hypotheses -> Nat"
        ∷ "Preservation is missing: a <=E b does not imply energyToNat a <= energyToNat b for any local energyToNat"
        ∷ "Reflection is missing: energyToNat a <= energyToNat b does not imply a <=E b for the package order"
        ∷ "The Nat-side weighted-lane dominance laws for p3, p5, and p7 are missing"
        ∷ "The Nat-side pressureNorm weighted-lane expansion law is missing"
        ∷ "The Nat-side activeLaneHamiltonianSum monotonicity law is missing"
        ∷ "The Nat-side Hamiltonian active-lane transport law is missing"
        ∷ "Therefore no one of the six Energy-order witnesses is derivable from existing definitions by this bridge route"
        ∷ "No spectral gap receipt or promotion is constructed by this request"
        ∷ []
    }

s8EnergyToNatOrderBridgeAbsentFromExistingDefinitions :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8EnergyToNatOrderBridgeRequest.bridgeConstructedFromExistingDefinitions
    (canonicalS8EnergyToNatOrderBridgeRequest
      hypotheses
      decomposition
      occupation
      weighting)
  ≡
  false
s8EnergyToNatOrderBridgeAbsentFromExistingDefinitions
  hypotheses
  decomposition
  occupation
  weighting =
  refl

s8LaneEnergyOrderCompatibilityFromFiniteLaneOrderArithmeticFields :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  ((a b c : Energy hypotheses) →
    _≤E_ hypotheses a b →
    _≤E_ hypotheses b c →
    _≤E_ hypotheses a c) →
  ((ψ : State hypotheses) →
    nonVacuum hypotheses ψ →
    orthogonalToVacuum hypotheses ψ →
    _≤E_ hypotheses
      (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
        weighting
        s8-p3-lane
        ψ)
      (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
        decomposition
        s8-p3-lane
        ψ)) →
  ((ψ : State hypotheses) →
    nonVacuum hypotheses ψ →
    orthogonalToVacuum hypotheses ψ →
    _≤E_ hypotheses
      (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
        weighting
        s8-p5-lane
        ψ)
      (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
        decomposition
        s8-p5-lane
        ψ)) →
  ((ψ : State hypotheses) →
    nonVacuum hypotheses ψ →
    orthogonalToVacuum hypotheses ψ →
    _≤E_ hypotheses
      (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
        weighting
        s8-p7-lane
        ψ)
      (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
        decomposition
        s8-p7-lane
        ψ)) →
  ((ψ : State hypotheses) →
    _≤E_ hypotheses
      (S8PressureNormSquaredLaneWeightSurface.pressureNorm² weighting ψ)
      (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
        decomposition
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p3-lane
          ψ)
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p5-lane
          ψ)
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p7-lane
          ψ))) →
  ((a3 a5 a7 b3 b5 b7 : Energy hypotheses) →
    _≤E_ hypotheses a3 b3 →
    _≤E_ hypotheses a5 b5 →
    _≤E_ hypotheses a7 b7 →
    _≤E_ hypotheses
      (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
        decomposition
        a3
        a5
        a7)
      (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
        decomposition
        b3
        b5
        b7)) →
  ((ψ : State hypotheses) →
    _≤E_ hypotheses
      (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
        decomposition
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p3-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p5-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p7-lane
          ψ))
      (hamiltonianEnergy hypotheses ψ)) →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting
s8LaneEnergyOrderCompatibilityFromFiniteLaneOrderArithmeticFields
  hypotheses
  decomposition
  occupation
  weighting
  orderTransitiveWitness
  p3WeightedLanePressureDominance
  p5WeightedLanePressureDominance
  p7WeightedLanePressureDominance
  pressureNormWeightedLaneSumExpansionWitness
  threeLaneWeightedPressureSumMonotonicityWitness
  hamiltonianActiveLaneSumTransportWitness =
  record
    { s8LaneOrderTransitive =
        orderTransitiveWitness
    ; p3WeightedLanePressureDominatedByLaneHamiltonian =
        p3WeightedLanePressureDominance
    ; p5WeightedLanePressureDominatedByLaneHamiltonian =
        p5WeightedLanePressureDominance
    ; p7WeightedLanePressureDominatedByLaneHamiltonian =
        p7WeightedLanePressureDominance
    ; pressureNormWeightedLaneSumExpansion =
        pressureNormWeightedLaneSumExpansionWitness
    ; threeLaneWeightedPressureSumMonotonicity =
        threeLaneWeightedPressureSumMonotonicityWitness
    ; hamiltonianActiveLaneSumTransport =
        hamiltonianActiveLaneSumTransportWitness
    }

record S8LaneSumDominanceExternalLemmaInterface
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses)
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition)
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation)
  : Setω where
  field
    exactExternalLemmaFields :
      List S8LaneSumDominanceCompilerMissingField

    exactExternalLemmaFieldsAreCanonical :
      exactExternalLemmaFields
      ≡
      canonicalS8LaneSumDominanceCompilerMissingFields

    natBridgeSearchReport :
      S8EnergyOrderNatBridgeSearchReport hypotheses

    p3WeightedLanePressureDominatedByLaneHamiltonian :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      _≤E_ hypotheses
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p3-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p3-lane
          ψ)

    p5WeightedLanePressureDominatedByLaneHamiltonian :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      _≤E_ hypotheses
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p5-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p5-lane
          ψ)

    p7WeightedLanePressureDominatedByLaneHamiltonian :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      _≤E_ hypotheses
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p7-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p7-lane
          ψ)

    pressureNormWeightedLaneSumExpansion :
      (ψ : State hypotheses) →
      _≤E_ hypotheses
        (S8PressureNormSquaredLaneWeightSurface.pressureNorm²
          weighting
          ψ)
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
            weighting
            s8-p3-lane
            ψ)
          (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
            weighting
            s8-p5-lane
            ψ)
          (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
            weighting
            s8-p7-lane
            ψ))

    threeLaneWeightedPressureSumMonotonicity :
      (a3 a5 a7 b3 b5 b7 : Energy hypotheses) →
      _≤E_ hypotheses a3 b3 →
      _≤E_ hypotheses a5 b5 →
      _≤E_ hypotheses a7 b7 →
      _≤E_ hypotheses
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          a3
          a5
          a7)
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          b3
          b5
          b7)

    hamiltonianActiveLaneSumTransport :
      (ψ : State hypotheses) →
      _≤E_ hypotheses
        (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
          decomposition
          (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
            decomposition
            s8-p3-lane
            ψ)
          (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
            decomposition
            s8-p5-lane
            ψ)
          (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
            decomposition
            s8-p7-lane
            ψ))
        (hamiltonianEnergy hypotheses ψ)

    externalLemmaBoundary :
      List String

open S8LaneSumDominanceExternalLemmaInterface public

s8LaneSumDominanceExternalLemmaInterfaceFromFields :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  ((ψ : State hypotheses) →
    nonVacuum hypotheses ψ →
    orthogonalToVacuum hypotheses ψ →
    _≤E_ hypotheses
      (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
        weighting
        s8-p3-lane
        ψ)
      (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
        decomposition
        s8-p3-lane
        ψ)) →
  ((ψ : State hypotheses) →
    nonVacuum hypotheses ψ →
    orthogonalToVacuum hypotheses ψ →
    _≤E_ hypotheses
      (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
        weighting
        s8-p5-lane
        ψ)
      (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
        decomposition
        s8-p5-lane
        ψ)) →
  ((ψ : State hypotheses) →
    nonVacuum hypotheses ψ →
    orthogonalToVacuum hypotheses ψ →
    _≤E_ hypotheses
      (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
        weighting
        s8-p7-lane
        ψ)
      (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
        decomposition
        s8-p7-lane
        ψ)) →
  ((ψ : State hypotheses) →
    _≤E_ hypotheses
      (S8PressureNormSquaredLaneWeightSurface.pressureNorm²
        weighting
        ψ)
      (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
        decomposition
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p3-lane
          ψ)
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p5-lane
          ψ)
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p7-lane
          ψ))) →
  ((a3 a5 a7 b3 b5 b7 : Energy hypotheses) →
    _≤E_ hypotheses a3 b3 →
    _≤E_ hypotheses a5 b5 →
    _≤E_ hypotheses a7 b7 →
    _≤E_ hypotheses
      (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
        decomposition
        a3
        a5
        a7)
      (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
        decomposition
        b3
        b5
        b7)) →
  ((ψ : State hypotheses) →
    _≤E_ hypotheses
      (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
        decomposition
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p3-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p5-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p7-lane
          ψ))
      (hamiltonianEnergy hypotheses ψ)) →
  List String →
  S8LaneSumDominanceExternalLemmaInterface
    hypotheses
    decomposition
    occupation
    weighting
s8LaneSumDominanceExternalLemmaInterfaceFromFields
  hypotheses
  decomposition
  occupation
  weighting
  p3WeightedLanePressureDominance
  p5WeightedLanePressureDominance
  p7WeightedLanePressureDominance
  pressureNormWeightedLaneSumExpansionWitness
  threeLaneWeightedPressureSumMonotonicityWitness
  hamiltonianActiveLaneSumTransportWitness
  externalLemmaBoundaryWitness =
  record
    { exactExternalLemmaFields =
        canonicalS8LaneSumDominanceCompilerMissingFields
    ; exactExternalLemmaFieldsAreCanonical =
        refl
    ; natBridgeSearchReport =
        canonicalS8EnergyOrderNatBridgeSearchReport hypotheses
    ; p3WeightedLanePressureDominatedByLaneHamiltonian =
        p3WeightedLanePressureDominance
    ; p5WeightedLanePressureDominatedByLaneHamiltonian =
        p5WeightedLanePressureDominance
    ; p7WeightedLanePressureDominatedByLaneHamiltonian =
        p7WeightedLanePressureDominance
    ; pressureNormWeightedLaneSumExpansion =
        pressureNormWeightedLaneSumExpansionWitness
    ; threeLaneWeightedPressureSumMonotonicity =
        threeLaneWeightedPressureSumMonotonicityWitness
    ; hamiltonianActiveLaneSumTransport =
        hamiltonianActiveLaneSumTransportWitness
    ; externalLemmaBoundary =
        externalLemmaBoundaryWitness
    }

record S8LaneSumDominanceExternalLemmaInterfaceAbsenceLedger
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses)
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition)
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation)
  : Setω where
  field
    targetInterfaceName :
      String

    exactExternalLemmaFields :
      List S8LaneSumDominanceCompilerMissingField

    exactExternalLemmaFieldsAreCanonical :
      exactExternalLemmaFields
      ≡
      canonicalS8LaneSumDominanceCompilerMissingFields

    p3WitnessType :
      String

    p5WitnessType :
      String

    p7WitnessType :
      String

    pressureExpansionWitnessType :
      String

    threeLaneMonotonicityWitnessType :
      String

    hamiltonianTransportWitnessType :
      String

    p3WitnessConstructedFromExistingDefinitions :
      Bool

    p3WitnessConstructedFromExistingDefinitionsIsFalse :
      p3WitnessConstructedFromExistingDefinitions ≡ false

    p5WitnessConstructedFromExistingDefinitions :
      Bool

    p5WitnessConstructedFromExistingDefinitionsIsFalse :
      p5WitnessConstructedFromExistingDefinitions ≡ false

    p7WitnessConstructedFromExistingDefinitions :
      Bool

    p7WitnessConstructedFromExistingDefinitionsIsFalse :
      p7WitnessConstructedFromExistingDefinitions ≡ false

    pressureExpansionConstructedFromExistingDefinitions :
      Bool

    pressureExpansionConstructedFromExistingDefinitionsIsFalse :
      pressureExpansionConstructedFromExistingDefinitions ≡ false

    threeLaneMonotonicityConstructedFromExistingDefinitions :
      Bool

    threeLaneMonotonicityConstructedFromExistingDefinitionsIsFalse :
      threeLaneMonotonicityConstructedFromExistingDefinitions ≡ false

    hamiltonianTransportConstructedFromExistingDefinitions :
      Bool

    hamiltonianTransportConstructedFromExistingDefinitionsIsFalse :
      hamiltonianTransportConstructedFromExistingDefinitions ≡ false

    externalLemmaInterfaceConstructedFromExistingDefinitions :
      Bool

    externalLemmaInterfaceConstructedFromExistingDefinitionsIsFalse :
      externalLemmaInterfaceConstructedFromExistingDefinitions ≡ false

    gapReceiptConstructed :
      Bool

    gapReceiptConstructedIsFalse :
      gapReceiptConstructed ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    absenceBoundary :
      List String

open S8LaneSumDominanceExternalLemmaInterfaceAbsenceLedger public

canonicalS8LaneSumDominanceExternalLemmaInterfaceAbsenceLedger :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8LaneSumDominanceExternalLemmaInterfaceAbsenceLedger
    hypotheses
    decomposition
    occupation
    weighting
canonicalS8LaneSumDominanceExternalLemmaInterfaceAbsenceLedger
  hypotheses
  decomposition
  occupation
  weighting =
  record
    { targetInterfaceName =
        "S8LaneSumDominanceExternalLemmaInterface"
    ; exactExternalLemmaFields =
        canonicalS8LaneSumDominanceCompilerMissingFields
    ; exactExternalLemmaFieldsAreCanonical =
        refl
    ; p3WitnessType =
        "nonVacuum psi -> orthogonalToVacuum psi -> weightedLanePressureEnergy p3 psi <=E laneHamiltonianEnergy p3 psi"
    ; p5WitnessType =
        "nonVacuum psi -> orthogonalToVacuum psi -> weightedLanePressureEnergy p5 psi <=E laneHamiltonianEnergy p5 psi"
    ; p7WitnessType =
        "nonVacuum psi -> orthogonalToVacuum psi -> weightedLanePressureEnergy p7 psi <=E laneHamiltonianEnergy p7 psi"
    ; pressureExpansionWitnessType =
        "pressureNormSquared psi <=E activeLaneHamiltonianSum weighted-p3 weighted-p5 weighted-p7"
    ; threeLaneMonotonicityWitnessType =
        "a3 <=E b3 -> a5 <=E b5 -> a7 <=E b7 -> activeLaneHamiltonianSum a3 a5 a7 <=E activeLaneHamiltonianSum b3 b5 b7"
    ; hamiltonianTransportWitnessType =
        "activeLaneHamiltonianSum h3 h5 h7 <=E hamiltonianEnergy psi for the decomposition lane Hamiltonians"
    ; p3WitnessConstructedFromExistingDefinitions =
        false
    ; p3WitnessConstructedFromExistingDefinitionsIsFalse =
        refl
    ; p5WitnessConstructedFromExistingDefinitions =
        false
    ; p5WitnessConstructedFromExistingDefinitionsIsFalse =
        refl
    ; p7WitnessConstructedFromExistingDefinitions =
        false
    ; p7WitnessConstructedFromExistingDefinitionsIsFalse =
        refl
    ; pressureExpansionConstructedFromExistingDefinitions =
        false
    ; pressureExpansionConstructedFromExistingDefinitionsIsFalse =
        refl
    ; threeLaneMonotonicityConstructedFromExistingDefinitions =
        false
    ; threeLaneMonotonicityConstructedFromExistingDefinitionsIsFalse =
        refl
    ; hamiltonianTransportConstructedFromExistingDefinitions =
        false
    ; hamiltonianTransportConstructedFromExistingDefinitionsIsFalse =
        refl
    ; externalLemmaInterfaceConstructedFromExistingDefinitions =
        false
    ; externalLemmaInterfaceConstructedFromExistingDefinitionsIsFalse =
        refl
    ; gapReceiptConstructed =
        false
    ; gapReceiptConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; absenceBoundary =
        "A named non-promoting constructor now packages S8LaneSumDominanceExternalLemmaInterface only after all six exact witnesses are supplied"
        ∷ "The local decomposition exposes hamiltonianEnergyIsActiveLaneSum as propositional equality, but no <=E reflexivity or equality-transport law is available for constructing hamiltonianActiveLaneSumTransport"
        ∷ "pressureNormSquaredIsWeightedOccupationSum is Set-valued and does not produce a <=E expansion witness"
        ∷ "activeLaneHamiltonianSum is an opaque ternary Energy operation with no monotonicity law"
        ∷ "The p3/p5/p7 weighted-lane dominance witnesses are not derivable from laneSupport, occupation, disjointness, or Nat lane weights"
        ∷ "The searched Energy/MDL modules expose generic preorder records and a Nat preorder instance, but this package does not identify _<=E_ with either preorder"
        ∷ "Therefore the external lemma interface itself remains unconstructed from existing local definitions"
        ∷ "No spectral gap receipt or promotion is constructed by this absence ledger"
        ∷ []
    }

s8LaneSumDominanceExternalLemmaInterfaceAbsentFromExistingDefinitions :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8LaneSumDominanceExternalLemmaInterfaceAbsenceLedger.externalLemmaInterfaceConstructedFromExistingDefinitions
    (canonicalS8LaneSumDominanceExternalLemmaInterfaceAbsenceLedger
      hypotheses
      decomposition
      occupation
      weighting)
  ≡
  false
s8LaneSumDominanceExternalLemmaInterfaceAbsentFromExistingDefinitions
  hypotheses
  decomposition
  occupation
  weighting =
  refl

s8LaneEnergyOrderCompatibilityFromExternalLemmaInterface :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  ((a b c : Energy hypotheses) →
    _≤E_ hypotheses a b →
    _≤E_ hypotheses b c →
    _≤E_ hypotheses a c) →
  S8LaneSumDominanceExternalLemmaInterface
    hypotheses
    decomposition
    occupation
    weighting →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting
s8LaneEnergyOrderCompatibilityFromExternalLemmaInterface
  hypotheses
  decomposition
  occupation
  weighting
  orderTransitiveWitness
  externalLemmas =
  s8LaneEnergyOrderCompatibilityFromFiniteLaneOrderArithmeticFields
    hypotheses
    decomposition
    occupation
    weighting
    orderTransitiveWitness
    (S8LaneSumDominanceExternalLemmaInterface.p3WeightedLanePressureDominatedByLaneHamiltonian
      externalLemmas)
    (S8LaneSumDominanceExternalLemmaInterface.p5WeightedLanePressureDominatedByLaneHamiltonian
      externalLemmas)
    (S8LaneSumDominanceExternalLemmaInterface.p7WeightedLanePressureDominatedByLaneHamiltonian
      externalLemmas)
    (S8LaneSumDominanceExternalLemmaInterface.pressureNormWeightedLaneSumExpansion
      externalLemmas)
    (S8LaneSumDominanceExternalLemmaInterface.threeLaneWeightedPressureSumMonotonicity
      externalLemmas)
    (S8LaneSumDominanceExternalLemmaInterface.hamiltonianActiveLaneSumTransport
      externalLemmas)

s8LaneEnergyOrderCompatibilityFromUserSuppliedEnergy≃NatAndExternalSixWitnesses :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8UserSuppliedEnergy≃Nat hypotheses →
  S8LaneSumDominanceExternalLemmaInterface
    hypotheses
    decomposition
    occupation
    weighting →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting
s8LaneEnergyOrderCompatibilityFromUserSuppliedEnergy≃NatAndExternalSixWitnesses
  hypotheses
  decomposition
  occupation
  weighting
  energy≃Nat
  externalLemmas =
  s8LaneEnergyOrderCompatibilityFromExternalLemmaInterface
    hypotheses
    decomposition
    occupation
    weighting
    (s8EnergyToNatBridgeGivesEnergyOrderTransitive
      hypotheses
      (s8EnergyToNatOrderBridgeFromUserSuppliedEnergy≃Nat
        hypotheses
        energy≃Nat))
    externalLemmas

data S8LaneEnergyOrderCompatibilityOpaqueBlockingField : Set where
  s8OpaqueEnergyOrderTransitivityField :
    S8LaneEnergyOrderCompatibilityOpaqueBlockingField

  s8OpaqueP3WeightedPressureDominanceField :
    S8LaneEnergyOrderCompatibilityOpaqueBlockingField

  s8OpaqueP5WeightedPressureDominanceField :
    S8LaneEnergyOrderCompatibilityOpaqueBlockingField

  s8OpaqueP7WeightedPressureDominanceField :
    S8LaneEnergyOrderCompatibilityOpaqueBlockingField

  s8OpaquePressureNormWeightedLaneSumExpansionField :
    S8LaneEnergyOrderCompatibilityOpaqueBlockingField

  s8OpaqueThreeLaneWeightedPressureSumMonotonicityField :
    S8LaneEnergyOrderCompatibilityOpaqueBlockingField

  s8OpaqueHamiltonianActiveLaneSumTransportField :
    S8LaneEnergyOrderCompatibilityOpaqueBlockingField

canonicalS8LaneEnergyOrderCompatibilityOpaqueBlockingFields :
  List S8LaneEnergyOrderCompatibilityOpaqueBlockingField
canonicalS8LaneEnergyOrderCompatibilityOpaqueBlockingFields =
  s8OpaqueEnergyOrderTransitivityField
  ∷ s8OpaqueP3WeightedPressureDominanceField
  ∷ s8OpaqueP5WeightedPressureDominanceField
  ∷ s8OpaqueP7WeightedPressureDominanceField
  ∷ s8OpaquePressureNormWeightedLaneSumExpansionField
  ∷ s8OpaqueThreeLaneWeightedPressureSumMonotonicityField
  ∷ s8OpaqueHamiltonianActiveLaneSumTransportField
  ∷ []

record S8LaneEnergyOrderCompatibilityIrreducibilityReport
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses)
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition)
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation)
  : Setω where
  field
    targetPrimitiveTypeName :
      String

    targetPrimitiveTypeDescription :
      String

    exactOpaqueBlockingFields :
      List S8LaneEnergyOrderCompatibilityOpaqueBlockingField

    exactOpaqueBlockingFieldsAreCanonical :
      exactOpaqueBlockingFields
      ≡
      canonicalS8LaneEnergyOrderCompatibilityOpaqueBlockingFields

    firstOpaqueBlockingField :
      S8LaneEnergyOrderCompatibilityOpaqueBlockingField

    firstOpaqueBlockingFieldIsEnergyOrderTransitivity :
      firstOpaqueBlockingField
      ≡
      s8OpaqueEnergyOrderTransitivityField

    opaqueEnergyOrderType :
      String

    opaqueWeightedLaneDominanceTypes :
      String

    opaquePressureNormExpansionType :
      String

    opaqueThreeLaneMonotonicityType :
      String

    opaqueHamiltonianTransportType :
      String

    constructedFromExistingDefinitions :
      Bool

    constructedFromExistingDefinitionsIsFalse :
      constructedFromExistingDefinitions ≡ false

    obstructionBoundary :
      List String

open S8LaneEnergyOrderCompatibilityIrreducibilityReport public

canonicalS8LaneEnergyOrderCompatibilityIrreducibilityReport :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8LaneEnergyOrderCompatibilityIrreducibilityReport
    hypotheses
    decomposition
    occupation
    weighting
canonicalS8LaneEnergyOrderCompatibilityIrreducibilityReport
  hypotheses
  decomposition
  occupation
  weighting =
  record
    { targetPrimitiveTypeName =
        "S8LaneEnergyOrderCompatibility"
    ; targetPrimitiveTypeDescription =
        "The finite three-lane weighted-pressure/order/arithmetic compatibility package"
    ; exactOpaqueBlockingFields =
        canonicalS8LaneEnergyOrderCompatibilityOpaqueBlockingFields
    ; exactOpaqueBlockingFieldsAreCanonical =
        refl
    ; firstOpaqueBlockingField =
        s8OpaqueEnergyOrderTransitivityField
    ; firstOpaqueBlockingFieldIsEnergyOrderTransitivity =
        refl
    ; opaqueEnergyOrderType =
        "_<=E_ hypotheses a b is an arbitrary package field with no transitivity, reflexivity, or equality-transport constructor exposed by PressureToSpectralGapHypothesisPackage"
    ; opaqueWeightedLaneDominanceTypes =
        "For p3/p5/p7: weightedLanePressureEnergy lane psi <=E laneHamiltonianEnergy lane psi is not derivable from laneSupport, occupation, or weighting surfaces"
    ; opaquePressureNormExpansionType =
        "pressureNormSquaredIsWeightedOccupationSum is only a Set-valued surface; it does not produce pressureNormSquared psi <=E activeLaneHamiltonianSum weighted-p3 weighted-p5 weighted-p7"
    ; opaqueThreeLaneMonotonicityType =
        "activeLaneHamiltonianSum is an arbitrary ternary Energy operation with no monotonicity field"
    ; opaqueHamiltonianTransportType =
        "hamiltonianEnergyIsActiveLaneSum is an equality in the opposite definitional direction for <=E transport unless order reflexivity/equality transport is supplied"
    ; constructedFromExistingDefinitions =
        false
    ; constructedFromExistingDefinitionsIsFalse =
        refl
    ; obstructionBoundary =
        "The named constructor s8LaneEnergyOrderCompatibilityFromFiniteLaneOrderArithmeticFields inhabits the compatibility only after the exact six order/arithmetic witnesses are supplied"
        ∷ "The inspected local definitions expose symbols for the energies and sums but no constructors for the required <=E proofs"
        ∷ "The exact opaque blockers are the package field _<=E_, the per-lane weighted-pressure inequalities, pressure-norm weighted-sum expansion, ternary sum monotonicity, and active-lane Hamiltonian transport"
        ∷ "The pressure-energy compiler remains available from compatibility, but the compatibility itself is irreducible from the present surfaces"
        ∷ []
    }

record S8LaneEnergyOrderCompatibilityPrimitiveRequest
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses)
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition)
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation)
  : Setω where
  field
    compatibilityTarget :
      String

    exactMissingPrimitives :
      List S8LaneEnergyOrderCompatibilityMissingPrimitive

    exactMissingPrimitivesAreCanonical :
      exactMissingPrimitives
      ≡
      canonicalS8LaneEnergyOrderCompatibilityMissingPrimitives

    firstMissingPrimitive :
      S8LaneEnergyOrderCompatibilityMissingPrimitive

    firstMissingPrimitiveIsWeightedPressureFiniteLaneOrderArithmetic :
      firstMissingPrimitive
      ≡
      s8WeightedPressureFiniteLaneOrderArithmeticCompatibilityPrimitive

    requestedPrimitiveName :
      String

    requestedPrimitiveTypeDescription :
      String

    compatibilityPrimitiveFound :
      Bool

    compatibilityPrimitiveFoundIsFalse :
      compatibilityPrimitiveFound ≡ false

    gapReceiptConstructed :
      Bool

    gapReceiptConstructedIsFalse :
      gapReceiptConstructed ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    irreducibilityReport :
      S8LaneEnergyOrderCompatibilityIrreducibilityReport
        hypotheses
        decomposition
        occupation
        weighting

    compatibilityBoundary :
      List String

open S8LaneEnergyOrderCompatibilityPrimitiveRequest public

canonicalS8LaneEnergyOrderCompatibilityPrimitiveRequest :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8LaneEnergyOrderCompatibilityPrimitiveRequest
    hypotheses
    decomposition
    occupation
    weighting
canonicalS8LaneEnergyOrderCompatibilityPrimitiveRequest
  hypotheses
  decomposition
  occupation
  weighting =
  record
    { compatibilityTarget =
        "S8LaneEnergyOrderCompatibility hypotheses decomposition occupation weighting"
    ; exactMissingPrimitives =
        canonicalS8LaneEnergyOrderCompatibilityMissingPrimitives
    ; exactMissingPrimitivesAreCanonical =
        refl
    ; firstMissingPrimitive =
        s8WeightedPressureFiniteLaneOrderArithmeticCompatibilityPrimitive
    ; firstMissingPrimitiveIsWeightedPressureFiniteLaneOrderArithmetic =
        refl
    ; requestedPrimitiveName =
        "s8WeightedPressureFiniteLaneOrderArithmeticCompatibilityPrimitive"
    ; requestedPrimitiveTypeDescription =
        "An inhabitant of S8LaneEnergyOrderCompatibility: transitivity of <=E, each weighted-lane pressure <=E its lane Hamiltonian, pressureNormSquared <=E the weighted three-lane pressure sum, monotonicity of activeLaneHamiltonianSum in all three lanes, and transport from the active lane Hamiltonian sum to hamiltonianEnergy"
    ; compatibilityPrimitiveFound =
        false
    ; compatibilityPrimitiveFoundIsFalse =
        refl
    ; gapReceiptConstructed =
        false
    ; gapReceiptConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; irreducibilityReport =
        canonicalS8LaneEnergyOrderCompatibilityIrreducibilityReport
          hypotheses
          decomposition
          occupation
          weighting
    ; compatibilityBoundary =
        "The file exposes the relevant lane-energy symbols but not the order/arithmetic laws needed to inhabit them"
        ∷ "The exact fail-closed primitive is the finite three-lane weighted-pressure/order compatibility package"
        ∷ "The irreducibility report records the exact opaque fields/types preventing construction from existing definitions"
        ∷ "Supplying that package lets the lane-sum compiler construct pressureNormSquared psi <=E hamiltonianEnergy psi"
        ∷ "No spectral gap receipt or promotion is constructed by this compatibility request"
        ∷ []
    }

s8WeightedPressureFiniteLaneOrderArithmeticCompatibilityAbsentFromExistingDefinitions :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8LaneEnergyOrderCompatibilityIrreducibilityReport.constructedFromExistingDefinitions
    (S8LaneEnergyOrderCompatibilityPrimitiveRequest.irreducibilityReport
      (canonicalS8LaneEnergyOrderCompatibilityPrimitiveRequest
        hypotheses
        decomposition
        occupation
        weighting))
  ≡
  false
s8WeightedPressureFiniteLaneOrderArithmeticCompatibilityAbsentFromExistingDefinitions
  hypotheses
  decomposition
  occupation
  weighting =
  refl

s8LaneEnergyOrderCompatibilityFromPrimitiveRequest :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8LaneEnergyOrderCompatibilityPrimitiveRequest
    hypotheses
    decomposition
    occupation
    weighting →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting
s8LaneEnergyOrderCompatibilityFromPrimitiveRequest
  hypotheses
  decomposition
  occupation
  weighting
  compatibilityRequest
  compatibility =
  compatibility

s8LaneSumDominanceCompilerFromOrderCompatibility :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting →
  (ψ : State hypotheses) →
  nonVacuum hypotheses ψ →
  orthogonalToVacuum hypotheses ψ →
  _≤E_ hypotheses
    (S8PressureNormSquaredLaneWeightSurface.pressureNorm² weighting ψ)
    (hamiltonianEnergy hypotheses ψ)
s8LaneSumDominanceCompilerFromOrderCompatibility
  hypotheses
  decomposition
  occupation
  weighting
  compatibility
  ψ
  ψNonVacuum
  ψOrthogonal =
  S8LaneEnergyOrderCompatibility.s8LaneOrderTransitive compatibility
    (S8PressureNormSquaredLaneWeightSurface.pressureNorm² weighting ψ)
    (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
      decomposition
      (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
        weighting
        s8-p3-lane
        ψ)
      (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
        weighting
        s8-p5-lane
        ψ)
      (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
        weighting
        s8-p7-lane
        ψ))
    (hamiltonianEnergy hypotheses ψ)
    (S8LaneEnergyOrderCompatibility.pressureNormWeightedLaneSumExpansion
      compatibility
      ψ)
    (S8LaneEnergyOrderCompatibility.s8LaneOrderTransitive compatibility
      (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
        decomposition
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p3-lane
          ψ)
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p5-lane
          ψ)
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p7-lane
          ψ))
      (YangMillsHamiltonianLaneDecomposition.activeLaneHamiltonianSum
        decomposition
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p3-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p5-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p7-lane
          ψ))
      (hamiltonianEnergy hypotheses ψ)
      (S8LaneEnergyOrderCompatibility.threeLaneWeightedPressureSumMonotonicity
        compatibility
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p3-lane
          ψ)
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p5-lane
          ψ)
        (S8PressureNormSquaredLaneWeightSurface.weightedLanePressureEnergy
          weighting
          s8-p7-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p3-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p5-lane
          ψ)
        (YangMillsHamiltonianLaneDecomposition.laneHamiltonianEnergy
          decomposition
          s8-p7-lane
          ψ)
        (S8LaneEnergyOrderCompatibility.p3WeightedLanePressureDominatedByLaneHamiltonian
          compatibility
          ψ
          ψNonVacuum
          ψOrthogonal)
        (S8LaneEnergyOrderCompatibility.p5WeightedLanePressureDominatedByLaneHamiltonian
          compatibility
          ψ
          ψNonVacuum
          ψOrthogonal)
        (S8LaneEnergyOrderCompatibility.p7WeightedLanePressureDominatedByLaneHamiltonian
          compatibility
          ψ
          ψNonVacuum
          ψOrthogonal))
      (S8LaneEnergyOrderCompatibility.hamiltonianActiveLaneSumTransport
        compatibility
        ψ))

s8LaneSumDominanceCompilerFromCompatibilityPrimitiveRequest :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8LaneEnergyOrderCompatibilityPrimitiveRequest
    hypotheses
    decomposition
    occupation
    weighting →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting →
  (ψ : State hypotheses) →
  nonVacuum hypotheses ψ →
  orthogonalToVacuum hypotheses ψ →
  _≤E_ hypotheses
    (S8PressureNormSquaredLaneWeightSurface.pressureNorm² weighting ψ)
    (hamiltonianEnergy hypotheses ψ)
s8LaneSumDominanceCompilerFromCompatibilityPrimitiveRequest
  hypotheses
  decomposition
  occupation
  weighting
  compatibilityRequest
  compatibility =
  s8LaneSumDominanceCompilerFromOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting
    (s8LaneEnergyOrderCompatibilityFromPrimitiveRequest
      hypotheses
      decomposition
      occupation
      weighting
      compatibilityRequest
      compatibility)

s8FinalInternalLaneDominanceCompilerFromExternalLemmaInterface :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  ((a b c : Energy hypotheses) →
    _≤E_ hypotheses a b →
    _≤E_ hypotheses b c →
    _≤E_ hypotheses a c) →
  S8LaneSumDominanceExternalLemmaInterface
    hypotheses
    decomposition
    occupation
    weighting →
  (ψ : State hypotheses) →
  nonVacuum hypotheses ψ →
  orthogonalToVacuum hypotheses ψ →
  _≤E_ hypotheses
    (S8PressureNormSquaredLaneWeightSurface.pressureNorm² weighting ψ)
    (hamiltonianEnergy hypotheses ψ)
s8FinalInternalLaneDominanceCompilerFromExternalLemmaInterface
  hypotheses
  decomposition
  occupation
  weighting
  orderTransitiveWitness
  externalLemmas =
  s8LaneSumDominanceCompilerFromOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting
    (s8LaneEnergyOrderCompatibilityFromExternalLemmaInterface
      hypotheses
      decomposition
      occupation
      weighting
      orderTransitiveWitness
      externalLemmas)

s8ExternalLemmaInterfaceUsesFinalInternalCompiler :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  (orderTransitiveWitness :
    (a b c : Energy hypotheses) →
    _≤E_ hypotheses a b →
    _≤E_ hypotheses b c →
    _≤E_ hypotheses a c) →
  (externalLemmas :
    S8LaneSumDominanceExternalLemmaInterface
      hypotheses
      decomposition
      occupation
      weighting) →
  s8FinalInternalLaneDominanceCompilerFromExternalLemmaInterface
    hypotheses
    decomposition
    occupation
    weighting
    orderTransitiveWitness
    externalLemmas
  ≡
  s8LaneSumDominanceCompilerFromOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting
    (s8LaneEnergyOrderCompatibilityFromExternalLemmaInterface
      hypotheses
      decomposition
      occupation
      weighting
      orderTransitiveWitness
      externalLemmas)
s8ExternalLemmaInterfaceUsesFinalInternalCompiler
  hypotheses
  decomposition
  occupation
  weighting
  orderTransitiveWitness
  externalLemmas =
  refl

s8PressureEnergyCoercivityPrimitiveFromLaneEnergyOrderCompatibility :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting →
  ((ψ : State hypotheses) →
    nonVacuum hypotheses ψ →
    orthogonalToVacuum hypotheses ψ →
    _≤E_ hypotheses
      (gapUnit hypotheses)
      (S8PressureNormSquaredLaneWeightSurface.pressureNorm²
        weighting
        ψ)) →
  S8PressureEnergyCoercivityPrimitiveInterface hypotheses
s8PressureEnergyCoercivityPrimitiveFromLaneEnergyOrderCompatibility
  hypotheses
  decomposition
  occupation
  weighting
  compatibility
  gapUnitDominatedByPressureNormWitness =
  record
    { pressureNorm² =
        S8PressureNormSquaredLaneWeightSurface.pressureNorm² weighting
    ; pressureOrderTransitive =
        S8LaneEnergyOrderCompatibility.s8LaneOrderTransitive compatibility
    ; gapUnitDominatedByPressureNorm =
        gapUnitDominatedByPressureNormWitness
    ; laneHamiltonianDominatesPressureNorm =
        s8LaneSumDominanceCompilerFromOrderCompatibility
          hypotheses
          decomposition
          occupation
          weighting
          compatibility
    }

s8PressureEnergyCoercivityPrimitiveFromCompatibilityPrimitiveRequest :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8LaneEnergyOrderCompatibilityPrimitiveRequest
    hypotheses
    decomposition
    occupation
    weighting →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting →
  ((ψ : State hypotheses) →
    nonVacuum hypotheses ψ →
    orthogonalToVacuum hypotheses ψ →
    _≤E_ hypotheses
      (gapUnit hypotheses)
      (S8PressureNormSquaredLaneWeightSurface.pressureNorm²
        weighting
        ψ)) →
  S8PressureEnergyCoercivityPrimitiveInterface hypotheses
s8PressureEnergyCoercivityPrimitiveFromCompatibilityPrimitiveRequest
  hypotheses
  decomposition
  occupation
  weighting
  compatibilityRequest
  compatibility =
  s8PressureEnergyCoercivityPrimitiveFromLaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting
    (s8LaneEnergyOrderCompatibilityFromPrimitiveRequest
      hypotheses
      decomposition
      occupation
      weighting
      compatibilityRequest
      compatibility)

record S8LaneHamiltonianDominanceInterface
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    Lane :
      Set

    pressureNorm² :
      State hypotheses →
      Energy hypotheses

    yangMillsHamiltonianLaneDecomposition :
      YangMillsHamiltonianLaneDecomposition hypotheses

    laneOccupationNumberDefinition :
      S8LaneOccupationNumberSurface
        hypotheses
        yangMillsHamiltonianLaneDecomposition

    pressureNormSquaredLaneWeightDefinition :
      S8PressureNormSquaredLaneWeightSurface
        hypotheses
        laneOccupationNumberDefinition

    pressureNorm²MatchesLaneWeightDefinition :
      pressureNorm²
      ≡
      S8PressureNormSquaredLaneWeightSurface.pressureNorm²
        pressureNormSquaredLaneWeightDefinition

    minimumNontrivialHolonomyDistanceDefinition :
      S8MinimumNontrivialHolonomyDistanceSurface

    minimumNontrivialHolonomyDistanceDefinitionMatchesWeighting :
      Set

    laneEnergyOrderCompatibility :
      S8LaneEnergyOrderCompatibility
        hypotheses
        yangMillsHamiltonianLaneDecomposition
        laneOccupationNumberDefinition
        pressureNormSquaredLaneWeightDefinition

    laneHamiltonianDominatesPressureNorm :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      _≤E_ hypotheses
        (pressureNorm² ψ)
        (hamiltonianEnergy hypotheses ψ)

open S8LaneHamiltonianDominanceInterface public

record S8ConcreteLaneHamiltonianDominanceDefinition
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    yangMillsHamiltonianLaneDecomposition :
      YangMillsHamiltonianLaneDecomposition hypotheses

    laneOccupationNumberSurface :
      S8LaneOccupationNumberSurface
        hypotheses
        yangMillsHamiltonianLaneDecomposition

    pressureNormSquaredLaneWeightSurface :
      S8PressureNormSquaredLaneWeightSurface
        hypotheses
        laneOccupationNumberSurface

    minimumNontrivialHolonomyDistanceSurface :
      S8MinimumNontrivialHolonomyDistanceSurface

    minimumNontrivialHolonomyDistanceSurfaceMatchesWeighting :
      Set

    laneEnergyOrderCompatibility :
      S8LaneEnergyOrderCompatibility
        hypotheses
        yangMillsHamiltonianLaneDecomposition
        laneOccupationNumberSurface
        pressureNormSquaredLaneWeightSurface

    laneSumDominanceToGlobalDominanceCompiler :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      _≤E_ hypotheses
        (S8PressureNormSquaredLaneWeightSurface.pressureNorm²
          pressureNormSquaredLaneWeightSurface
          ψ)
        (hamiltonianEnergy hypotheses ψ)

open S8ConcreteLaneHamiltonianDominanceDefinition public

s8ConcreteLaneHamiltonianDominanceDefinitionFromCompatibility :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8MinimumNontrivialHolonomyDistanceSurface →
  Set →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting →
  S8ConcreteLaneHamiltonianDominanceDefinition hypotheses
s8ConcreteLaneHamiltonianDominanceDefinitionFromCompatibility
  hypotheses
  decomposition
  occupation
  weighting
  holonomyDistance
  holonomyDistanceMatchesWeighting
  compatibility =
  record
    { yangMillsHamiltonianLaneDecomposition =
        decomposition
    ; laneOccupationNumberSurface =
        occupation
    ; pressureNormSquaredLaneWeightSurface =
        weighting
    ; minimumNontrivialHolonomyDistanceSurface =
        holonomyDistance
    ; minimumNontrivialHolonomyDistanceSurfaceMatchesWeighting =
        holonomyDistanceMatchesWeighting
    ; laneEnergyOrderCompatibility =
        compatibility
    ; laneSumDominanceToGlobalDominanceCompiler =
        s8LaneSumDominanceCompilerFromOrderCompatibility
          hypotheses
          decomposition
          occupation
          weighting
          compatibility
    }

s8ConcreteLaneHamiltonianDominanceDefinitionFromCarrierNaturalUnitConvention :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  (bridge : S8EnergyToNatOrderBridge hypotheses) →
  S8CarrierNaturalLaneEnergyUnitConvention
    hypotheses
    decomposition
    occupation
    weighting
    bridge →
  S8ConcreteLaneHamiltonianDominanceDefinition hypotheses
s8ConcreteLaneHamiltonianDominanceDefinitionFromCarrierNaturalUnitConvention
  hypotheses
  decomposition
  occupation
  weighting
  bridge
  convention =
  s8ConcreteLaneHamiltonianDominanceDefinitionFromCompatibility
    hypotheses
    decomposition
    occupation
    weighting
    (S8PressureNormSquaredLaneWeightSurface.holonomyDistanceSurface weighting)
    (S8MinimumNontrivialHolonomyDistanceSurface.minimumNontrivialHolonomyDistance
      (S8PressureNormSquaredLaneWeightSurface.holonomyDistanceSurface weighting)
      ≡
      S8MinimumNontrivialHolonomyDistanceSurface.minimumNontrivialHolonomyDistance
        (S8PressureNormSquaredLaneWeightSurface.holonomyDistanceSurface weighting))
    (s8LaneEnergyOrderCompatibilityFromCarrierNaturalUnitConvention
      hypotheses
      decomposition
      occupation
      weighting
      bridge
      convention)

s8LaneHamiltonianDominanceInterfaceFromConcreteDefinition :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8ConcreteLaneHamiltonianDominanceDefinition hypotheses →
  S8LaneHamiltonianDominanceInterface hypotheses
s8LaneHamiltonianDominanceInterfaceFromConcreteDefinition
  hypotheses
  concreteDefinition =
  record
    { Lane =
        S8ActiveYangMillsLane
    ; pressureNorm² =
        S8PressureNormSquaredLaneWeightSurface.pressureNorm²
          (S8ConcreteLaneHamiltonianDominanceDefinition.pressureNormSquaredLaneWeightSurface
            concreteDefinition)
    ; yangMillsHamiltonianLaneDecomposition =
        S8ConcreteLaneHamiltonianDominanceDefinition.yangMillsHamiltonianLaneDecomposition
          concreteDefinition
    ; laneOccupationNumberDefinition =
        S8ConcreteLaneHamiltonianDominanceDefinition.laneOccupationNumberSurface
          concreteDefinition
    ; pressureNormSquaredLaneWeightDefinition =
        S8ConcreteLaneHamiltonianDominanceDefinition.pressureNormSquaredLaneWeightSurface
          concreteDefinition
    ; pressureNorm²MatchesLaneWeightDefinition =
        refl
    ; minimumNontrivialHolonomyDistanceDefinition =
        S8ConcreteLaneHamiltonianDominanceDefinition.minimumNontrivialHolonomyDistanceSurface
          concreteDefinition
    ; minimumNontrivialHolonomyDistanceDefinitionMatchesWeighting =
        S8ConcreteLaneHamiltonianDominanceDefinition.minimumNontrivialHolonomyDistanceSurfaceMatchesWeighting
          concreteDefinition
    ; laneEnergyOrderCompatibility =
        S8ConcreteLaneHamiltonianDominanceDefinition.laneEnergyOrderCompatibility
          concreteDefinition
    ; laneHamiltonianDominatesPressureNorm =
        S8ConcreteLaneHamiltonianDominanceDefinition.laneSumDominanceToGlobalDominanceCompiler
          concreteDefinition
    }

s8PrimitiveInterfaceFromLaneHamiltonianDominance :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (laneDominance : S8LaneHamiltonianDominanceInterface hypotheses) →
  ((a b c : Energy hypotheses) →
    _≤E_ hypotheses a b →
    _≤E_ hypotheses b c →
    _≤E_ hypotheses a c) →
  ((ψ : State hypotheses) →
    nonVacuum hypotheses ψ →
    orthogonalToVacuum hypotheses ψ →
    _≤E_ hypotheses
      (gapUnit hypotheses)
      (S8LaneHamiltonianDominanceInterface.pressureNorm²
        laneDominance
        ψ)) →
  S8PressureEnergyCoercivityPrimitiveInterface hypotheses
s8PrimitiveInterfaceFromLaneHamiltonianDominance
  hypotheses
  laneDominance
  pressureOrderTransitiveWitness
  gapUnitDominatedByPressureNormWitness =
  record
    { pressureNorm² =
        S8LaneHamiltonianDominanceInterface.pressureNorm²
          laneDominance
    ; pressureOrderTransitive =
        pressureOrderTransitiveWitness
    ; gapUnitDominatedByPressureNorm =
        gapUnitDominatedByPressureNormWitness
    ; laneHamiltonianDominatesPressureNorm =
        S8LaneHamiltonianDominanceInterface.laneHamiltonianDominatesPressureNorm
          laneDominance
    }

record S8PressureEnergyCoercivityCompilerInterface
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    primitiveInterface :
      S8PressureEnergyCoercivityPrimitiveInterface hypotheses

    pressureEnergyCoercivityCompiler :
      S8PressureEnergyCoercivityPrimitiveInterface hypotheses →
      pressureEnergyCoercive hypotheses

open S8PressureEnergyCoercivityCompilerInterface public

s8PressureEnergyCoercivityFromCompilerInterface :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8PressureEnergyCoercivityCompilerInterface hypotheses →
  pressureEnergyCoercive hypotheses
s8PressureEnergyCoercivityFromCompilerInterface hypotheses compilerInterface =
  pressureEnergyCoercivityCompiler compilerInterface
    (primitiveInterface compilerInterface)

s8PressureEnergyCoercivityCompilerInterfaceFromFields :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8PressureEnergyCoercivityPrimitiveInterface hypotheses →
  (S8PressureEnergyCoercivityPrimitiveInterface hypotheses →
    pressureEnergyCoercive hypotheses) →
  S8PressureEnergyCoercivityCompilerInterface hypotheses
s8PressureEnergyCoercivityCompilerInterfaceFromFields
  hypotheses
  primitiveInterfaceWitness
  pressureEnergyCoercivityCompilerWitness =
  record
    { primitiveInterface =
        primitiveInterfaceWitness
    ; pressureEnergyCoercivityCompiler =
        pressureEnergyCoercivityCompilerWitness
    }

s8PressureEnergyCoercivityFromPrimitiveAndCompiler :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8PressureEnergyCoercivityPrimitiveInterface hypotheses →
  (S8PressureEnergyCoercivityPrimitiveInterface hypotheses →
    pressureEnergyCoercive hypotheses) →
  pressureEnergyCoercive hypotheses
s8PressureEnergyCoercivityFromPrimitiveAndCompiler
  hypotheses
  primitiveInterfaceWitness
  pressureEnergyCoercivityCompilerWitness =
  s8PressureEnergyCoercivityFromCompilerInterface
    hypotheses
    (s8PressureEnergyCoercivityCompilerInterfaceFromFields
      hypotheses
      primitiveInterfaceWitness
      pressureEnergyCoercivityCompilerWitness)

record S8PressureEnergyCoercivityCompilerAbsenceLedger
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    compilerTargetName :
      String

    exactCompilerMissingFields :
      List S8PressureEnergyCoercivityCompilerMissingField

    exactCompilerMissingFieldsAreCanonical :
      exactCompilerMissingFields
      ≡
      canonicalS8PressureEnergyCoercivityCompilerMissingFields

    firstCompilerMissing :
      S8PressureEnergyCoercivityCompilerMissingField

    firstCompilerMissingIsPrimitiveInterfaceToPackageCompiler :
      firstCompilerMissing
      ≡
      s8PrimitiveInterfaceToPackagePressureEnergyCoerciveCompilerField

    requestedCompilerType :
      String

    primitiveInterfaceConstructibleAfterLaneDominance :
      Bool

    primitiveInterfaceConstructibleAfterLaneDominanceIsFalse :
      primitiveInterfaceConstructibleAfterLaneDominance ≡ false

    packageCoercivityConstructedFromExistingDefinitions :
      Bool

    packageCoercivityConstructedFromExistingDefinitionsIsFalse :
      packageCoercivityConstructedFromExistingDefinitions ≡ false

    gapReceiptConstructed :
      Bool

    gapReceiptConstructedIsFalse :
      gapReceiptConstructed ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    compilerBoundary :
      List String

open S8PressureEnergyCoercivityCompilerAbsenceLedger public

canonicalS8PressureEnergyCoercivityCompilerAbsenceLedger :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8PressureEnergyCoercivityCompilerAbsenceLedger hypotheses
canonicalS8PressureEnergyCoercivityCompilerAbsenceLedger hypotheses =
  record
    { compilerTargetName =
        "pressureEnergyCoercive hypotheses"
    ; exactCompilerMissingFields =
        canonicalS8PressureEnergyCoercivityCompilerMissingFields
    ; exactCompilerMissingFieldsAreCanonical =
        refl
    ; firstCompilerMissing =
        s8PrimitiveInterfaceToPackagePressureEnergyCoerciveCompilerField
    ; firstCompilerMissingIsPrimitiveInterfaceToPackageCompiler =
        refl
    ; requestedCompilerType =
        "S8PressureEnergyCoercivityPrimitiveInterface hypotheses -> pressureEnergyCoercive hypotheses"
    ; primitiveInterfaceConstructibleAfterLaneDominance =
        false
    ; primitiveInterfaceConstructibleAfterLaneDominanceIsFalse =
        refl
    ; packageCoercivityConstructedFromExistingDefinitions =
        false
    ; packageCoercivityConstructedFromExistingDefinitionsIsFalse =
        refl
    ; gapReceiptConstructed =
        false
    ; gapReceiptConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; compilerBoundary =
        "S8PressureEnergyCoercivityPrimitiveInterface is the strongest local primitive surface for gapUnit <=E pressureNormSquared and pressureNormSquared <=E hamiltonianEnergy"
        ∷ "s8PressureEnergyCoercivityFromPrimitiveAndCompiler wires that primitive into pressureEnergyCoercive only after the package-specific compiler is supplied"
        ∷ "The exact missing opaque package field is the compiler from S8PressureEnergyCoercivityPrimitiveInterface hypotheses to pressureEnergyCoercive hypotheses"
        ∷ "No local postulate, mirror package, spectral gap receipt, terminal claim, W3/W4/W5 authority, or continuum Clay mass-gap promotion is constructed here"
        ∷ []
    }

s8LowerBoundTransportFromPressureEnergyCoercivityPrimitive :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8PressureEnergyCoercivityPrimitiveInterface hypotheses →
  S8LowerBoundTransport hypotheses
s8LowerBoundTransportFromPressureEnergyCoercivityPrimitive
  hypotheses
  primitiveInterface
  ψ
  ψNonVacuum
  ψOrthogonal =
  pressureOrderTransitive primitiveInterface
    (gapUnit hypotheses)
    (pressureNorm² primitiveInterface ψ)
    (hamiltonianEnergy hypotheses ψ)
    (gapUnitDominatedByPressureNorm primitiveInterface ψ ψNonVacuum ψOrthogonal)
    (laneHamiltonianDominatesPressureNorm primitiveInterface ψ ψNonVacuum ψOrthogonal)

s8LowerBoundTransportFromHypotheses :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8LowerBoundTransport hypotheses
s8LowerBoundTransportFromHypotheses hypotheses =
  subThresholdLowerBound hypotheses
    14
    15
    Probe.fourteenBelowFifteen

record S8PressureBelow15LocalTheoremFields
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    hamiltonianCarrier :
      Set

    energyCarrier :
      Set

    hamiltonianEnergyMap :
      hamiltonianCarrier →
      energyCarrier

    vacuumState :
      hamiltonianCarrier

    nonVacuumSector :
      hamiltonianCarrier →
      Set

    vacuumOrthogonality :
      hamiltonianCarrier →
      Set

    energyOrder :
      energyCarrier →
      energyCarrier →
      Set

    positiveGapUnit :
      energyCarrier

    positiveGapUnitWitness :
      gapUnitPositive hypotheses

    pressureEnergyCoercivityWitness :
      pressureEnergyCoercive hypotheses

    carrierUnitNormalizationWitness :
      carrierUnitNormalization hypotheses
        14
        15
        Probe.canonicalPressureDeficitIs1

    lowerBoundTransport :
      S8LowerBoundTransport hypotheses

    spectralWitness :
      Set

    spectralWitnessInhabited :
      spectralWitness

record S8PressureBelow15SubobligationSurface
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    verdict :
      S8PressurePackageMechanicalVerdict

    localTheoremFieldsName :
      String

    exactLocalFields :
      List S8PressureBelow15LocalTheoremField

    exactLocalFieldsAreCanonical :
      exactLocalFields
      ≡
      canonicalS8PressureBelow15LocalTheoremFields

    firstLocalMissing :
      S8PressureBelow15LocalTheoremField

    firstLocalMissingIsCoercivityWitness :
      firstLocalMissing
      ≡
      s8PressureEnergyCoercivityWitnessField

    availableLowerBoundTransport :
      S8LowerBoundTransport hypotheses

    wrappedNatSelectionReport :
      S8UserSuppliedEnergy≃NatSelectionReport hypotheses

    pressureEnergyCoercivityObligation :
      Set

    pressureEnergyCoercivityObligationMatchesPackage :
      pressureEnergyCoercivityObligation
      ≡
      pressureEnergyCoercive hypotheses

    carrierUnitNormalizationObligation :
      Set

    carrierUnitNormalizationObligationMatchesPackage :
      carrierUnitNormalizationObligation
      ≡
      carrierUnitNormalization hypotheses
        14
        15
        Probe.canonicalPressureDeficitIs1

    gapReceiptConstructed :
      Bool

    gapReceiptConstructedIsFalse :
      gapReceiptConstructed ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    subobligationBoundary :
      List String

record S8SubThresholdSpectralGapDependency
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    pressureBound :
      Nat

    canonicalDim :
      Nat

    pressureBelow :
      pressureBound < canonicalDim

    pressureNotSaturatedAt15 :
      ¬ (pressureBound ≡ canonicalDim)

    pressureDeficitIsCarrierUnit :
      canonicalDim ∸ pressureBound ≡ 1

    pressureEnergyCoerciveDependency :
      pressureEnergyCoercive hypotheses

    carrierUnitNormalizationDependency :
      carrierUnitNormalization hypotheses
        pressureBound
        canonicalDim
        pressureDeficitIsCarrierUnit

    subThresholdLowerBoundDependency :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      _≤E_ hypotheses
        (gapUnit hypotheses)
        (hamiltonianEnergy hypotheses ψ)

s8SubThresholdDependencyFromLocalWitnesses :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  pressureEnergyCoercive hypotheses →
  carrierUnitNormalization hypotheses
    14
    15
    Probe.canonicalPressureDeficitIs1 →
  S8SubThresholdSpectralGapDependency hypotheses
s8SubThresholdDependencyFromLocalWitnesses
  hypotheses
  pressureEnergyCoercivityWitness
  carrierUnitNormalizationWitness =
  record
    { pressureBound =
        14
    ; canonicalDim =
        15
    ; pressureBelow =
        Probe.fourteenBelowFifteen
    ; pressureNotSaturatedAt15 =
        Probe.canonicalPressureNotSaturatedAt15
    ; pressureDeficitIsCarrierUnit =
        Probe.canonicalPressureDeficitIs1
    ; pressureEnergyCoerciveDependency =
        pressureEnergyCoercivityWitness
    ; carrierUnitNormalizationDependency =
        carrierUnitNormalizationWitness
    ; subThresholdLowerBoundDependency =
        s8LowerBoundTransportFromHypotheses hypotheses
    }

s8SubThresholdDependencyFromPrimitiveCompilerAndNormalization :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8PressureEnergyCoercivityPrimitiveInterface hypotheses →
  (S8PressureEnergyCoercivityPrimitiveInterface hypotheses →
    pressureEnergyCoercive hypotheses) →
  carrierUnitNormalization hypotheses
    14
    15
    Probe.canonicalPressureDeficitIs1 →
  S8SubThresholdSpectralGapDependency hypotheses
s8SubThresholdDependencyFromPrimitiveCompilerAndNormalization
  hypotheses
  primitiveInterfaceWitness
  pressureEnergyCoercivityCompilerWitness
  carrierUnitNormalizationWitness =
  s8SubThresholdDependencyFromLocalWitnesses
    hypotheses
    (s8PressureEnergyCoercivityFromPrimitiveAndCompiler
      hypotheses
      primitiveInterfaceWitness
      pressureEnergyCoercivityCompilerWitness)
    carrierUnitNormalizationWitness

s8SubThresholdDependencyFromCompilerInterfaceAndNormalization :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8PressureEnergyCoercivityCompilerInterface hypotheses →
  carrierUnitNormalization hypotheses
    14
    15
    Probe.canonicalPressureDeficitIs1 →
  S8SubThresholdSpectralGapDependency hypotheses
s8SubThresholdDependencyFromCompilerInterfaceAndNormalization
  hypotheses
  compilerInterface
  carrierUnitNormalizationWitness =
  s8SubThresholdDependencyFromLocalWitnesses
    hypotheses
    (s8PressureEnergyCoercivityFromCompilerInterface
      hypotheses
      compilerInterface)
    carrierUnitNormalizationWitness

canonicalS8SubobligationSurface :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  S8PressureBelow15SubobligationSurface hypotheses
canonicalS8SubobligationSurface hypotheses =
  record
    { verdict =
        packageDoesNotMechanicallyYieldGapReceipt
    ; localTheoremFieldsName =
        "S8PressureBelow15LocalTheoremFields"
    ; exactLocalFields =
        canonicalS8PressureBelow15LocalTheoremFields
    ; exactLocalFieldsAreCanonical =
        refl
    ; firstLocalMissing =
        s8PressureEnergyCoercivityWitnessField
    ; firstLocalMissingIsCoercivityWitness =
        refl
    ; availableLowerBoundTransport =
        s8LowerBoundTransportFromHypotheses hypotheses
    ; wrappedNatSelectionReport =
        canonicalS8UserSuppliedEnergy≃NatSelectionReport hypotheses
    ; pressureEnergyCoercivityObligation =
        pressureEnergyCoercive hypotheses
    ; pressureEnergyCoercivityObligationMatchesPackage =
        refl
    ; carrierUnitNormalizationObligation =
        carrierUnitNormalization hypotheses
          14
          15
          Probe.canonicalPressureDeficitIs1
    ; carrierUnitNormalizationObligationMatchesPackage =
        refl
    ; gapReceiptConstructed =
        false
    ; gapReceiptConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; subobligationBoundary =
        "PressureToSpectralGapHypothesisPackage mechanically yields only lower-bound transport for non-vacuum states orthogonal to the vacuum"
        ∷ "It does not inhabit pressureEnergyCoercive, carrierUnitNormalization, gapUnitPositive, or a Yang-Mills spectral witness"
        ∷ "No concrete wrapped-Nat energy package is selected from current hypotheses; S8UserSuppliedEnergy≃Nat is the narrow user-supplied adapter surface"
        ∷ "The first local missing field below S8 is pressureEnergyCoercivityWitness"
        ∷ "s8SubThresholdDependencyFromLocalWitnesses constructs only the S8 dependency after explicit coercivity and normalization witnesses are supplied"
        ∷ "No PressureBelow15SpectralGapReceipt or spectral-gap promotion is constructed by this subobligation surface"
        ∷ []
    }

record S8LaneSumDominanceCompilerRequest : Set where
  field
    compilerTarget :
      String

    exactCompilerMissingFields :
      List S8LaneSumDominanceCompilerMissingField

    exactCompilerMissingFieldsAreCanonical :
      exactCompilerMissingFields
      ≡
      canonicalS8LaneSumDominanceCompilerMissingFields

    firstCompilerMissing :
      S8LaneSumDominanceCompilerMissingField

    firstCompilerMissingIsP3WeightedLanePressureDominance :
      firstCompilerMissing
      ≡
      s8P3WeightedLanePressureDominatedByLaneHamiltonianField

    requestedPerLaneInequalityDirection :
      String

    requestedFiniteThreeLaneMonotonicityEvidence :
      String

    requestedPressureNormWeightedLaneSumExpansion :
      String

    requestedHamiltonianActiveLaneSumTransport :
      String

    compilerFound :
      Bool

    compilerFoundIsFalse :
      compilerFound ≡ false

    gapReceiptConstructed :
      Bool

    gapReceiptConstructedIsFalse :
      gapReceiptConstructed ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    compilerBoundary :
      List String

canonicalS8LaneSumDominanceCompilerRequest :
  S8LaneSumDominanceCompilerRequest
canonicalS8LaneSumDominanceCompilerRequest =
  record
    { compilerTarget =
        "pressureNormSquared psi <=E hamiltonianEnergy psi"
    ; exactCompilerMissingFields =
        canonicalS8LaneSumDominanceCompilerMissingFields
    ; exactCompilerMissingFieldsAreCanonical =
        refl
    ; firstCompilerMissing =
        s8P3WeightedLanePressureDominatedByLaneHamiltonianField
    ; firstCompilerMissingIsP3WeightedLanePressureDominance =
        refl
    ; requestedPerLaneInequalityDirection =
        "For each active lane l in p3/p5/p7: weightedLanePressureEnergy l psi <=E laneHamiltonianEnergy l psi"
    ; requestedFiniteThreeLaneMonotonicityEvidence =
        "If a3 <=E b3, a5 <=E b5, and a7 <=E b7, then activeLaneHamiltonianSum a3 a5 a7 <=E activeLaneHamiltonianSum b3 b5 b7"
    ; requestedPressureNormWeightedLaneSumExpansion =
        "pressureNormSquared psi is the three-lane weighted pressure sum over p3, p5, and p7"
    ; requestedHamiltonianActiveLaneSumTransport =
        "Transport the monotone three-lane Hamiltonian sum along hamiltonianEnergyIsActiveLaneSum psi"
    ; compilerFound =
        false
    ; compilerFoundIsFalse =
        refl
    ; gapReceiptConstructed =
        false
    ; gapReceiptConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; compilerBoundary =
        "The present surfaces expose weightedLanePressureEnergy, pressureNormSquared, laneHamiltonianEnergy, activeLaneHamiltonianSum, and hamiltonianEnergyIsActiveLaneSum"
        ∷ "S8LaneEnergyOrderCompatibility is now the typed destructible field package for the requested per-lane inequalities, finite three-lane monotonicity, pressure-norm weighted-sum expansion, and Hamiltonian active-lane-sum transport"
        ∷ "s8LaneSumDominanceCompilerFromOrderCompatibility constructs the requested compiler once that typed compatibility package is supplied"
        ∷ "No canonical inhabitant of S8LaneEnergyOrderCompatibility is constructed here; the remaining algebra/order law is exactly that typed finite-sum compatibility package"
        ∷ "No spectral gap receipt or promotion is constructed by this compiler request"
        ∷ []
    }

s8LaneSumDominanceCompilerFromRequestAndTypedFields :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8LaneSumDominanceCompilerRequest →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting →
  (ψ : State hypotheses) →
  nonVacuum hypotheses ψ →
  orthogonalToVacuum hypotheses ψ →
  _≤E_ hypotheses
    (S8PressureNormSquaredLaneWeightSurface.pressureNorm² weighting ψ)
    (hamiltonianEnergy hypotheses ψ)
s8LaneSumDominanceCompilerFromRequestAndTypedFields
  hypotheses
  decomposition
  occupation
  weighting
  compilerRequest
  compatibility =
  s8LaneSumDominanceCompilerFromOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting
    compatibility

s8CanonicalLaneSumDominanceCompilerFromTypedFields :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  (decomposition : YangMillsHamiltonianLaneDecomposition hypotheses) →
  (occupation :
    S8LaneOccupationNumberSurface hypotheses decomposition) →
  (weighting :
    S8PressureNormSquaredLaneWeightSurface hypotheses occupation) →
  S8LaneEnergyOrderCompatibility
    hypotheses
    decomposition
    occupation
    weighting →
  (ψ : State hypotheses) →
  nonVacuum hypotheses ψ →
  orthogonalToVacuum hypotheses ψ →
  _≤E_ hypotheses
    (S8PressureNormSquaredLaneWeightSurface.pressureNorm² weighting ψ)
    (hamiltonianEnergy hypotheses ψ)
s8CanonicalLaneSumDominanceCompilerFromTypedFields
  hypotheses
  decomposition
  occupation
  weighting =
  s8LaneSumDominanceCompilerFromRequestAndTypedFields
    hypotheses
    decomposition
    occupation
    weighting
    canonicalS8LaneSumDominanceCompilerRequest

record S8LaneHamiltonianDominanceDefinitionRequest : Set where
  field
    definitionInterfaceName :
      String

    exactDefinitionFields :
      List S8LaneHamiltonianDominanceDefinitionField

    exactDefinitionFieldsAreCanonical :
      exactDefinitionFields
      ≡
      canonicalS8LaneHamiltonianDominanceDefinitionFields

    firstDefinitionMissing :
      S8LaneHamiltonianDominanceDefinitionField

    firstDefinitionMissingIsLaneEnergyOrderCompatibility :
      firstDefinitionMissing
      ≡
      s8LaneEnergyOrderCompatibilityDefinitionField

    requestedHamiltonianLaneDecompositionDefinition :
      String

    requestedLaneOccupationNumberDefinition :
      String

    requestedPressureNormSquaredLaneWeightDefinition :
      String

    requestedMinimumNontrivialHolonomyDistanceDefinition :
      String

    concreteLaneDominanceDefinitionSurfaceName :
      String

    requestedLaneEnergyOrderCompatibilityDefinition :
      String

    requestedLaneSumDominanceCompiler :
      String

    laneSumDominanceCompilerRequest :
      S8LaneSumDominanceCompilerRequest

    laneSumDominanceCompilerRequestIsCanonical :
      laneSumDominanceCompilerRequest
      ≡
      canonicalS8LaneSumDominanceCompilerRequest

    laneDominancePrimitiveFound :
      Bool

    laneDominancePrimitiveFoundIsFalse :
      laneDominancePrimitiveFound ≡ false

    gapReceiptConstructed :
      Bool

    gapReceiptConstructedIsFalse :
      gapReceiptConstructed ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    definitionBoundary :
      List String

canonicalS8LaneHamiltonianDominanceDefinitionRequest :
  S8LaneHamiltonianDominanceDefinitionRequest
canonicalS8LaneHamiltonianDominanceDefinitionRequest =
  record
    { definitionInterfaceName =
        "S8LaneHamiltonianDominanceInterface"
    ; exactDefinitionFields =
        canonicalS8LaneHamiltonianDominanceDefinitionFields
    ; exactDefinitionFieldsAreCanonical =
        refl
    ; firstDefinitionMissing =
        s8LaneEnergyOrderCompatibilityDefinitionField
    ; firstDefinitionMissingIsLaneEnergyOrderCompatibility =
        refl
    ; requestedHamiltonianLaneDecompositionDefinition =
        "yangMillsHamiltonianLaneDecomposition : YangMillsHamiltonianLaneDecomposition hypotheses, with active p3/p5/p7 electric + magnetic energies and disjoint FactorVec supports"
    ; requestedLaneOccupationNumberDefinition =
        "laneOccupationNumberDefinition : occupation numbers for the active prime lanes of State"
    ; requestedPressureNormSquaredLaneWeightDefinition =
        "pressureNormSquaredLaneWeightDefinition : S8PressureNormSquaredLaneWeightSurface hypotheses laneOccupationNumberDefinition, with lane pressure weights, weighted lane energies, and pressureNormSquared as the weighted occupation surface"
    ; requestedMinimumNontrivialHolonomyDistanceDefinition =
        "minimumNontrivialHolonomyDistanceDefinition : S8MinimumNontrivialHolonomyDistanceSurface, normalized to the carrier unit 15 - 14"
    ; concreteLaneDominanceDefinitionSurfaceName =
        "S8ConcreteLaneHamiltonianDominanceDefinition"
    ; requestedLaneEnergyOrderCompatibilityDefinition =
        "laneEnergyOrderCompatibility : the Energy order is compatible with lane sums and Hamiltonian/norm comparison"
    ; requestedLaneSumDominanceCompiler =
        "laneSumDominanceToGlobalDominance : lane-wise Hamiltonian dominance compiles to pressureNormSquared psi <=E hamiltonianEnergy psi"
    ; laneSumDominanceCompilerRequest =
        canonicalS8LaneSumDominanceCompilerRequest
    ; laneSumDominanceCompilerRequestIsCanonical =
        refl
    ; laneDominancePrimitiveFound =
        false
    ; laneDominancePrimitiveFoundIsFalse =
        refl
    ; gapReceiptConstructed =
        false
    ; gapReceiptConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; definitionBoundary =
        "The local S8 package now names YangMillsHamiltonianLaneDecomposition as the concrete p3/p5/p7 Hamiltonian definition surface"
        ∷ "Lane occupation is narrowed to S8LaneOccupationNumberSurface over the active p3/p5/p7 decomposition"
        ∷ "Pressure weighting is narrowed to S8PressureNormSquaredLaneWeightSurface with an explicit weighted-lane pressureNormSquared"
        ∷ "The minimum nontrivial holonomy distance is narrowed to S8MinimumNontrivialHolonomyDistanceSurface and normalized to the carrier unit 15 - 14"
        ∷ "S8ConcreteLaneHamiltonianDominanceDefinition compiles these surfaces to S8LaneHamiltonianDominanceInterface only when an explicit laneSumDominanceToGlobalDominanceCompiler is supplied"
        ∷ "The exact remaining theorem gap below laneHamiltonianDominatesPressureNorm is the S8LaneEnergyOrderCompatibility primitive"
        ∷ "The lane-sum dominance compiler is now available once the typed compatibility package supplies the missing finite-lane order/arithmetic evidence"
        ∷ "Supplying S8LaneHamiltonianDominanceInterface plus order and gap-unit witnesses constructs the primitive interface, but still requires a compiler into the opaque pressureEnergyCoercive package field"
        ∷ "No spectral gap receipt or promotion is constructed by this definition request"
        ∷ []
    }

record S8PressureEnergyCoercivityPrimitiveRequest : Set where
  field
    primitiveInterfaceName :
      String

    exactPrimitiveFields :
      List S8PressureEnergyCoercivityPrimitiveField

    exactPrimitiveFieldsAreCanonical :
      exactPrimitiveFields
      ≡
      canonicalS8PressureEnergyCoercivityPrimitiveFields

    firstPrimitiveMissing :
      S8PressureEnergyCoercivityPrimitiveField

    firstPrimitiveMissingIsLaneHamiltonianDominance :
      firstPrimitiveMissing
      ≡
      s8LaneHamiltonianDominatesPressureNormField

    requestedPressureNormSquaredField :
      String

    requestedPressureOrderTransitivityField :
      String

    requestedGapUnitDominatedByPressureNormField :
      String

    requestedLaneHamiltonianDominatesPressureNormField :
      String

    requestedPressureEnergyCoercivityCompilerField :
      String

    laneHamiltonianDominanceDefinitionRequest :
      S8LaneHamiltonianDominanceDefinitionRequest

    laneHamiltonianDominanceDefinitionRequestIsCanonical :
      laneHamiltonianDominanceDefinitionRequest
      ≡
      canonicalS8LaneHamiltonianDominanceDefinitionRequest

    firstLaneDominanceDefinitionMissing :
      S8LaneHamiltonianDominanceDefinitionField

    firstLaneDominanceDefinitionMissingIsLaneEnergyOrderCompatibility :
      firstLaneDominanceDefinitionMissing
      ≡
      s8LaneEnergyOrderCompatibilityDefinitionField

    coercivityPrimitiveFound :
      Bool

    coercivityPrimitiveFoundIsFalse :
      coercivityPrimitiveFound ≡ false

    gapReceiptConstructed :
      Bool

    gapReceiptConstructedIsFalse :
      gapReceiptConstructed ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    primitiveBoundary :
      List String

canonicalS8PressureEnergyCoercivityPrimitiveRequest :
  S8PressureEnergyCoercivityPrimitiveRequest
canonicalS8PressureEnergyCoercivityPrimitiveRequest =
  record
    { primitiveInterfaceName =
        "S8PressureEnergyCoercivityPrimitiveInterface"
    ; exactPrimitiveFields =
        canonicalS8PressureEnergyCoercivityPrimitiveFields
    ; exactPrimitiveFieldsAreCanonical =
        refl
    ; firstPrimitiveMissing =
        s8LaneHamiltonianDominatesPressureNormField
    ; firstPrimitiveMissingIsLaneHamiltonianDominance =
        refl
    ; requestedPressureNormSquaredField =
        "pressureNormSquared : State -> Energy"
    ; requestedPressureOrderTransitivityField =
        "pressureOrderTransitive : a <=E b -> b <=E c -> a <=E c"
    ; requestedGapUnitDominatedByPressureNormField =
        "gapUnitDominatedByPressureNorm : nonVacuum psi -> psi orthogonalToVacuum -> gapUnit <=E pressureNormSquared psi"
    ; requestedLaneHamiltonianDominatesPressureNormField =
        "laneHamiltonianDominatesPressureNorm : nonVacuum psi -> psi orthogonalToVacuum -> pressureNormSquared psi <=E hamiltonianEnergy psi"
    ; requestedPressureEnergyCoercivityCompilerField =
        "pressureEnergyCoercivityCompiler : S8PressureEnergyCoercivityPrimitiveInterface hypotheses -> pressureEnergyCoercive hypotheses"
    ; laneHamiltonianDominanceDefinitionRequest =
        canonicalS8LaneHamiltonianDominanceDefinitionRequest
    ; laneHamiltonianDominanceDefinitionRequestIsCanonical =
        refl
    ; firstLaneDominanceDefinitionMissing =
        s8LaneEnergyOrderCompatibilityDefinitionField
    ; firstLaneDominanceDefinitionMissingIsLaneEnergyOrderCompatibility =
        refl
    ; coercivityPrimitiveFound =
        false
    ; coercivityPrimitiveFoundIsFalse =
        refl
    ; gapReceiptConstructed =
        false
    ; gapReceiptConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; primitiveBoundary =
        "This request narrows pressureEnergyCoercive to a lane Hamiltonian dominance theorem over a pressure norm"
        ∷ "The typed primitive interface can derive gapUnit <=E hamiltonianEnergy psi by transitivity"
        ∷ "The lane dominance primitive is further narrowed to YangMillsHamiltonianLaneDecomposition plus pressure-norm lane-weight and occupation definitions"
        ∷ "It still does not inhabit the opaque package field pressureEnergyCoercive without an explicit compiler witness"
        ∷ "The first missing primitive is laneHamiltonianDominatesPressureNorm; below that, the first missing definition witness is S8LaneEnergyOrderCompatibility"
        ∷ "No spectral gap receipt or promotion is constructed by this request"
        ∷ []
    }

canonicalS8PressureBelow15SearchedLocalCandidateSurfaces :
  List String
canonicalS8PressureBelow15SearchedLocalCandidateSurfaces =
  "DASHI.Physics.Closure.PressureBelow15SpectralProbe"
  ∷ "DASHI.Energy.Core"
  ∷ "DASHI.Energy.Energy"
  ∷ "DASHI.MDL.MDLDescentProofShift"
  ∷ "DASHI.Physics.Closure.ContinuumClayMassGapReceiptObligation"
  ∷ "DASHI.Physics.Closure.SchrodingerSelfAdjointEvolutionReceipt"
  ∷ "DASHI.Quantum.Stone"
  ∷ "DASHI.Physics.SchrodingerGap"
  ∷ "DASHI.Physics.SchrodingerGapShiftInstance"
  ∷ "DASHI.Physics.PressureHamiltonJacobiGap"
  ∷ "DASHI.Physics.Closure.YangMillsFieldEquationReceipt"
  ∷ "DASHI.Physics.Closure.YangMillsFieldEquationObstruction"
  ∷ "DASHI.Physics.ShiftDiscreteHelmholtzSurface"
  ∷ "DASHI.Physics.ShiftDiscreteWaveEnergy"
  ∷ "DASHI.Physics.ShiftWaveEnergyHierarchy"
  ∷ []

canonicalS8PressureBelow15SearchedWitnessFamilies :
  List String
canonicalS8PressureBelow15SearchedWitnessFamilies =
  "pressureEnergyCoercivityWitness"
  ∷ "positiveGapUnitWitness"
  ∷ "carrierUnitNormalizationWitness"
  ∷ "spectralWitnessInhabited"
  ∷ []

record S8PressureBelow15EvidenceIndex : Set where
  field
    searchedLocalCandidateSurfaces :
      List String

    searchedLocalCandidateSurfacesAreCanonical :
      searchedLocalCandidateSurfaces
      ≡
      canonicalS8PressureBelow15SearchedLocalCandidateSurfaces

    searchedWitnessFamilies :
      List String

    searchedWitnessFamiliesAreCanonical :
      searchedWitnessFamilies
      ≡
      canonicalS8PressureBelow15SearchedWitnessFamilies

    searchedLocalSplitFields :
      List S8PressureBelow15LocalTheoremField

    searchedLocalSplitFieldsAreCanonical :
      searchedLocalSplitFields
      ≡
      canonicalS8PressureBelow15LocalTheoremFields

    pressureEnergyCoercivityPrimitiveRequest :
      S8PressureEnergyCoercivityPrimitiveRequest

    pressureEnergyCoercivityPrimitiveRequestIsCanonical :
      pressureEnergyCoercivityPrimitiveRequest
      ≡
      canonicalS8PressureEnergyCoercivityPrimitiveRequest

    firstCoercivityPrimitiveMissing :
      S8PressureEnergyCoercivityPrimitiveField

    firstCoercivityPrimitiveMissingIsLaneHamiltonianDominance :
      firstCoercivityPrimitiveMissing
      ≡
      s8LaneHamiltonianDominatesPressureNormField

    coercivityPrimitiveFound :
      Bool

    coercivityPrimitiveFoundIsFalse :
      coercivityPrimitiveFound ≡ false

    positivityPrimitiveFound :
      Bool

    positivityPrimitiveFoundIsFalse :
      positivityPrimitiveFound ≡ false

    carrierUnitNormalizationPrimitiveFound :
      Bool

    carrierUnitNormalizationPrimitiveFoundIsFalse :
      carrierUnitNormalizationPrimitiveFound ≡ false

    spectralWitnessPrimitiveFound :
      Bool

    spectralWitnessPrimitiveFoundIsFalse :
      spectralWitnessPrimitiveFound ≡ false

    firstMissingWitness :
      S8PressureBelow15LocalTheoremField

    firstMissingWitnessIsCoercivity :
      firstMissingWitness
      ≡
      s8PressureEnergyCoercivityWitnessField

    firstMissingWitnessName :
      String

    evidenceBoundary :
      List String

canonicalS8PressureBelow15EvidenceIndex :
  S8PressureBelow15EvidenceIndex
canonicalS8PressureBelow15EvidenceIndex =
  record
    { searchedLocalCandidateSurfaces =
        canonicalS8PressureBelow15SearchedLocalCandidateSurfaces
    ; searchedLocalCandidateSurfacesAreCanonical =
        refl
    ; searchedWitnessFamilies =
        canonicalS8PressureBelow15SearchedWitnessFamilies
    ; searchedWitnessFamiliesAreCanonical =
        refl
    ; searchedLocalSplitFields =
        canonicalS8PressureBelow15LocalTheoremFields
    ; searchedLocalSplitFieldsAreCanonical =
        refl
    ; pressureEnergyCoercivityPrimitiveRequest =
        canonicalS8PressureEnergyCoercivityPrimitiveRequest
    ; pressureEnergyCoercivityPrimitiveRequestIsCanonical =
        refl
    ; firstCoercivityPrimitiveMissing =
        s8LaneHamiltonianDominatesPressureNormField
    ; firstCoercivityPrimitiveMissingIsLaneHamiltonianDominance =
        refl
    ; coercivityPrimitiveFound =
        false
    ; coercivityPrimitiveFoundIsFalse =
        refl
    ; positivityPrimitiveFound =
        false
    ; positivityPrimitiveFoundIsFalse =
        refl
    ; carrierUnitNormalizationPrimitiveFound =
        false
    ; carrierUnitNormalizationPrimitiveFoundIsFalse =
        refl
    ; spectralWitnessPrimitiveFound =
        false
    ; spectralWitnessPrimitiveFoundIsFalse =
        refl
    ; firstMissingWitness =
        s8PressureEnergyCoercivityWitnessField
    ; firstMissingWitnessIsCoercivity =
        refl
    ; firstMissingWitnessName =
        "s8PressureEnergyCoercivityWitnessField"
    ; evidenceBoundary =
        "PressureBelow15SpectralProbe supplies arithmetic pressure evidence only"
        ∷ "Energy.Core, Energy.Energy, and MDLDescentProofShift expose abstract preorders and a Nat preorder instance, but no bridge from this package's opaque Energy/_<=E_ to Nat order"
        ∷ "ContinuumClayMassGapReceiptObligation records pressure-to-spectral-gap as still missing"
        ∷ "SchrodingerSelfAdjointEvolutionReceipt and DASHI.Quantum.Stone expose only supplied-bundle/self-adjoint routes, not pressure coercivity or a spectral gap"
        ∷ "SchrodingerGap and PressureHamiltonJacobiGap are theorem-thin supplied-witness packaging surfaces"
        ∷ "YangMillsFieldEquationReceipt and YangMillsFieldEquationObstruction stop at field-equation or curvature obligations, not Hamiltonian spectral witnesses"
        ∷ "Shift discrete wave and Helmholtz surfaces are finite proxy surfaces and explicitly avoid coercivity, positivity-theorem, spectral-theorem, or PDE claims"
        ∷ "No searched local surface inhabits coercivity, positivity, carrier-unit normalization, or spectral witness fields for S8"
        ∷ "The pressure-energy coercivity witness is now narrowed to the primitive laneHamiltonianDominatesPressureNorm request"
        ∷ "S8LaneSumDominanceExternalLemmaInterface is the final external interface for the six p3/p5/p7 dominance, pressure-expansion, three-lane monotonicity, and active-lane transport witnesses"
        ∷ "The first missing local witness remains pressureEnergyCoercivityWitness"
        ∷ []
    }

record SelfAdjointYangMillsHamiltonianOnCarrierQuotient
  (hypotheses : PressureToSpectralGapHypothesisPackage)
  : Setω where
  field
    carrierQuotientState :
      Set

    carrierQuotientStateIsPackageState :
      carrierQuotientState
      ≡
      State hypotheses

    carrierHilbertSpace :
      U.HilbertSpace

    carrierHilbertSpaceStateCarrierMatchesQuotient :
      U.HilbertSpace.H carrierHilbertSpace
      ≡
      carrierQuotientState

    carrierHamiltonian :
      U.HilbertSpace.H carrierHilbertSpace →
      U.HilbertSpace.H carrierHilbertSpace

    s8SelfAdjointHamiltonianOnCarrierQuotient :
      Stone.StoneSelfAdjoint
        carrierHilbertSpace
        carrierHamiltonian

    selfAdjointFieldIsCanonical :
      s8SelfAdjointHamiltonianOnCarrierQuotientField
      ≡
      s8SelfAdjointHamiltonianOnCarrierQuotientField

    vacuumSector :
      State hypotheses

    vacuumSectorIsPackageVacuum :
      vacuumSector
      ≡
      vacuum hypotheses

    nonVacuumSectorPredicate :
      State hypotheses →
      Set

    nonVacuumSectorPredicateMatchesPackage :
      nonVacuumSectorPredicate
      ≡
      nonVacuum hypotheses

    vacuumOrthogonalityPredicate :
      State hypotheses →
      Set

    vacuumOrthogonalityPredicateMatchesPackage :
      vacuumOrthogonalityPredicate
      ≡
      orthogonalToVacuum hypotheses

    energyOrderAndPositiveGapUnit :
      gapUnitPositive hypotheses

    subThresholdLowerBoundTransport :
      (ψ : State hypotheses) →
      nonVacuum hypotheses ψ →
      orthogonalToVacuum hypotheses ψ →
      _≤E_ hypotheses
        (gapUnit hypotheses)
        (hamiltonianEnergy hypotheses ψ)

    pressureEnergyCoercivityWitness :
      pressureEnergyCoercive hypotheses

    carrierUnitNormalizationWitness :
      carrierUnitNormalization hypotheses
        14
        15
        Probe.canonicalPressureDeficitIs1

    carrierTheoremFields :
      List S8GlobalYangMillsHamiltonianCarrierTheoremField

    carrierTheoremFieldsAreCanonical :
      carrierTheoremFields
      ≡
      canonicalS8GlobalYangMillsHamiltonianCarrierTheoremFields

    theoremBoundary :
      List String

open SelfAdjointYangMillsHamiltonianOnCarrierQuotient public

selfAdjointYangMillsCarrierSubThresholdDependency :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  SelfAdjointYangMillsHamiltonianOnCarrierQuotient hypotheses →
  S8SubThresholdSpectralGapDependency hypotheses
selfAdjointYangMillsCarrierSubThresholdDependency
  hypotheses
  carrierTheorem =
  s8SubThresholdDependencyFromLocalWitnesses
    hypotheses
    (pressureEnergyCoercivityWitness carrierTheorem)
    (carrierUnitNormalizationWitness carrierTheorem)

record S8GlobalYangMillsHamiltonianCarrierBlocker : Setω where
  field
    targetCarrierTheoremName :
      String

    exactMissingCarrierTheorem :
      S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    firstMissingCarrierTheorem :
      S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    firstMissingCarrierTheoremIsSelfAdjointYangMillsHamiltonian :
      firstMissingCarrierTheorem
      ≡
      missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    requiredCarrierTheoremFields :
      List S8GlobalYangMillsHamiltonianCarrierTheoremField

    requiredCarrierTheoremFieldsAreCanonical :
      requiredCarrierTheoremFields
      ≡
      canonicalS8GlobalYangMillsHamiltonianCarrierTheoremFields

    firstMissingCarrierTheoremField :
      S8GlobalYangMillsHamiltonianCarrierTheoremField

    firstMissingCarrierTheoremFieldIsSelfAdjointHamiltonian :
      firstMissingCarrierTheoremField
      ≡
      s8SelfAdjointHamiltonianOnCarrierQuotientField

    remainingCarrierTheoremFieldsAfterFirstMissing :
      List S8GlobalYangMillsHamiltonianCarrierTheoremField

    remainingCarrierTheoremFieldsAfterFirstMissingAreCanonical :
      remainingCarrierTheoremFieldsAfterFirstMissing
      ≡
      canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterSelfAdjoint

    nextCarrierTheoremFieldAfterFirstMissing :
      S8GlobalYangMillsHamiltonianCarrierTheoremField

    nextCarrierTheoremFieldAfterFirstMissingIsVacuumSector :
      nextCarrierTheoremFieldAfterFirstMissing
      ≡
      s8VacuumSectorField

    nextCarrierTheoremFieldAfterVacuum :
      S8GlobalYangMillsHamiltonianCarrierTheoremField

    nextCarrierTheoremFieldAfterVacuumIsNonVacuumPredicate :
      nextCarrierTheoremFieldAfterVacuum
      ≡
      s8NonVacuumSectorPredicateField

    nextCarrierTheoremFieldAfterNonVacuum :
      S8GlobalYangMillsHamiltonianCarrierTheoremField

    nextCarrierTheoremFieldAfterNonVacuumIsVacuumOrthogonality :
      nextCarrierTheoremFieldAfterNonVacuum
      ≡
      s8VacuumOrthogonalityPredicateField

    nextCarrierTheoremFieldAfterVacuumOrthogonality :
      S8GlobalYangMillsHamiltonianCarrierTheoremField

    nextCarrierTheoremFieldAfterVacuumOrthogonalityIsEnergyOrderAndPositiveGapUnit :
      nextCarrierTheoremFieldAfterVacuumOrthogonality
      ≡
      s8EnergyOrderAndPositiveGapUnitField

    nextCarrierTheoremFieldAfterEnergyOrderAndPositiveGapUnit :
      S8GlobalYangMillsHamiltonianCarrierTheoremField

    nextCarrierTheoremFieldAfterEnergyOrderAndPositiveGapUnitIsSubThresholdLowerBoundTransport :
      nextCarrierTheoremFieldAfterEnergyOrderAndPositiveGapUnit
      ≡
      s8SubThresholdLowerBoundTransportField

    nextCarrierTheoremFieldAfterSubThresholdLowerBoundTransport :
      S8GlobalYangMillsHamiltonianCarrierTheoremField

    nextCarrierTheoremFieldAfterSubThresholdLowerBoundTransportIsPressureEnergyCoercivityWitness :
      nextCarrierTheoremFieldAfterSubThresholdLowerBoundTransport
      ≡
      s8PressureEnergyCoercivityWitnessField

    nextCarrierTheoremFieldAfterPressureEnergyCoercivity :
      S8GlobalYangMillsHamiltonianCarrierTheoremField

    nextCarrierTheoremFieldAfterPressureEnergyCoercivityIsCarrierUnitNormalization :
      nextCarrierTheoremFieldAfterPressureEnergyCoercivity
      ≡
      s8CarrierUnitNormalizationField

    remainingCarrierTheoremFieldsAfterNonVacuum :
      List S8GlobalYangMillsHamiltonianCarrierTheoremField

    remainingCarrierTheoremFieldsAfterNonVacuumAreCanonical :
      remainingCarrierTheoremFieldsAfterNonVacuum
      ≡
      canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterNonVacuum

    remainingCarrierTheoremFieldsAfterVacuumOrthogonality :
      List S8GlobalYangMillsHamiltonianCarrierTheoremField

    remainingCarrierTheoremFieldsAfterVacuumOrthogonalityAreCanonical :
      remainingCarrierTheoremFieldsAfterVacuumOrthogonality
      ≡
      canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterVacuumOrthogonality

    remainingCarrierTheoremFieldsAfterEnergyOrderAndPositiveGapUnit :
      List S8GlobalYangMillsHamiltonianCarrierTheoremField

    remainingCarrierTheoremFieldsAfterEnergyOrderAndPositiveGapUnitAreCanonical :
      remainingCarrierTheoremFieldsAfterEnergyOrderAndPositiveGapUnit
      ≡
      canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterEnergyOrderAndPositiveGapUnit

    remainingCarrierTheoremFieldsAfterSubThresholdLowerBoundTransport :
      List S8GlobalYangMillsHamiltonianCarrierTheoremField

    remainingCarrierTheoremFieldsAfterSubThresholdLowerBoundTransportAreCanonical :
      remainingCarrierTheoremFieldsAfterSubThresholdLowerBoundTransport
      ≡
      canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterSubThresholdLowerBoundTransport

    remainingCarrierTheoremFieldsAfterPressureEnergyCoercivity :
      List S8GlobalYangMillsHamiltonianCarrierTheoremField

    remainingCarrierTheoremFieldsAfterPressureEnergyCoercivityAreCanonical :
      remainingCarrierTheoremFieldsAfterPressureEnergyCoercivity
      ≡
      canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterPressureEnergyCoercivity

    remainingCarrierTheoremFieldsAfterVacuum :
      List S8GlobalYangMillsHamiltonianCarrierTheoremField

    remainingCarrierTheoremFieldsAfterVacuumAreCanonical :
      remainingCarrierTheoremFieldsAfterVacuum
      ≡
      canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterVacuum

    blockerVerdict :
      S8GlobalYangMillsHamiltonianCarrierBlockerVerdict

    blockerVerdictIsGlobalCarrierRequired :
      blockerVerdict
      ≡
      globalCarrierTheoremRequiredBeforeS8SpectralGap

    carrierTheoremConstructed :
      Bool

    carrierTheoremConstructedIsFalse :
      carrierTheoremConstructed ≡ false

    yangMillsHamiltonianCarrierAvailable :
      Bool

    yangMillsHamiltonianCarrierAvailableIsFalse :
      yangMillsHamiltonianCarrierAvailable ≡ false

    s8TheoremInhabited :
      Bool

    s8TheoremInhabitedIsFalse :
      s8TheoremInhabited ≡ false

    gapReceiptConstructed :
      Bool

    gapReceiptConstructedIsFalse :
      gapReceiptConstructed ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    carrierBlockerBoundary :
      List String

open S8GlobalYangMillsHamiltonianCarrierBlocker public

canonicalS8GlobalYangMillsHamiltonianCarrierBlocker :
  S8GlobalYangMillsHamiltonianCarrierBlocker
canonicalS8GlobalYangMillsHamiltonianCarrierBlocker =
  record
    { targetCarrierTheoremName =
        "SelfAdjointYangMillsHamiltonianOnCarrierQuotient"
    ; exactMissingCarrierTheorem =
        missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; firstMissingCarrierTheorem =
        missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; firstMissingCarrierTheoremIsSelfAdjointYangMillsHamiltonian =
        refl
    ; requiredCarrierTheoremFields =
        canonicalS8GlobalYangMillsHamiltonianCarrierTheoremFields
    ; requiredCarrierTheoremFieldsAreCanonical =
        refl
    ; firstMissingCarrierTheoremField =
        s8SelfAdjointHamiltonianOnCarrierQuotientField
    ; firstMissingCarrierTheoremFieldIsSelfAdjointHamiltonian =
        refl
    ; remainingCarrierTheoremFieldsAfterFirstMissing =
        canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterSelfAdjoint
    ; remainingCarrierTheoremFieldsAfterFirstMissingAreCanonical =
        refl
    ; nextCarrierTheoremFieldAfterFirstMissing =
        s8VacuumSectorField
    ; nextCarrierTheoremFieldAfterFirstMissingIsVacuumSector =
        refl
    ; nextCarrierTheoremFieldAfterVacuum =
        s8NonVacuumSectorPredicateField
    ; nextCarrierTheoremFieldAfterVacuumIsNonVacuumPredicate =
        refl
    ; nextCarrierTheoremFieldAfterNonVacuum =
        s8VacuumOrthogonalityPredicateField
    ; nextCarrierTheoremFieldAfterNonVacuumIsVacuumOrthogonality =
        refl
    ; nextCarrierTheoremFieldAfterVacuumOrthogonality =
        s8EnergyOrderAndPositiveGapUnitField
    ; nextCarrierTheoremFieldAfterVacuumOrthogonalityIsEnergyOrderAndPositiveGapUnit =
        refl
    ; nextCarrierTheoremFieldAfterEnergyOrderAndPositiveGapUnit =
        s8SubThresholdLowerBoundTransportField
    ; nextCarrierTheoremFieldAfterEnergyOrderAndPositiveGapUnitIsSubThresholdLowerBoundTransport =
        refl
    ; nextCarrierTheoremFieldAfterSubThresholdLowerBoundTransport =
        s8PressureEnergyCoercivityWitnessField
    ; nextCarrierTheoremFieldAfterSubThresholdLowerBoundTransportIsPressureEnergyCoercivityWitness =
        refl
    ; nextCarrierTheoremFieldAfterPressureEnergyCoercivity =
        s8CarrierUnitNormalizationField
    ; nextCarrierTheoremFieldAfterPressureEnergyCoercivityIsCarrierUnitNormalization =
        refl
    ; remainingCarrierTheoremFieldsAfterNonVacuum =
        canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterNonVacuum
    ; remainingCarrierTheoremFieldsAfterNonVacuumAreCanonical =
        refl
    ; remainingCarrierTheoremFieldsAfterVacuumOrthogonality =
        canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterVacuumOrthogonality
    ; remainingCarrierTheoremFieldsAfterVacuumOrthogonalityAreCanonical =
        refl
    ; remainingCarrierTheoremFieldsAfterEnergyOrderAndPositiveGapUnit =
        canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterEnergyOrderAndPositiveGapUnit
    ; remainingCarrierTheoremFieldsAfterEnergyOrderAndPositiveGapUnitAreCanonical =
        refl
    ; remainingCarrierTheoremFieldsAfterSubThresholdLowerBoundTransport =
        canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterSubThresholdLowerBoundTransport
    ; remainingCarrierTheoremFieldsAfterSubThresholdLowerBoundTransportAreCanonical =
        refl
    ; remainingCarrierTheoremFieldsAfterPressureEnergyCoercivity =
        canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterPressureEnergyCoercivity
    ; remainingCarrierTheoremFieldsAfterPressureEnergyCoercivityAreCanonical =
        refl
    ; remainingCarrierTheoremFieldsAfterVacuum =
        canonicalS8GlobalYangMillsHamiltonianCarrierRemainingFieldsAfterVacuum
    ; remainingCarrierTheoremFieldsAfterVacuumAreCanonical =
        refl
    ; blockerVerdict =
        globalCarrierTheoremRequiredBeforeS8SpectralGap
    ; blockerVerdictIsGlobalCarrierRequired =
        refl
    ; carrierTheoremConstructed =
        false
    ; carrierTheoremConstructedIsFalse =
        refl
    ; yangMillsHamiltonianCarrierAvailable =
        false
    ; yangMillsHamiltonianCarrierAvailableIsFalse =
        refl
    ; s8TheoremInhabited =
        false
    ; s8TheoremInhabitedIsFalse =
        refl
    ; gapReceiptConstructed =
        false
    ; gapReceiptConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; carrierBlockerBoundary =
        "The bounded Nat slice supplies package-local arithmetic only"
        ∷ "The global S8 theorem still needs a self-adjoint Yang-Mills Hamiltonian carrier over the carrier quotient"
        ∷ "The carrier theorem now has a canonical required-field list, with first missing field s8SelfAdjointHamiltonianOnCarrierQuotientField"
        ∷ "Post-self-adjoint focus is now explicit: the canonical next missing field is s8VacuumSectorField"
        ∷ "Post-vacuum focus is now explicit: the canonical next missing field is s8NonVacuumSectorPredicateField"
        ∷ "Post-non-vacuum focus is now explicit: the canonical next missing field is s8VacuumOrthogonalityPredicateField"
        ∷ "Post-vacuum-orthogonality focus is now explicit: the canonical next missing field is s8EnergyOrderAndPositiveGapUnitField"
        ∷ "Post-energy-order focus is now explicit: the canonical next missing field is s8SubThresholdLowerBoundTransportField"
        ∷ "Post-subthreshold focus is now explicit: the canonical next missing field is s8PressureEnergyCoercivityWitnessField"
        ∷ "Post-pressure-energy-coercivity focus is now explicit: the canonical next missing field is s8CarrierUnitNormalizationField"
        ∷ "That carrier theorem must expose the Hamiltonian carrier, vacuum/non-vacuum sector split, vacuum orthogonality, ordered energy codomain, positive gap unit, coercivity, and carrier-unit normalization needed by PressureToSpectralGapHypothesisPackage"
        ∷ "Until that carrier theorem is inhabited, S8PressureBelow15ToYangMillsSpectralGapTheorem is uninhabited"
        ∷ "No PressureBelow15SpectralGapReceipt or spectral-gap promotion is constructed by this blocker record"
        ∷ []
    }

record S8RealPhysicalCarrierTransitionTarget : Setω where
  field
    boundedNatPressureEnergyCoercivityField :
      S8GlobalYangMillsHamiltonianCarrierTheoremField

    boundedNatPressureEnergyCoercivityFieldIsCanonical :
      boundedNatPressureEnergyCoercivityField
      ≡
      s8PressureEnergyCoercivityWitnessField

    boundedNatCarrierUnitNormalizationField :
      S8GlobalYangMillsHamiltonianCarrierTheoremField

    boundedNatCarrierUnitNormalizationFieldIsCanonical :
      boundedNatCarrierUnitNormalizationField
      ≡
      s8CarrierUnitNormalizationField

    boundedNatCarrierKind :
      S8CarrierEvidenceKind

    boundedNatCarrierKindIsBoundedNat :
      boundedNatCarrierKind
      ≡
      boundedNatCarrierEvidence

    realPhysicalCarrierKind :
      S8CarrierEvidenceKind

    realPhysicalCarrierKindIsRealPhysical :
      realPhysicalCarrierKind
      ≡
      realPhysicalCarrierEvidence

    realPhysicalCarrier :
      Set

    realPhysicalCarrierIsRealAnalysisℝ :
      realPhysicalCarrier
      ≡
      s8RealPhysicalCarrier

    requiredRealCarrierTheoremName :
      String

    requiredRealCarrierTheoremNameIsSelfAdjointYangMillsHamiltonianOnCarrierQuotient :
      requiredRealCarrierTheoremName
      ≡
      "SelfAdjointYangMillsHamiltonianOnCarrierQuotient"

    requiredRealCarrierTheoremTarget :
      S8RealCarrierRequiredTheoremTarget

    requiredRealCarrierTheoremTargetIsSelfAdjointYangMillsHamiltonianOnRealCarrier :
      requiredRealCarrierTheoremTarget
      ≡
      selfAdjointYangMillsHamiltonianOnRealCarrierQuotientTarget

    nonVacuumSpectralLowerBoundTarget :
      S8NonVacuumSpectralLowerBoundTarget

    nonVacuumSpectralLowerBoundTargetIsInfSigmaHYMGreaterThanZero :
      nonVacuumSpectralLowerBoundTarget
      ≡
      infSigmaHYMGreaterThanZeroOnNonVacuumCarrier

    nonVacuumSpectralLowerBoundTargetName :
      String

    nonVacuumSpectralLowerBoundTargetNameIsInfSigmaHYMGreaterThanZero :
      nonVacuumSpectralLowerBoundTargetName
      ≡
      "inf sigma(H_YM)>0 on the non-vacuum real carrier"

    nonVacuumSpectralLowerBoundSet :
      RA.ℝ →
      Set

    nonVacuumSpectralLowerBoundSetIsInfSigmaPositive :
      (infSigmaHYM : RA.ℝ) →
      nonVacuumSpectralLowerBoundSet infSigmaHYM
      ≡
      s8InfSigmaHYMGreaterThanZeroTarget infSigmaHYM

    firstRemainingRealCarrierBlocker :
      S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    firstRemainingRealCarrierBlockerIsMissingSelfAdjoint :
      firstRemainingRealCarrierBlocker
      ≡
      missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    hardExternalHalt :
      S8RealCarrierHardExternalHalt

    hardExternalHaltIsUniformBalabanOrAgawaIRFixedPoint :
      hardExternalHalt
      ≡
      uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    hardExternalHaltName :
      String

    hardExternalHaltNameIsUniformBalabanOrAgawaIRFixedPoint :
      hardExternalHaltName
      ≡
      "UniformBalaban-or-AgawaIRFixedPoint"

    carrierTheoremConstructed :
      Bool

    carrierTheoremConstructedIsFalse :
      carrierTheoremConstructed ≡ false

    s8TheoremPromoted :
      Bool

    s8TheoremPromotedIsFalse :
      s8TheoremPromoted ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    receiptBoundary :
      List String

canonicalS8RealPhysicalCarrierTransitionTarget :
  S8RealPhysicalCarrierTransitionTarget
canonicalS8RealPhysicalCarrierTransitionTarget =
  record
    { boundedNatPressureEnergyCoercivityField =
        s8PressureEnergyCoercivityWitnessField
    ; boundedNatPressureEnergyCoercivityFieldIsCanonical =
        refl
    ; boundedNatCarrierUnitNormalizationField =
        s8CarrierUnitNormalizationField
    ; boundedNatCarrierUnitNormalizationFieldIsCanonical =
        refl
    ; boundedNatCarrierKind =
        boundedNatCarrierEvidence
    ; boundedNatCarrierKindIsBoundedNat =
        refl
    ; realPhysicalCarrierKind =
        realPhysicalCarrierEvidence
    ; realPhysicalCarrierKindIsRealPhysical =
        refl
    ; realPhysicalCarrier =
        s8RealPhysicalCarrier
    ; realPhysicalCarrierIsRealAnalysisℝ =
        refl
    ; requiredRealCarrierTheoremName =
        "SelfAdjointYangMillsHamiltonianOnCarrierQuotient"
    ; requiredRealCarrierTheoremNameIsSelfAdjointYangMillsHamiltonianOnCarrierQuotient =
        refl
    ; requiredRealCarrierTheoremTarget =
        selfAdjointYangMillsHamiltonianOnRealCarrierQuotientTarget
    ; requiredRealCarrierTheoremTargetIsSelfAdjointYangMillsHamiltonianOnRealCarrier =
        refl
    ; nonVacuumSpectralLowerBoundTarget =
        infSigmaHYMGreaterThanZeroOnNonVacuumCarrier
    ; nonVacuumSpectralLowerBoundTargetIsInfSigmaHYMGreaterThanZero =
        refl
    ; nonVacuumSpectralLowerBoundTargetName =
        "inf sigma(H_YM)>0 on the non-vacuum real carrier"
    ; nonVacuumSpectralLowerBoundTargetNameIsInfSigmaHYMGreaterThanZero =
        refl
    ; nonVacuumSpectralLowerBoundSet =
        s8InfSigmaHYMGreaterThanZeroTarget
    ; nonVacuumSpectralLowerBoundSetIsInfSigmaPositive =
        λ infSigmaHYM → refl
    ; firstRemainingRealCarrierBlocker =
        missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; firstRemainingRealCarrierBlockerIsMissingSelfAdjoint =
        refl
    ; hardExternalHalt =
        uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; hardExternalHaltIsUniformBalabanOrAgawaIRFixedPoint =
        refl
    ; hardExternalHaltName =
        "UniformBalaban-or-AgawaIRFixedPoint"
    ; hardExternalHaltNameIsUniformBalabanOrAgawaIRFixedPoint =
        refl
    ; carrierTheoremConstructed =
        false
    ; carrierTheoremConstructedIsFalse =
        refl
    ; s8TheoremPromoted =
        false
    ; s8TheoremPromotedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; receiptBoundary =
        "The bounded Nat s8PressureEnergyCoercivityWitnessField and s8CarrierUnitNormalizationField remain Nat-slice witnesses only"
        ∷ "The real physical carrier is RealAnalysisAxioms.ℝ, not the bounded Nat carrier"
        ∷ "The required real-carrier theorem is SelfAdjointYangMillsHamiltonianOnCarrierQuotient over a package whose State is the real carrier"
        ∷ "The non-vacuum spectral lower-bound target is named as inf sigma(H_YM)>0 on the non-vacuum real carrier"
        ∷ "The first remaining real-carrier blocker is missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient"
        ∷ "The hard external halt is UniformBalaban-or-AgawaIRFixedPoint"
        ∷ "No global S8 theorem, spectral-gap receipt, or promotion bit is constructed by this transition target"
        ∷ []
    }

data U1RealYMCarrierAttemptStatus : Set where
  u1RealCarrierQuotientHamiltonianBlockedFiniteEvidenceOnly :
    U1RealYMCarrierAttemptStatus

data U1RealYMCarrierAttemptField : Set where
  u1RealCarrierQuotientField :
    U1RealYMCarrierAttemptField

  u1HamiltonianOperatorField :
    U1RealYMCarrierAttemptField

  u1DenseDomainField :
    U1RealYMCarrierAttemptField

  u1SymmetryOnDomainField :
    U1RealYMCarrierAttemptField

  u1SelfAdjointnessField :
    U1RealYMCarrierAttemptField

  u1LocalFiniteCasimirSpectralBoundField :
    U1RealYMCarrierAttemptField

  u1ConditionalPreprintAuthorityField :
    U1RealYMCarrierAttemptField

  u1ContinuumClayFalseField :
    U1RealYMCarrierAttemptField

canonicalU1RealYMCarrierAttemptFields :
  List U1RealYMCarrierAttemptField
canonicalU1RealYMCarrierAttemptFields =
  u1RealCarrierQuotientField
  ∷ u1HamiltonianOperatorField
  ∷ u1DenseDomainField
  ∷ u1SymmetryOnDomainField
  ∷ u1SelfAdjointnessField
  ∷ u1LocalFiniteCasimirSpectralBoundField
  ∷ u1ConditionalPreprintAuthorityField
  ∷ u1ContinuumClayFalseField
  ∷ []

record U1RealYMCarrierHamiltonianDomainSymmetryFailClosedReceipt : Setω where
  field
    status :
      U1RealYMCarrierAttemptStatus

    attemptFields :
      List U1RealYMCarrierAttemptField

    attemptFieldsAreCanonical :
      attemptFields
      ≡
      canonicalU1RealYMCarrierAttemptFields

    realCarrierTransitionTarget :
      S8RealPhysicalCarrierTransitionTarget

    realCarrierTransitionTargetIsCanonical :
      Bool

    realCarrierTransitionTargetIsCanonicalIsTrue :
      realCarrierTransitionTargetIsCanonical ≡ true

    selfAdjointHamiltonianBlockerReceipt :
      S8SelfAdjointHamiltonianBlockerReceipt

    selfAdjointHamiltonianBlockerReceiptIsCanonical :
      Bool

    selfAdjointHamiltonianBlockerReceiptIsCanonicalIsTrue :
      selfAdjointHamiltonianBlockerReceiptIsCanonical ≡ true

    stonePrimitiveRequest :
      Stone.PhysicalHilbertStonePrimitiveRequest

    stonePrimitiveRequestIsCanonical :
      stonePrimitiveRequest
      ≡
      Stone.canonicalPhysicalHilbertStonePrimitiveRequest

    authorityBoundary :
      MassGap.U1ConditionalPreprintAuthorityBoundary

    authorityBoundaryIsCanonical :
      Bool

    authorityBoundaryIsCanonicalIsTrue :
      authorityBoundaryIsCanonical ≡ true

    realCarrier :
      Set

    realCarrierIsRealAnalysisℝ :
      realCarrier
      ≡
      s8RealPhysicalCarrier

    requiredRealCarrierTheorem :
      S8RealCarrierRequiredTheoremTarget

    requiredRealCarrierTheoremIsSelfAdjointHamiltonian :
      requiredRealCarrierTheorem
      ≡
      selfAdjointYangMillsHamiltonianOnRealCarrierQuotientTarget

    localFiniteCasimirGapEvidenceAvailable :
      Bool

    localFiniteCasimirGapEvidenceAvailableIsTrue :
      localFiniteCasimirGapEvidenceAvailable ≡ true

    localFiniteCasimirGapEvidencePromotesRealQuotient :
      Bool

    localFiniteCasimirGapEvidencePromotesRealQuotientIsFalse :
      localFiniteCasimirGapEvidencePromotesRealQuotient ≡ false

    realCarrierQuotientConstructed :
      Bool

    realCarrierQuotientConstructedIsFalse :
      realCarrierQuotientConstructed ≡ false

    hamiltonianOperatorConstructed :
      Bool

    hamiltonianOperatorConstructedIsFalse :
      hamiltonianOperatorConstructed ≡ false

    denseDomainConstructed :
      Bool

    denseDomainConstructedIsFalse :
      denseDomainConstructed ≡ false

    symmetricOnDomainConstructed :
      Bool

    symmetricOnDomainConstructedIsFalse :
      symmetricOnDomainConstructed ≡ false

    selfAdjointHamiltonianConstructed :
      Bool

    selfAdjointHamiltonianConstructedIsFalse :
      selfAdjointHamiltonianConstructed ≡ false

    conditionalPreprintAuthorityAccepted :
      Bool

    conditionalPreprintAuthorityAcceptedIsFalse :
      conditionalPreprintAuthorityAccepted ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    boundary :
      List String

open U1RealYMCarrierHamiltonianDomainSymmetryFailClosedReceipt public

canonicalU1RealYMCarrierHamiltonianDomainSymmetryFailClosedReceipt :
  U1RealYMCarrierHamiltonianDomainSymmetryFailClosedReceipt
canonicalU1RealYMCarrierHamiltonianDomainSymmetryFailClosedReceipt =
  record
    { status =
        u1RealCarrierQuotientHamiltonianBlockedFiniteEvidenceOnly
    ; attemptFields =
        canonicalU1RealYMCarrierAttemptFields
    ; attemptFieldsAreCanonical =
        refl
    ; realCarrierTransitionTarget =
        canonicalS8RealPhysicalCarrierTransitionTarget
    ; realCarrierTransitionTargetIsCanonical =
        true
    ; realCarrierTransitionTargetIsCanonicalIsTrue =
        refl
    ; selfAdjointHamiltonianBlockerReceipt =
        canonicalS8SelfAdjointHamiltonianBlockerReceipt
    ; selfAdjointHamiltonianBlockerReceiptIsCanonical =
        true
    ; selfAdjointHamiltonianBlockerReceiptIsCanonicalIsTrue =
        refl
    ; stonePrimitiveRequest =
        Stone.canonicalPhysicalHilbertStonePrimitiveRequest
    ; stonePrimitiveRequestIsCanonical =
        refl
    ; authorityBoundary =
        MassGap.canonicalU1ConditionalPreprintAuthorityBoundary
    ; authorityBoundaryIsCanonical =
        true
    ; authorityBoundaryIsCanonicalIsTrue =
        refl
    ; realCarrier =
        s8RealPhysicalCarrier
    ; realCarrierIsRealAnalysisℝ =
        refl
    ; requiredRealCarrierTheorem =
        selfAdjointYangMillsHamiltonianOnRealCarrierQuotientTarget
    ; requiredRealCarrierTheoremIsSelfAdjointHamiltonian =
        refl
    ; localFiniteCasimirGapEvidenceAvailable =
        true
    ; localFiniteCasimirGapEvidenceAvailableIsTrue =
        refl
    ; localFiniteCasimirGapEvidencePromotesRealQuotient =
        false
    ; localFiniteCasimirGapEvidencePromotesRealQuotientIsFalse =
        refl
    ; realCarrierQuotientConstructed =
        false
    ; realCarrierQuotientConstructedIsFalse =
        refl
    ; hamiltonianOperatorConstructed =
        false
    ; hamiltonianOperatorConstructedIsFalse =
        refl
    ; denseDomainConstructed =
        false
    ; denseDomainConstructedIsFalse =
        refl
    ; symmetricOnDomainConstructed =
        false
    ; symmetricOnDomainConstructedIsFalse =
        refl
    ; selfAdjointHamiltonianConstructed =
        false
    ; selfAdjointHamiltonianConstructedIsFalse =
        refl
    ; conditionalPreprintAuthorityAccepted =
        false
    ; conditionalPreprintAuthorityAcceptedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; boundary =
        "u1 attempted the real Yang-Mills carrier quotient, Hamiltonian, dense-domain, and symmetry route"
        ∷ "The route reuses the S8 real-carrier transition target and the self-adjoint Hamiltonian blocker receipt"
        ∷ "DASHI.Quantum.Stone supplies finite one-point Stone data and a primitive request, but not the physical quotient inner product, dense domain, or self-adjoint Yang-Mills Hamiltonian"
        ∷ "The available gap evidence is local finite Casimir-style carrier evidence only"
        ∷ "That local finite evidence does not promote to a real carrier quotient or continuum spectral theorem"
        ∷ "Conditional preprint authority is recorded under review and not accepted"
        ∷ "No spectral gap, continuum Clay mass gap, or terminal claim is promoted"
        ∷ []
    }

u1RealYMSelfAdjointHamiltonianBlocked :
  selfAdjointHamiltonianConstructed
    canonicalU1RealYMCarrierHamiltonianDomainSymmetryFailClosedReceipt
  ≡
  false
u1RealYMSelfAdjointHamiltonianBlocked =
  refl

u1RealYMLocalFiniteEvidenceDoesNotPromoteRealQuotient :
  localFiniteCasimirGapEvidencePromotesRealQuotient
    canonicalU1RealYMCarrierHamiltonianDomainSymmetryFailClosedReceipt
  ≡
  false
u1RealYMLocalFiniteEvidenceDoesNotPromoteRealQuotient =
  refl

u1RealYMContinuumClayFalse :
  continuumClayMassGapPromoted
    canonicalU1RealYMCarrierHamiltonianDomainSymmetryFailClosedReceipt
  ≡
  false
u1RealYMContinuumClayFalse =
  refl

data U1RealYMFriedrichsHaltPoint : Set where
  haltsAtFriedrichsRealAnalysisSelfAdjointExtension :
    U1RealYMFriedrichsHaltPoint

record U1YMQuotientCarrierHamiltonianShapeSymmetryAttemptReceipt : Setω where
  field
    quotientCarrierShape :
      RealYMCarrierQuotient

    quotientCarrierShapeIsCanonical :
      Bool

    quotientCarrierShapeIsCanonicalIsTrue :
      quotientCarrierShapeIsCanonical ≡ true

    hamiltonianShape :
      SelfAdjointYangMillsHamiltonianOnCarrierQuotientCarrierShape

    hamiltonianShapeIsCanonical :
      Bool

    hamiltonianShapeIsCanonicalIsTrue :
      hamiltonianShapeIsCanonical ≡ true

    ymQuotientCarrierName :
      String

    ymQuotientCarrierNameIsYMQuotientCarrier :
      ymQuotientCarrierName
      ≡
      "YMQuotientCarrier"

    ymHamiltonianShapeName :
      String

    ymHamiltonianShapeNameIsYMHamiltonianShape :
      ymHamiltonianShapeName
      ≡
      "YMHamiltonianShape"

    gaugeOrbitEquivalenceAttempted :
      Bool

    gaugeOrbitEquivalenceAttemptedIsTrue :
      gaugeOrbitEquivalenceAttempted ≡ true

    gaugeOrbitEquivalenceConstructed :
      Bool

    gaugeOrbitEquivalenceConstructedIsFalse :
      gaugeOrbitEquivalenceConstructed ≡ false

    hamiltonianShapeAttempted :
      Bool

    hamiltonianShapeAttemptedIsTrue :
      hamiltonianShapeAttempted ≡ true

    hamiltonianOperatorConstructed :
      Bool

    hamiltonianOperatorConstructedIsFalse :
      hamiltonianOperatorConstructed ≡ false

    symmetryAttempted :
      Bool

    symmetryAttemptedIsTrue :
      symmetryAttempted ≡ true

    symmetryOnDomainConstructed :
      Bool

    symmetryOnDomainConstructedIsFalse :
      symmetryOnDomainConstructed ≡ false

    friedrichsRealAnalysisHalt :
      U1RealYMFriedrichsHaltPoint

    friedrichsRealAnalysisHaltIsCanonical :
      friedrichsRealAnalysisHalt
      ≡
      haltsAtFriedrichsRealAnalysisSelfAdjointExtension

    exactFirstMissing :
      S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    exactFirstMissingIsSelfAdjointYangMillsHamiltonianOnCarrierQuotient :
      exactFirstMissing
      ≡
      missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    hardExternalHalt :
      S8RealCarrierHardExternalHalt

    hardExternalHaltIsUniformBalabanOrAgawa :
      hardExternalHalt
      ≡
      uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    realSelfAdjointnessConstructed :
      Bool

    realSelfAdjointnessConstructedIsFalse :
      realSelfAdjointnessConstructed ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    haltBoundary :
      List String

open U1YMQuotientCarrierHamiltonianShapeSymmetryAttemptReceipt public

canonicalU1YMQuotientCarrierHamiltonianShapeSymmetryAttemptReceipt :
  U1YMQuotientCarrierHamiltonianShapeSymmetryAttemptReceipt
canonicalU1YMQuotientCarrierHamiltonianShapeSymmetryAttemptReceipt =
  record
    { quotientCarrierShape =
        canonicalRealYMCarrierQuotient
    ; quotientCarrierShapeIsCanonical =
        true
    ; quotientCarrierShapeIsCanonicalIsTrue =
        refl
    ; hamiltonianShape =
        canonicalSelfAdjointYangMillsHamiltonianOnCarrierQuotientCarrierShape
    ; hamiltonianShapeIsCanonical =
        true
    ; hamiltonianShapeIsCanonicalIsTrue =
        refl
    ; ymQuotientCarrierName =
        "YMQuotientCarrier"
    ; ymQuotientCarrierNameIsYMQuotientCarrier =
        refl
    ; ymHamiltonianShapeName =
        "YMHamiltonianShape"
    ; ymHamiltonianShapeNameIsYMHamiltonianShape =
        refl
    ; gaugeOrbitEquivalenceAttempted =
        true
    ; gaugeOrbitEquivalenceAttemptedIsTrue =
        refl
    ; gaugeOrbitEquivalenceConstructed =
        false
    ; gaugeOrbitEquivalenceConstructedIsFalse =
        refl
    ; hamiltonianShapeAttempted =
        true
    ; hamiltonianShapeAttemptedIsTrue =
        refl
    ; hamiltonianOperatorConstructed =
        false
    ; hamiltonianOperatorConstructedIsFalse =
        refl
    ; symmetryAttempted =
        true
    ; symmetryAttemptedIsTrue =
        refl
    ; symmetryOnDomainConstructed =
        false
    ; symmetryOnDomainConstructedIsFalse =
        refl
    ; friedrichsRealAnalysisHalt =
        haltsAtFriedrichsRealAnalysisSelfAdjointExtension
    ; friedrichsRealAnalysisHaltIsCanonical =
        refl
    ; exactFirstMissing =
        missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; exactFirstMissingIsSelfAdjointYangMillsHamiltonianOnCarrierQuotient =
        refl
    ; hardExternalHalt =
        uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; hardExternalHaltIsUniformBalabanOrAgawa =
        refl
    ; realSelfAdjointnessConstructed =
        false
    ; realSelfAdjointnessConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; haltBoundary =
        "u1 names the attempted quotient carrier as YMQuotientCarrier and keeps it at the RealYMCarrierQuotient target shape"
        ∷ "Gauge-orbit equivalence is attempted but not constructed as a real binary quotient relation"
        ∷ "u1 names the attempted Hamiltonian carrier as YMHamiltonianShape and keeps it at the target shape for H_YM"
        ∷ "The symmetry attempt halts before a dense real-analysis domain and before a Friedrichs extension or essential-self-adjointness theorem"
        ∷ "The exact first missing theorem remains missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient"
        ∷ "UniformBalaban-or-AgawaIRFixedPoint remains the hard external halt for real-carrier promotion"
        ∷ "No spectral gap, continuum Clay theorem, SI authority, or terminal claim is promoted"
        ∷ []
    }

data U1RealYMQuotientHamiltonianNextBlocker : Set where
  missingRealGaugeOrbitEquivalence :
    U1RealYMQuotientHamiltonianNextBlocker

  missingQuotientNormIndependence :
    U1RealYMQuotientHamiltonianNextBlocker

  missingDenseDomainAndHamiltonianSymmetry :
    U1RealYMQuotientHamiltonianNextBlocker

  missingFriedrichsOrSelfAdjointExtension :
    U1RealYMQuotientHamiltonianNextBlocker

  missingFiniteCasimirGapToContinuumClayUniformBalaban :
    U1RealYMQuotientHamiltonianNextBlocker

canonicalU1RealYMQuotientHamiltonianNextBlockers :
  List U1RealYMQuotientHamiltonianNextBlocker
canonicalU1RealYMQuotientHamiltonianNextBlockers =
  missingRealGaugeOrbitEquivalence
  ∷ missingQuotientNormIndependence
  ∷ missingDenseDomainAndHamiltonianSymmetry
  ∷ missingFriedrichsOrSelfAdjointExtension
  ∷ missingFiniteCasimirGapToContinuumClayUniformBalaban
  ∷ []

record U1RealYMQuotientHamiltonianNextBlockerSurface : Setω where
  field
    priorAttempt :
      U1YMQuotientCarrierHamiltonianShapeSymmetryAttemptReceipt

    priorAttemptIsCanonical :
      Bool

    priorAttemptIsCanonicalIsTrue :
      priorAttemptIsCanonical ≡ true

    quotientCarrierShape :
      RealYMCarrierQuotient

    quotientCarrierShapeIsCanonical :
      Bool

    quotientCarrierShapeIsCanonicalIsTrue :
      quotientCarrierShapeIsCanonical ≡ true

    hamiltonianShape :
      SelfAdjointYangMillsHamiltonianOnCarrierQuotientCarrierShape

    hamiltonianShapeIsCanonical :
      Bool

    hamiltonianShapeIsCanonicalIsTrue :
      hamiltonianShapeIsCanonical ≡ true

    orderedBlockers :
      List U1RealYMQuotientHamiltonianNextBlocker

    orderedBlockersAreCanonical :
      orderedBlockers
      ≡
      canonicalU1RealYMQuotientHamiltonianNextBlockers

    firstBlocker :
      U1RealYMQuotientHamiltonianNextBlocker

    firstBlockerIsRealGaugeOrbitEquivalence :
      firstBlocker
      ≡
      missingRealGaugeOrbitEquivalence

    firstGlobalCarrierMissing :
      S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    firstGlobalCarrierMissingIsSelfAdjointYangMillsHamiltonian :
      firstGlobalCarrierMissing
      ≡
      missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    realGaugeOrbitEquivalenceConstructed :
      Bool

    realGaugeOrbitEquivalenceConstructedIsFalse :
      realGaugeOrbitEquivalenceConstructed ≡ false

    quotientNormIndependentOfRepresentative :
      Bool

    quotientNormIndependentOfRepresentativeIsFalse :
      quotientNormIndependentOfRepresentative ≡ false

    denseDomainConstructed :
      Bool

    denseDomainConstructedIsFalse :
      denseDomainConstructed ≡ false

    symmetricOnDenseDomainConstructed :
      Bool

    symmetricOnDenseDomainConstructedIsFalse :
      symmetricOnDenseDomainConstructed ≡ false

    friedrichsExtensionConstructed :
      Bool

    friedrichsExtensionConstructedIsFalse :
      friedrichsExtensionConstructed ≡ false

    selfAdjointExtensionConstructed :
      Bool

    selfAdjointExtensionConstructedIsFalse :
      selfAdjointExtensionConstructed ≡ false

    finiteCasimirGapTransportedToContinuum :
      Bool

    finiteCasimirGapTransportedToContinuumIsFalse :
      finiteCasimirGapTransportedToContinuum ≡ false

    uniformBalabanOrAgawaDischarged :
      Bool

    uniformBalabanOrAgawaDischargedIsFalse :
      uniformBalabanOrAgawaDischarged ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    blockerBoundary :
      List String

open U1RealYMQuotientHamiltonianNextBlockerSurface public

canonicalU1RealYMQuotientHamiltonianNextBlockerSurface :
  U1RealYMQuotientHamiltonianNextBlockerSurface
canonicalU1RealYMQuotientHamiltonianNextBlockerSurface =
  record
    { priorAttempt =
        canonicalU1YMQuotientCarrierHamiltonianShapeSymmetryAttemptReceipt
    ; priorAttemptIsCanonical =
        true
    ; priorAttemptIsCanonicalIsTrue =
        refl
    ; quotientCarrierShape =
        canonicalRealYMCarrierQuotient
    ; quotientCarrierShapeIsCanonical =
        true
    ; quotientCarrierShapeIsCanonicalIsTrue =
        refl
    ; hamiltonianShape =
        canonicalSelfAdjointYangMillsHamiltonianOnCarrierQuotientCarrierShape
    ; hamiltonianShapeIsCanonical =
        true
    ; hamiltonianShapeIsCanonicalIsTrue =
        refl
    ; orderedBlockers =
        canonicalU1RealYMQuotientHamiltonianNextBlockers
    ; orderedBlockersAreCanonical =
        refl
    ; firstBlocker =
        missingRealGaugeOrbitEquivalence
    ; firstBlockerIsRealGaugeOrbitEquivalence =
        refl
    ; firstGlobalCarrierMissing =
        missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; firstGlobalCarrierMissingIsSelfAdjointYangMillsHamiltonian =
        refl
    ; realGaugeOrbitEquivalenceConstructed =
        false
    ; realGaugeOrbitEquivalenceConstructedIsFalse =
        refl
    ; quotientNormIndependentOfRepresentative =
        false
    ; quotientNormIndependentOfRepresentativeIsFalse =
        refl
    ; denseDomainConstructed =
        false
    ; denseDomainConstructedIsFalse =
        refl
    ; symmetricOnDenseDomainConstructed =
        false
    ; symmetricOnDenseDomainConstructedIsFalse =
        refl
    ; friedrichsExtensionConstructed =
        false
    ; friedrichsExtensionConstructedIsFalse =
        refl
    ; selfAdjointExtensionConstructed =
        false
    ; selfAdjointExtensionConstructedIsFalse =
        refl
    ; finiteCasimirGapTransportedToContinuum =
        false
    ; finiteCasimirGapTransportedToContinuumIsFalse =
        refl
    ; uniformBalabanOrAgawaDischarged =
        false
    ; uniformBalabanOrAgawaDischargedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; blockerBoundary =
        "After the U1 quotient/Hamiltonian shape receipt, the first local blocker is a real gauge-orbit equivalence relation"
        ∷ "A quotient norm independent of representative cannot be stated as discharged before that relation is built"
        ∷ "Dense real-analysis Hamiltonian domain and symmetry remain later blockers, not constructed facts"
        ∷ "Friedrichs extension, essential self-adjointness, and self-adjoint extension remain absent"
        ∷ "Finite Casimir-style gap evidence is not transported to continuum Clay or UniformBalaban/Agawa authority"
        ∷ "No self-adjoint Yang-Mills Hamiltonian, continuum Clay theorem, or terminal promotion is constructed"
        ∷ []
    }

u1RealYMNextBlockerIsGaugeOrbitEquivalence :
  firstBlocker canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
  ≡
  missingRealGaugeOrbitEquivalence
u1RealYMNextBlockerIsGaugeOrbitEquivalence =
  refl

u1RealYMNextBlockerSurfaceDoesNotPromoteClay :
  continuumClayMassGapPromoted
    canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
  ≡
  false
u1RealYMNextBlockerSurfaceDoesNotPromoteClay =
  refl

data U1Gate2S8RealYMQuotientNormDependencyStatus : Set where
  gate2QuotientNormBlockedByDoubledChristoffelIntegralMetricCompatibility :
    U1Gate2S8RealYMQuotientNormDependencyStatus

data U1Gate2S8RealYMQuotientNormDependencyField : Set where
  gate2RealYMQuotientNormIndependenceField :
    U1Gate2S8RealYMQuotientNormDependencyField

  gate2GaugeInvariantRepresentativeNormField :
    U1Gate2S8RealYMQuotientNormDependencyField

  gate2DoubledChristoffelCancellationField :
    U1Gate2S8RealYMQuotientNormDependencyField

  gate2IntegralMetricCompatibilityField :
    U1Gate2S8RealYMQuotientNormDependencyField

  gate2RealYMQuotientNormPromotionBoundaryField :
    U1Gate2S8RealYMQuotientNormDependencyField

canonicalU1Gate2S8RealYMQuotientNormDependencyFields :
  List U1Gate2S8RealYMQuotientNormDependencyField
canonicalU1Gate2S8RealYMQuotientNormDependencyFields =
  gate2RealYMQuotientNormIndependenceField
  ∷ gate2GaugeInvariantRepresentativeNormField
  ∷ gate2DoubledChristoffelCancellationField
  ∷ gate2IntegralMetricCompatibilityField
  ∷ gate2RealYMQuotientNormPromotionBoundaryField
  ∷ []

record U1Gate2S8RealYMQuotientNormDependencyReceipt : Setω where
  field
    status :
      U1Gate2S8RealYMQuotientNormDependencyStatus

    priorBlockerSurface :
      U1RealYMQuotientHamiltonianNextBlockerSurface

    priorBlockerSurfaceIsCanonical :
      Bool

    priorBlockerSurfaceIsCanonicalIsTrue :
      priorBlockerSurfaceIsCanonical ≡ true

    realYMCarrierQuotient :
      RealYMCarrierQuotient

    realYMCarrierQuotientIsCanonical :
      Bool

    realYMCarrierQuotientIsCanonicalIsTrue :
      realYMCarrierQuotientIsCanonical ≡ true

    gateName :
      String

    gateNameIsGate2 :
      gateName
      ≡
      "Gate 2"

    dependencyFields :
      List U1Gate2S8RealYMQuotientNormDependencyField

    dependencyFieldsAreCanonical :
      dependencyFields
      ≡
      canonicalU1Gate2S8RealYMQuotientNormDependencyFields

    quotientNormMissingAPI :
      S8RealYMCarrierQuotientShapeMissingAPI

    quotientNormMissingAPIIsGaugeInvariantNorm :
      quotientNormMissingAPI
      ≡
      missingGaugeInvariantRealQuotientNormAPI

    quotientNormNextBlocker :
      U1RealYMQuotientHamiltonianNextBlocker

    quotientNormNextBlockerIsNormIndependence :
      quotientNormNextBlocker
      ≡
      missingQuotientNormIndependence

    boundedToPressureBelow15SpectralTheoremObstruction :
      Bool

    boundedToPressureBelow15SpectralTheoremObstructionIsTrue :
      boundedToPressureBelow15SpectralTheoremObstruction ≡ true

    touchesGRFiles :
      Bool

    touchesGRFilesIsFalse :
      touchesGRFiles ≡ false

    importsGRReceipt :
      Bool

    importsGRReceiptIsFalse :
      importsGRReceipt ≡ false

    doubledChristoffelDependencyRecorded :
      Bool

    doubledChristoffelDependencyRecordedIsTrue :
      doubledChristoffelDependencyRecorded ≡ true

    integralMetricCompatibilityDependencyRecorded :
      Bool

    integralMetricCompatibilityDependencyRecordedIsTrue :
      integralMetricCompatibilityDependencyRecorded ≡ true

    doubledChristoffelCancellationConstructed :
      Bool

    doubledChristoffelCancellationConstructedIsFalse :
      doubledChristoffelCancellationConstructed ≡ false

    integralMetricCompatibilityConstructed :
      Bool

    integralMetricCompatibilityConstructedIsFalse :
      integralMetricCompatibilityConstructed ≡ false

    quotientNormIndependentOfRepresentative :
      Bool

    quotientNormIndependentOfRepresentativeIsFalse :
      quotientNormIndependentOfRepresentative ≡ false

    gaugeInvariantQuotientNormConstructed :
      Bool

    gaugeInvariantQuotientNormConstructedIsFalse :
      gaugeInvariantQuotientNormConstructed ≡ false

    realYMCarrierQuotientPromoted :
      Bool

    realYMCarrierQuotientPromotedIsFalse :
      realYMCarrierQuotientPromoted ≡ false

    selfAdjointHamiltonianConstructed :
      Bool

    selfAdjointHamiltonianConstructedIsFalse :
      selfAdjointHamiltonianConstructed ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    receiptBoundary :
      List String

open U1Gate2S8RealYMQuotientNormDependencyReceipt public

canonicalU1Gate2S8RealYMQuotientNormDependencyReceipt :
  U1Gate2S8RealYMQuotientNormDependencyReceipt
canonicalU1Gate2S8RealYMQuotientNormDependencyReceipt =
  record
    { status =
        gate2QuotientNormBlockedByDoubledChristoffelIntegralMetricCompatibility
    ; priorBlockerSurface =
        canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; priorBlockerSurfaceIsCanonical =
        true
    ; priorBlockerSurfaceIsCanonicalIsTrue =
        refl
    ; realYMCarrierQuotient =
        canonicalRealYMCarrierQuotient
    ; realYMCarrierQuotientIsCanonical =
        true
    ; realYMCarrierQuotientIsCanonicalIsTrue =
        refl
    ; gateName =
        "Gate 2"
    ; gateNameIsGate2 =
        refl
    ; dependencyFields =
        canonicalU1Gate2S8RealYMQuotientNormDependencyFields
    ; dependencyFieldsAreCanonical =
        refl
    ; quotientNormMissingAPI =
        missingGaugeInvariantRealQuotientNormAPI
    ; quotientNormMissingAPIIsGaugeInvariantNorm =
        refl
    ; quotientNormNextBlocker =
        missingQuotientNormIndependence
    ; quotientNormNextBlockerIsNormIndependence =
        refl
    ; boundedToPressureBelow15SpectralTheoremObstruction =
        true
    ; boundedToPressureBelow15SpectralTheoremObstructionIsTrue =
        refl
    ; touchesGRFiles =
        false
    ; touchesGRFilesIsFalse =
        refl
    ; importsGRReceipt =
        false
    ; importsGRReceiptIsFalse =
        refl
    ; doubledChristoffelDependencyRecorded =
        true
    ; doubledChristoffelDependencyRecordedIsTrue =
        refl
    ; integralMetricCompatibilityDependencyRecorded =
        true
    ; integralMetricCompatibilityDependencyRecordedIsTrue =
        refl
    ; doubledChristoffelCancellationConstructed =
        false
    ; doubledChristoffelCancellationConstructedIsFalse =
        refl
    ; integralMetricCompatibilityConstructed =
        false
    ; integralMetricCompatibilityConstructedIsFalse =
        refl
    ; quotientNormIndependentOfRepresentative =
        false
    ; quotientNormIndependentOfRepresentativeIsFalse =
        refl
    ; gaugeInvariantQuotientNormConstructed =
        false
    ; gaugeInvariantQuotientNormConstructedIsFalse =
        refl
    ; realYMCarrierQuotientPromoted =
        false
    ; realYMCarrierQuotientPromotedIsFalse =
        refl
    ; selfAdjointHamiltonianConstructed =
        false
    ; selfAdjointHamiltonianConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; receiptBoundary =
        "u1 Gate 2 records the S8 real YM quotient-norm side only"
        ∷ "The current quotient-norm dependency is doubled-Christoffel cancellation plus integral metric compatibility"
        ∷ "This bounded receipt does not import a GR receipt and records touchesGRFiles=false"
        ∷ "The dependency is recorded as a blocker for gauge-invariant representative norm independence, not as a constructed metric-compatibility theorem"
        ∷ "No real YM quotient norm, self-adjoint Hamiltonian, S8 spectral gap, continuum Clay theorem, or terminal claim is promoted"
        ∷ []
    }

u1Gate2S8RealYMQuotientNormIntegralMetricCompatibilityStillMissing :
  integralMetricCompatibilityConstructed
    canonicalU1Gate2S8RealYMQuotientNormDependencyReceipt
  ≡
  false
u1Gate2S8RealYMQuotientNormIntegralMetricCompatibilityStillMissing =
  refl

u1Gate2S8RealYMQuotientNormNoTerminalPromotion :
  terminalClaimPromoted
    canonicalU1Gate2S8RealYMQuotientNormDependencyReceipt
  ≡
  false
u1Gate2S8RealYMQuotientNormNoTerminalPromotion =
  refl

record U1Gate2FiniteYMFormalDomainTerm : Set where
  field
    finiteDomainCoefficient :
      Nat

    finiteDomainRepresentative :
      YMConnectionCarrier.Connection canonicalFiniteSFGCSite2DYMConnectionCarrier

open U1Gate2FiniteYMFormalDomainTerm public

u1Gate2FiniteFormalDenseDomainCandidate : Set
u1Gate2FiniteFormalDenseDomainCandidate =
  List U1Gate2FiniteYMFormalDomainTerm

data U1Gate2DenseDomainHYMSymmetryMissingAPI : Set where
  u1MissingDenseDomainDensityAPI :
    U1Gate2DenseDomainHYMSymmetryMissingAPI

  u1MissingPhysicalQuotientInnerProductAPI :
    U1Gate2DenseDomainHYMSymmetryMissingAPI

  u1MissingConnectionLaplacianActionAPI :
    U1Gate2DenseDomainHYMSymmetryMissingAPI

  u1MissingPlaquettePotentialActionAPI :
    U1Gate2DenseDomainHYMSymmetryMissingAPI

  u1MissingLaplacianSymmetryProofAPI :
    U1Gate2DenseDomainHYMSymmetryMissingAPI

  u1MissingPlaquettePotentialSymmetryProofAPI :
    U1Gate2DenseDomainHYMSymmetryMissingAPI

  u1MissingFriedrichsSelfAdjointExtensionAPI :
    U1Gate2DenseDomainHYMSymmetryMissingAPI

canonicalU1Gate2DenseDomainHYMSymmetryMissingAPIs :
  List U1Gate2DenseDomainHYMSymmetryMissingAPI
canonicalU1Gate2DenseDomainHYMSymmetryMissingAPIs =
  u1MissingDenseDomainDensityAPI
  ∷ u1MissingPhysicalQuotientInnerProductAPI
  ∷ u1MissingConnectionLaplacianActionAPI
  ∷ u1MissingPlaquettePotentialActionAPI
  ∷ u1MissingLaplacianSymmetryProofAPI
  ∷ u1MissingPlaquettePotentialSymmetryProofAPI
  ∷ u1MissingFriedrichsSelfAdjointExtensionAPI
  ∷ []

record U1Gate2DenseDomainHYMSymmetryFailClosedReceipt : Setω where
  field
    u1Gate2DenseSymmetryPriorNormReceipt :
      U1Gate2S8RealYMQuotientNormDependencyReceipt

    u1Gate2DenseSymmetryPriorNormReceiptIsCanonical :
      Bool

    u1Gate2DenseSymmetryPriorNormReceiptIsCanonical-v :
      u1Gate2DenseSymmetryPriorNormReceiptIsCanonical ≡ true

    u1Gate2DenseSymmetryHamiltonianShape :
      YMHamiltonianShape
        canonicalFiniteSFGCSite2DYMConnectionCarrier
        canonicalFiniteSFGCSite2DYMQuotientCarrierShape

    u1Gate2DenseSymmetryHamiltonianShapeIsCanonical :
      Bool

    u1Gate2DenseSymmetryHamiltonianShapeIsCanonical-v :
      u1Gate2DenseSymmetryHamiltonianShapeIsCanonical ≡ true

    u1Gate2FiniteFormalDomainCandidate :
      Set

    u1Gate2FiniteFormalDomainCandidateIsConnectionList :
      u1Gate2FiniteFormalDomainCandidate
      ≡
      u1Gate2FiniteFormalDenseDomainCandidate

    u1Gate2HYMActionTarget :
      Set

    u1Gate2HYMActionTargetIsConnectionEndomap :
      u1Gate2HYMActionTarget
      ≡
      (YMConnectionCarrier.Connection canonicalFiniteSFGCSite2DYMConnectionCarrier →
       YMConnectionCarrier.Connection canonicalFiniteSFGCSite2DYMConnectionCarrier)

    u1Gate2HYMInnerProductTarget :
      Set

    u1Gate2HYMInnerProductTargetIsRealValuedPairing :
      u1Gate2HYMInnerProductTarget
      ≡
      (YMConnectionCarrier.Connection canonicalFiniteSFGCSite2DYMConnectionCarrier →
       YMConnectionCarrier.Connection canonicalFiniteSFGCSite2DYMConnectionCarrier →
       RA.ℝ)

    u1Gate2HYMSymmetryTarget :
      Set₁

    u1Gate2HYMSymmetryTargetIsBinaryEqualityTarget :
      u1Gate2HYMSymmetryTarget
      ≡
      (YMConnectionCarrier.Connection canonicalFiniteSFGCSite2DYMConnectionCarrier →
       YMConnectionCarrier.Connection canonicalFiniteSFGCSite2DYMConnectionCarrier →
       Set)

    u1Gate2DenseDomainAttempted :
      Bool

    u1Gate2DenseDomainAttempted-v :
      u1Gate2DenseDomainAttempted ≡ true

    u1Gate2FiniteFormalDomainCandidateConstructed :
      Bool

    u1Gate2FiniteFormalDomainCandidateConstructed-v :
      u1Gate2FiniteFormalDomainCandidateConstructed ≡ true

    u1Gate2DenseDomainDensityConstructed :
      Bool

    u1Gate2DenseDomainDensityConstructed-v :
      u1Gate2DenseDomainDensityConstructed ≡ false

    u1Gate2HYMActionConstructed :
      Bool

    u1Gate2HYMActionConstructed-v :
      u1Gate2HYMActionConstructed ≡ false

    u1Gate2PhysicalQuotientInnerProductConstructed :
      Bool

    u1Gate2PhysicalQuotientInnerProductConstructed-v :
      u1Gate2PhysicalQuotientInnerProductConstructed ≡ false

    u1Gate2LaplacianSymmetryConstructed :
      Bool

    u1Gate2LaplacianSymmetryConstructed-v :
      u1Gate2LaplacianSymmetryConstructed ≡ false

    u1Gate2PotentialSymmetryConstructed :
      Bool

    u1Gate2PotentialSymmetryConstructed-v :
      u1Gate2PotentialSymmetryConstructed ≡ false

    u1Gate2HYMSymmetryConstructed :
      Bool

    u1Gate2HYMSymmetryConstructed-v :
      u1Gate2HYMSymmetryConstructed ≡ false

    u1Gate2FriedrichsSelfAdjointHalt :
      U1RealYMFriedrichsHaltPoint

    u1Gate2FriedrichsSelfAdjointHalt-v :
      u1Gate2FriedrichsSelfAdjointHalt
      ≡
      haltsAtFriedrichsRealAnalysisSelfAdjointExtension

    u1Gate2DenseSymmetryMissingAPIs :
      List U1Gate2DenseDomainHYMSymmetryMissingAPI

    u1Gate2DenseSymmetryMissingAPIsAreCanonical :
      u1Gate2DenseSymmetryMissingAPIs
      ≡
      canonicalU1Gate2DenseDomainHYMSymmetryMissingAPIs

    u1Gate2DenseSymmetryFirstMissingAPI :
      U1Gate2DenseDomainHYMSymmetryMissingAPI

    u1Gate2DenseSymmetryFirstMissingAPI-v :
      u1Gate2DenseSymmetryFirstMissingAPI
      ≡
      u1MissingDenseDomainDensityAPI

    u1Gate2DenseSymmetryExactGlobalBlocker :
      S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    u1Gate2DenseSymmetryExactGlobalBlocker-v :
      u1Gate2DenseSymmetryExactGlobalBlocker
      ≡
      missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    u1Gate2DenseSymmetryHardExternalHalt :
      S8RealCarrierHardExternalHalt

    u1Gate2DenseSymmetryHardExternalHalt-v :
      u1Gate2DenseSymmetryHardExternalHalt
      ≡
      uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    u1Gate2RealYMPromoted :
      Bool

    u1Gate2RealYMPromoted-v :
      u1Gate2RealYMPromoted ≡ false

    u1Gate2SpectralGapPromoted :
      Bool

    u1Gate2SpectralGapPromoted-v :
      u1Gate2SpectralGapPromoted ≡ false

    u1Gate2ContinuumClayPromoted :
      Bool

    u1Gate2ContinuumClayPromoted-v :
      u1Gate2ContinuumClayPromoted ≡ false

    u1Gate2TerminalPromoted :
      Bool

    u1Gate2TerminalPromoted-v :
      u1Gate2TerminalPromoted ≡ false

    u1Gate2DenseSymmetryBoundary :
      List String

open U1Gate2DenseDomainHYMSymmetryFailClosedReceipt public

canonicalU1Gate2DenseDomainHYMSymmetryFailClosedReceipt :
  U1Gate2DenseDomainHYMSymmetryFailClosedReceipt
canonicalU1Gate2DenseDomainHYMSymmetryFailClosedReceipt =
  record
    { u1Gate2DenseSymmetryPriorNormReceipt =
        canonicalU1Gate2S8RealYMQuotientNormDependencyReceipt
    ; u1Gate2DenseSymmetryPriorNormReceiptIsCanonical =
        true
    ; u1Gate2DenseSymmetryPriorNormReceiptIsCanonical-v =
        refl
    ; u1Gate2DenseSymmetryHamiltonianShape =
        canonicalFiniteSFGCSite2DYMHamiltonianShape
    ; u1Gate2DenseSymmetryHamiltonianShapeIsCanonical =
        true
    ; u1Gate2DenseSymmetryHamiltonianShapeIsCanonical-v =
        refl
    ; u1Gate2FiniteFormalDomainCandidate =
        u1Gate2FiniteFormalDenseDomainCandidate
    ; u1Gate2FiniteFormalDomainCandidateIsConnectionList =
        refl
    ; u1Gate2HYMActionTarget =
        SFGC.SFGCSite2DDiscrete1Form →
        SFGC.SFGCSite2DDiscrete1Form
    ; u1Gate2HYMActionTargetIsConnectionEndomap =
        refl
    ; u1Gate2HYMInnerProductTarget =
        SFGC.SFGCSite2DDiscrete1Form →
        SFGC.SFGCSite2DDiscrete1Form →
        RA.ℝ
    ; u1Gate2HYMInnerProductTargetIsRealValuedPairing =
        refl
    ; u1Gate2HYMSymmetryTarget =
        SFGC.SFGCSite2DDiscrete1Form →
        SFGC.SFGCSite2DDiscrete1Form →
        Set
    ; u1Gate2HYMSymmetryTargetIsBinaryEqualityTarget =
        refl
    ; u1Gate2DenseDomainAttempted =
        true
    ; u1Gate2DenseDomainAttempted-v =
        refl
    ; u1Gate2FiniteFormalDomainCandidateConstructed =
        true
    ; u1Gate2FiniteFormalDomainCandidateConstructed-v =
        refl
    ; u1Gate2DenseDomainDensityConstructed =
        false
    ; u1Gate2DenseDomainDensityConstructed-v =
        refl
    ; u1Gate2HYMActionConstructed =
        false
    ; u1Gate2HYMActionConstructed-v =
        refl
    ; u1Gate2PhysicalQuotientInnerProductConstructed =
        false
    ; u1Gate2PhysicalQuotientInnerProductConstructed-v =
        refl
    ; u1Gate2LaplacianSymmetryConstructed =
        false
    ; u1Gate2LaplacianSymmetryConstructed-v =
        refl
    ; u1Gate2PotentialSymmetryConstructed =
        false
    ; u1Gate2PotentialSymmetryConstructed-v =
        refl
    ; u1Gate2HYMSymmetryConstructed =
        false
    ; u1Gate2HYMSymmetryConstructed-v =
        refl
    ; u1Gate2FriedrichsSelfAdjointHalt =
        haltsAtFriedrichsRealAnalysisSelfAdjointExtension
    ; u1Gate2FriedrichsSelfAdjointHalt-v =
        refl
    ; u1Gate2DenseSymmetryMissingAPIs =
        canonicalU1Gate2DenseDomainHYMSymmetryMissingAPIs
    ; u1Gate2DenseSymmetryMissingAPIsAreCanonical =
        refl
    ; u1Gate2DenseSymmetryFirstMissingAPI =
        u1MissingDenseDomainDensityAPI
    ; u1Gate2DenseSymmetryFirstMissingAPI-v =
        refl
    ; u1Gate2DenseSymmetryExactGlobalBlocker =
        missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; u1Gate2DenseSymmetryExactGlobalBlocker-v =
        refl
    ; u1Gate2DenseSymmetryHardExternalHalt =
        uniformBalabanOrAgawaIRFixedPointForMissingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; u1Gate2DenseSymmetryHardExternalHalt-v =
        refl
    ; u1Gate2RealYMPromoted =
        false
    ; u1Gate2RealYMPromoted-v =
        refl
    ; u1Gate2SpectralGapPromoted =
        false
    ; u1Gate2SpectralGapPromoted-v =
        refl
    ; u1Gate2ContinuumClayPromoted =
        false
    ; u1Gate2ContinuumClayPromoted-v =
        refl
    ; u1Gate2TerminalPromoted =
        false
    ; u1Gate2TerminalPromoted-v =
        refl
    ; u1Gate2DenseSymmetryBoundary =
        "u1 attempted the requested dense-domain and H_YM symmetry lane over the existing finite quotient staging"
        ∷ "The only concrete term added here is a finite formal-domain candidate: List U1Gate2FiniteYMFormalDomainTerm over the finite SFGCSite2D connection carrier"
        ∷ "The file still lacks exact APIs for density in a physical quotient Hilbert space, the quotient inner product, the connection Laplacian action, and the plaquette potential action"
        ∷ "Therefore laplacian symmetry, potential symmetry, and H_YM symmetry on a dense real domain are recorded as missing, not constructed"
        ∷ "The route halts at Friedrichs/self-adjoint extension and at missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient"
        ∷ "No real YM, spectral gap, continuum Clay, or terminal promotion is made"
        ∷ []
    }

u1Gate2DenseDomainHYMSymmetryStillMissing :
  u1Gate2HYMSymmetryConstructed
    canonicalU1Gate2DenseDomainHYMSymmetryFailClosedReceipt
  ≡
  false
u1Gate2DenseDomainHYMSymmetryStillMissing =
  refl

u1Gate2DenseDomainHYMSymmetryNoTerminalPromotion :
  u1Gate2TerminalPromoted
    canonicalU1Gate2DenseDomainHYMSymmetryFailClosedReceipt
  ≡
  false
u1Gate2DenseDomainHYMSymmetryNoTerminalPromotion =
  refl

record U1ConditionalFiniteCarrierSpectralBoundReceipt : Setω where
  field
    realYMAttemptReceiptName :
      String

    realYMAttemptReceiptNameIsCanonical :
      realYMAttemptReceiptName
      ≡
      "canonicalU1RealYMCarrierHamiltonianDomainSymmetryFailClosedReceipt"

    realYMAttemptReceiptAvailable :
      Bool

    realYMAttemptReceiptAvailableIsTrue :
      realYMAttemptReceiptAvailable ≡ true

    finiteCarrierSourceName :
      String

    finiteCarrierSourceNameIsST3 :
      finiteCarrierSourceName
      ≡
      "canonicalST3DepthRecursionMonotonicityReceipt"

    finiteCarrierSourceAvailable :
      Bool

    finiteCarrierSourceAvailableIsTrue :
      finiteCarrierSourceAvailable ≡ true

    authorityBoundaryName :
      String

    authorityBoundaryNameIsU1Conditional :
      authorityBoundaryName
      ≡
      "canonicalU1ConditionalPreprintAuthorityBoundary"

    authorityBoundaryAvailable :
      Bool

    authorityBoundaryAvailableIsTrue :
      authorityBoundaryAvailable ≡ true

    localFiniteCarrierSpectralBoundAvailable :
      Bool

    localFiniteCarrierSpectralBoundAvailableIsTrue :
      localFiniteCarrierSpectralBoundAvailable ≡ true

    localFiniteCarrierBoundIsConditional :
      Bool

    localFiniteCarrierBoundIsConditionalIsTrue :
      localFiniteCarrierBoundIsConditional ≡ true

    finiteCarrierBoundTransportedToRealYM :
      Bool

    finiteCarrierBoundTransportedToRealYMIsFalse :
      finiteCarrierBoundTransportedToRealYM ≡ false

    realCarrierQuotientConstructed :
      Bool

    realCarrierQuotientConstructedIsFalse :
      realCarrierQuotientConstructed ≡ false

    hamiltonianOperatorConstructed :
      Bool

    hamiltonianOperatorConstructedIsFalse :
      hamiltonianOperatorConstructed ≡ false

    selfAdjointHamiltonianConstructed :
      Bool

    selfAdjointHamiltonianConstructedIsFalse :
      selfAdjointHamiltonianConstructed ≡ false

    firstRemainingBlocker :
      S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    firstRemainingBlockerIsSelfAdjointYangMillsHamiltonian :
      firstRemainingBlocker
      ≡
      missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    conditionalPreprintAuthorityAccepted :
      Bool

    conditionalPreprintAuthorityAcceptedIsFalse :
      conditionalPreprintAuthorityAccepted ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    receiptBoundary :
      List String

open U1ConditionalFiniteCarrierSpectralBoundReceipt public

canonicalU1ConditionalFiniteCarrierSpectralBoundReceipt :
  U1ConditionalFiniteCarrierSpectralBoundReceipt
canonicalU1ConditionalFiniteCarrierSpectralBoundReceipt =
  record
    { realYMAttemptReceiptName =
        "canonicalU1RealYMCarrierHamiltonianDomainSymmetryFailClosedReceipt"
    ; realYMAttemptReceiptNameIsCanonical =
        refl
    ; realYMAttemptReceiptAvailable =
        true
    ; realYMAttemptReceiptAvailableIsTrue =
        refl
    ; finiteCarrierSourceName =
        "canonicalST3DepthRecursionMonotonicityReceipt"
    ; finiteCarrierSourceNameIsST3 =
        refl
    ; finiteCarrierSourceAvailable =
        true
    ; finiteCarrierSourceAvailableIsTrue =
        refl
    ; authorityBoundaryName =
        "canonicalU1ConditionalPreprintAuthorityBoundary"
    ; authorityBoundaryNameIsU1Conditional =
        refl
    ; authorityBoundaryAvailable =
        true
    ; authorityBoundaryAvailableIsTrue =
        refl
    ; localFiniteCarrierSpectralBoundAvailable =
        true
    ; localFiniteCarrierSpectralBoundAvailableIsTrue =
        refl
    ; localFiniteCarrierBoundIsConditional =
        true
    ; localFiniteCarrierBoundIsConditionalIsTrue =
        refl
    ; finiteCarrierBoundTransportedToRealYM =
        false
    ; finiteCarrierBoundTransportedToRealYMIsFalse =
        refl
    ; realCarrierQuotientConstructed =
        false
    ; realCarrierQuotientConstructedIsFalse =
        refl
    ; hamiltonianOperatorConstructed =
        false
    ; hamiltonianOperatorConstructedIsFalse =
        refl
    ; selfAdjointHamiltonianConstructed =
        false
    ; selfAdjointHamiltonianConstructedIsFalse =
        refl
    ; firstRemainingBlocker =
        missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; firstRemainingBlockerIsSelfAdjointYangMillsHamiltonian =
        refl
    ; conditionalPreprintAuthorityAccepted =
        false
    ; conditionalPreprintAuthorityAcceptedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; receiptBoundary =
        "The finite-carrier spectral bound source is the local ST3 depth-recursion receipt"
        ∷ "This receipt is conditional and finite-carrier only"
        ∷ "It is not transported to a real Yang-Mills carrier quotient"
        ∷ "The real carrier quotient, Hamiltonian operator, and self-adjoint Hamiltonian remain unconstructed"
        ∷ "Agawa and related preprint inputs remain conditional under-review authority, not accepted Clay authority"
        ∷ "No S8 spectral-gap receipt, continuum Clay theorem, or terminal claim is promoted"
        ∷ []
    }

u1ConditionalFiniteCarrierBoundDoesNotTransportToRealYM :
  finiteCarrierBoundTransportedToRealYM
    canonicalU1ConditionalFiniteCarrierSpectralBoundReceipt
  ≡
  false
u1ConditionalFiniteCarrierBoundDoesNotTransportToRealYM =
  refl

u1ConditionalFiniteCarrierBoundTerminalFalse :
  terminalClaimPromoted canonicalU1ConditionalFiniteCarrierSpectralBoundReceipt
  ≡
  false
u1ConditionalFiniteCarrierBoundTerminalFalse =
  refl

data U1FiniteCasimirCanonicalMode : Set where
  u1CasimirVacuumMode :
    U1FiniteCasimirCanonicalMode

  u1CasimirUnitT1Mode :
    U1FiniteCasimirCanonicalMode

  u1CasimirUnitT2Mode :
    U1FiniteCasimirCanonicalMode

  u1CasimirUnitT3Mode :
    U1FiniteCasimirCanonicalMode

u1FiniteCasimirEigenvalue :
  U1FiniteCasimirCanonicalMode →
  Nat
u1FiniteCasimirEigenvalue u1CasimirVacuumMode =
  0
u1FiniteCasimirEigenvalue u1CasimirUnitT1Mode =
  1
u1FiniteCasimirEigenvalue u1CasimirUnitT2Mode =
  1
u1FiniteCasimirEigenvalue u1CasimirUnitT3Mode =
  1

record U1FiniteCasimirGapOneCanonicalModeReceipt : Setω where
  field
    u1FiniteCasimirCarrierShape :
      String

    u1FiniteCasimirCarrierShapeIsCanonical :
      u1FiniteCasimirCarrierShape
      ≡
      "canonical finite su2-like Casimir modes: vacuum, T1, T2, T3"

    u1FiniteCasimirGapValue :
      Nat

    u1FiniteCasimirGapValueIsOne :
      u1FiniteCasimirGapValue ≡ 1

    u1FiniteCasimirVacuumEigenvalue :
      Nat

    u1FiniteCasimirVacuumEigenvalueIsZero :
      u1FiniteCasimirVacuumEigenvalue ≡ 0

    u1FiniteCasimirUnitT1Eigenvalue :
      Nat

    u1FiniteCasimirUnitT1EigenvalueIsOne :
      u1FiniteCasimirUnitT1Eigenvalue ≡ 1

    u1FiniteCasimirUnitT2Eigenvalue :
      Nat

    u1FiniteCasimirUnitT2EigenvalueIsOne :
      u1FiniteCasimirUnitT2Eigenvalue ≡ 1

    u1FiniteCasimirUnitT3Eigenvalue :
      Nat

    u1FiniteCasimirUnitT3EigenvalueIsOne :
      u1FiniteCasimirUnitT3Eigenvalue ≡ 1

    u1FiniteCasimirCanonicalGapOneRecorded :
      Bool

    u1FiniteCasimirCanonicalGapOneRecordedIsTrue :
      u1FiniteCasimirCanonicalGapOneRecorded ≡ true

    u1FiniteCasimirNonzeroSquareLemmaName :
      String

    u1FiniteCasimirNonzeroSquareLemmaNameIsCanonical :
      u1FiniteCasimirNonzeroSquareLemmaName
      ≡
      "nonzero integer square is at least one"

    u1FiniteCasimirFullZ3LemmaConstructed :
      Bool

    u1FiniteCasimirFullZ3LemmaConstructedIsFalse :
      u1FiniteCasimirFullZ3LemmaConstructed ≡ false

    u1FiniteHYMSpectrumConstructed :
      Bool

    u1FiniteHYMSpectrumConstructedIsFalse :
      u1FiniteHYMSpectrumConstructed ≡ false

    u1FiniteCasimirDominatesPlaquetteHamiltonianConstructed :
      Bool

    u1FiniteCasimirDominatesPlaquetteHamiltonianConstructedIsFalse :
      u1FiniteCasimirDominatesPlaquetteHamiltonianConstructed ≡ false

    u1FiniteSpectralGapTheoremConstructed :
      Bool

    u1FiniteSpectralGapTheoremConstructedIsFalse :
      u1FiniteSpectralGapTheoremConstructed ≡ false

    u1RealSelfAdjointHYMConstructed :
      Bool

    u1RealSelfAdjointHYMConstructedIsFalse :
      u1RealSelfAdjointHYMConstructed ≡ false

    u1ContinuumClayMassGapPromoted :
      Bool

    u1ContinuumClayMassGapPromotedIsFalse :
      u1ContinuumClayMassGapPromoted ≡ false

    u1TerminalClaimPromoted :
      Bool

    u1TerminalClaimPromotedIsFalse :
      u1TerminalClaimPromoted ≡ false

    u1FiniteCasimirGapOneBoundary :
      List String

open U1FiniteCasimirGapOneCanonicalModeReceipt public

canonicalU1FiniteCasimirGapOneCanonicalModeReceipt :
  U1FiniteCasimirGapOneCanonicalModeReceipt
canonicalU1FiniteCasimirGapOneCanonicalModeReceipt =
  record
    { u1FiniteCasimirCarrierShape =
        "canonical finite su2-like Casimir modes: vacuum, T1, T2, T3"
    ; u1FiniteCasimirCarrierShapeIsCanonical =
        refl
    ; u1FiniteCasimirGapValue =
        1
    ; u1FiniteCasimirGapValueIsOne =
        refl
    ; u1FiniteCasimirVacuumEigenvalue =
        u1FiniteCasimirEigenvalue u1CasimirVacuumMode
    ; u1FiniteCasimirVacuumEigenvalueIsZero =
        refl
    ; u1FiniteCasimirUnitT1Eigenvalue =
        u1FiniteCasimirEigenvalue u1CasimirUnitT1Mode
    ; u1FiniteCasimirUnitT1EigenvalueIsOne =
        refl
    ; u1FiniteCasimirUnitT2Eigenvalue =
        u1FiniteCasimirEigenvalue u1CasimirUnitT2Mode
    ; u1FiniteCasimirUnitT2EigenvalueIsOne =
        refl
    ; u1FiniteCasimirUnitT3Eigenvalue =
        u1FiniteCasimirEigenvalue u1CasimirUnitT3Mode
    ; u1FiniteCasimirUnitT3EigenvalueIsOne =
        refl
    ; u1FiniteCasimirCanonicalGapOneRecorded =
        true
    ; u1FiniteCasimirCanonicalGapOneRecordedIsTrue =
        refl
    ; u1FiniteCasimirNonzeroSquareLemmaName =
        "nonzero integer square is at least one"
    ; u1FiniteCasimirNonzeroSquareLemmaNameIsCanonical =
        refl
    ; u1FiniteCasimirFullZ3LemmaConstructed =
        false
    ; u1FiniteCasimirFullZ3LemmaConstructedIsFalse =
        refl
    ; u1FiniteHYMSpectrumConstructed =
        false
    ; u1FiniteHYMSpectrumConstructedIsFalse =
        refl
    ; u1FiniteCasimirDominatesPlaquetteHamiltonianConstructed =
        false
    ; u1FiniteCasimirDominatesPlaquetteHamiltonianConstructedIsFalse =
        refl
    ; u1FiniteSpectralGapTheoremConstructed =
        false
    ; u1FiniteSpectralGapTheoremConstructedIsFalse =
        refl
    ; u1RealSelfAdjointHYMConstructed =
        false
    ; u1RealSelfAdjointHYMConstructedIsFalse =
        refl
    ; u1ContinuumClayMassGapPromoted =
        false
    ; u1ContinuumClayMassGapPromotedIsFalse =
        refl
    ; u1TerminalClaimPromoted =
        false
    ; u1TerminalClaimPromotedIsFalse =
        refl
    ; u1FiniteCasimirGapOneBoundary =
        "The canonical finite Casimir mode surface has numeric gapValue = 1"
        ∷ "The vacuum mode has Casimir eigenvalue 0 and each canonical unit T_i mode has eigenvalue 1"
        ∷ "This records the finite-mode arithmetic target for the nonzero-square >= 1 lemma"
        ∷ "The full Z^3 nonzero-square lemma, finite H_YM spectrum, and Casimir domination of the plaquette Hamiltonian are still absent"
        ∷ "Therefore this is numeric finite-mode progress, not a finite spectral-gap theorem for H_YM"
        ∷ "Real self-adjoint H_YM, continuum Clay mass gap, and terminal promotion remain false"
        ∷ []
    }

u1FiniteCasimirGapOneValueIsOne :
  u1FiniteCasimirGapValue
    canonicalU1FiniteCasimirGapOneCanonicalModeReceipt
  ≡
  1
u1FiniteCasimirGapOneValueIsOne =
  refl

u1FiniteCasimirGapOneDoesNotConstructFiniteHYMSpectrum :
  u1FiniteHYMSpectrumConstructed
    canonicalU1FiniteCasimirGapOneCanonicalModeReceipt
  ≡
  false
u1FiniteCasimirGapOneDoesNotConstructFiniteHYMSpectrum =
  refl

u1FiniteCasimirGapOneDoesNotPromoteClay :
  u1ContinuumClayMassGapPromoted
    canonicalU1FiniteCasimirGapOneCanonicalModeReceipt
  ≡
  false
u1FiniteCasimirGapOneDoesNotPromoteClay =
  refl

u1FiniteCasimirGapOneNoTerminalPromotion :
  u1TerminalClaimPromoted
    canonicalU1FiniteCasimirGapOneCanonicalModeReceipt
  ≡
  false
u1FiniteCasimirGapOneNoTerminalPromotion =
  refl

data U1FiniteCarrierSpectralGapInternalLayerMissingAPI : Set where
  missingFiniteHYMSpectrumAPI :
    U1FiniteCarrierSpectralGapInternalLayerMissingAPI

  missingFinitePlaquetteHamiltonianSpectrumAPI :
    U1FiniteCarrierSpectralGapInternalLayerMissingAPI

  missingFiniteCasimirDominatesPlaquetteHamiltonianAPI :
    U1FiniteCarrierSpectralGapInternalLayerMissingAPI

  missingPositiveDeltaCarrierAPI :
    U1FiniteCarrierSpectralGapInternalLayerMissingAPI

  missingFiniteVolumeUniformityAPI :
    U1FiniteCarrierSpectralGapInternalLayerMissingAPI

canonicalU1FiniteCarrierSpectralGapInternalLayerMissingAPIs :
  List U1FiniteCarrierSpectralGapInternalLayerMissingAPI
canonicalU1FiniteCarrierSpectralGapInternalLayerMissingAPIs =
  missingFiniteHYMSpectrumAPI
  ∷ missingFinitePlaquetteHamiltonianSpectrumAPI
  ∷ missingFiniteCasimirDominatesPlaquetteHamiltonianAPI
  ∷ missingPositiveDeltaCarrierAPI
  ∷ missingFiniteVolumeUniformityAPI
  ∷ []

record U1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt : Setω where
  field
    conditionalFiniteCarrierReceipt :
      U1ConditionalFiniteCarrierSpectralBoundReceipt

    conditionalFiniteCarrierReceiptIsCanonical :
      Bool

    conditionalFiniteCarrierReceiptIsCanonicalIsTrue :
      conditionalFiniteCarrierReceiptIsCanonical ≡ true

    massGapSurface :
      MassGap.BalabanRGMassGapReceiptSurface

    massGapSurfaceIsCanonical :
      Bool

    massGapSurfaceIsCanonicalIsTrue :
      massGapSurfaceIsCanonical ≡ true

    finiteDepthProObjectReceipt :
      MassGap.FiniteDepthLatticeGapProObjectReceipt

    finiteDepthProObjectReceiptIsCanonical :
      Bool

    finiteDepthProObjectReceiptIsCanonicalIsTrue :
      finiteDepthProObjectReceiptIsCanonical ≡ true

    st3DepthRecursionReceipt :
      MassGap.ST3DepthRecursionMonotonicityReceipt

    st3DepthRecursionReceiptIsCanonical :
      Bool

    st3DepthRecursionReceiptIsCanonicalIsTrue :
      st3DepthRecursionReceiptIsCanonical ≡ true

    existingLocalFiniteCarrierSpectralGapPromoted :
      Bool

    existingLocalFiniteCarrierSpectralGapPromotedIsTrue :
      existingLocalFiniteCarrierSpectralGapPromoted ≡ true

    st3LocalFiniteCarrierSpectralGapReceipt :
      Bool

    st3LocalFiniteCarrierSpectralGapReceiptIsTrue :
      st3LocalFiniteCarrierSpectralGapReceipt ≡ true

    finiteDepthPointwiseGapAvailable :
      Bool

    finiteDepthPointwiseGapAvailableIsTrue :
      finiteDepthPointwiseGapAvailable ≡ true

    attemptedFiniteCarrierSpectralGapStyleReceipt :
      Bool

    attemptedFiniteCarrierSpectralGapStyleReceiptIsTrue :
      attemptedFiniteCarrierSpectralGapStyleReceipt ≡ true

    missingAPIs :
      List U1FiniteCarrierSpectralGapInternalLayerMissingAPI

    missingAPIsAreCanonical :
      missingAPIs
      ≡
      canonicalU1FiniteCarrierSpectralGapInternalLayerMissingAPIs

    finiteHYMOperatorAndSpectrumConstructed :
      Bool

    finiteHYMOperatorAndSpectrumConstructedIsFalse :
      finiteHYMOperatorAndSpectrumConstructed ≡ false

    casimirLowerBoundConstructed :
      Bool

    casimirLowerBoundConstructedIsFalse :
      casimirLowerBoundConstructed ≡ false

    positiveDeltaConstructed :
      Bool

    positiveDeltaConstructedIsFalse :
      positiveDeltaConstructed ≡ false

    finiteVolumeUniformityConstructed :
      Bool

    finiteVolumeUniformityConstructedIsFalse :
      finiteVolumeUniformityConstructed ≡ false

    finiteCarrierBoundTransportedToRealYM :
      Bool

    finiteCarrierBoundTransportedToRealYMIsFalse :
      finiteCarrierBoundTransportedToRealYM ≡ false

    realSelfAdjointHamiltonianConstructed :
      Bool

    realSelfAdjointHamiltonianConstructedIsFalse :
      realSelfAdjointHamiltonianConstructed ≡ false

    uniformBalabanConsumed :
      Bool

    uniformBalabanConsumedIsFalse :
      uniformBalabanConsumed ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    receiptBoundary :
      List String

open U1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt public

canonicalU1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt :
  U1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt
canonicalU1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt =
  record
    { conditionalFiniteCarrierReceipt =
        canonicalU1ConditionalFiniteCarrierSpectralBoundReceipt
    ; conditionalFiniteCarrierReceiptIsCanonical =
        true
    ; conditionalFiniteCarrierReceiptIsCanonicalIsTrue =
        refl
    ; massGapSurface =
        MassGap.canonicalBalabanRGMassGapReceiptSurface
    ; massGapSurfaceIsCanonical =
        true
    ; massGapSurfaceIsCanonicalIsTrue =
        refl
    ; finiteDepthProObjectReceipt =
        MassGap.canonicalFiniteDepthLatticeGapProObjectReceipt
    ; finiteDepthProObjectReceiptIsCanonical =
        true
    ; finiteDepthProObjectReceiptIsCanonicalIsTrue =
        refl
    ; st3DepthRecursionReceipt =
        MassGap.canonicalST3DepthRecursionMonotonicityReceipt
    ; st3DepthRecursionReceiptIsCanonical =
        true
    ; st3DepthRecursionReceiptIsCanonicalIsTrue =
        refl
    ; existingLocalFiniteCarrierSpectralGapPromoted =
        MassGap.localFiniteCarrierSpectralGapPromoted
          MassGap.canonicalBalabanRGMassGapReceiptSurface
    ; existingLocalFiniteCarrierSpectralGapPromotedIsTrue =
        MassGap.localFiniteCarrierSpectralGapPromotedIsTrue
          MassGap.canonicalBalabanRGMassGapReceiptSurface
    ; st3LocalFiniteCarrierSpectralGapReceipt =
        MassGap.localFiniteCarrierSpectralGapReceipt
          MassGap.canonicalST3DepthRecursionMonotonicityReceipt
    ; st3LocalFiniteCarrierSpectralGapReceiptIsTrue =
        MassGap.localFiniteCarrierSpectralGapReceiptIsTrue
          MassGap.canonicalST3DepthRecursionMonotonicityReceipt
    ; finiteDepthPointwiseGapAvailable =
        MassGap.depthIndexedPromoted
          MassGap.canonicalFiniteDepthLatticeGapProObjectReceipt
    ; finiteDepthPointwiseGapAvailableIsTrue =
        MassGap.depthIndexedPromotedIsTrue
          MassGap.canonicalFiniteDepthLatticeGapProObjectReceipt
    ; attemptedFiniteCarrierSpectralGapStyleReceipt =
        true
    ; attemptedFiniteCarrierSpectralGapStyleReceiptIsTrue =
        refl
    ; missingAPIs =
        canonicalU1FiniteCarrierSpectralGapInternalLayerMissingAPIs
    ; missingAPIsAreCanonical =
        refl
    ; finiteHYMOperatorAndSpectrumConstructed =
        false
    ; finiteHYMOperatorAndSpectrumConstructedIsFalse =
        refl
    ; casimirLowerBoundConstructed =
        false
    ; casimirLowerBoundConstructedIsFalse =
        refl
    ; positiveDeltaConstructed =
        false
    ; positiveDeltaConstructedIsFalse =
        refl
    ; finiteVolumeUniformityConstructed =
        false
    ; finiteVolumeUniformityConstructedIsFalse =
        refl
    ; finiteCarrierBoundTransportedToRealYM =
        false
    ; finiteCarrierBoundTransportedToRealYMIsFalse =
        refl
    ; realSelfAdjointHamiltonianConstructed =
        false
    ; realSelfAdjointHamiltonianConstructedIsFalse =
        refl
    ; uniformBalabanConsumed =
        false
    ; uniformBalabanConsumedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; receiptBoundary =
        "u1 attempted the internal finite-carrier spectral-gap layer over the existing Balaban/ST3 finite-depth receipts"
        ∷ "The available local evidence is status-level: finite-depth pro-object gap receipts and ST3 depth-recursion positivity are present"
        ∷ "The owned file still lacks a finite H_YM operator with spectrum, a finite plaquette Hamiltonian spectrum, an exact Casimir domination theorem, an ordered positive Delta carrier, and finite-volume uniformity"
        ∷ "Therefore no finiteCarrierSpectralGap theorem of the form exists Delta, Delta>0 and infSpectrum H_YM_finite >= Delta is constructed here"
        ∷ "The finite evidence remains local and is not transported to the real Yang-Mills quotient or continuum limit"
        ∷ "UniformBalaban-or-AgawaIRFixedPoint, real self-adjoint H_YM, continuum Clay, spectral-gap, and terminal promotions remain false"
        ∷ []
    }

u1FiniteCarrierInternalLayerDoesNotPromoteClay :
  continuumClayMassGapPromoted
    canonicalU1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt
  ≡
  false
u1FiniteCarrierInternalLayerDoesNotPromoteClay =
  refl

u1FiniteCarrierInternalLayerDoesNotConsumeUniformBalaban :
  uniformBalabanConsumed
    canonicalU1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt
  ≡
  false
u1FiniteCarrierInternalLayerDoesNotConsumeUniformBalaban =
  refl

u1FiniteCarrierInternalLayerNoTerminalPromotion :
  terminalClaimPromoted
    canonicalU1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt
  ≡
  false
u1FiniteCarrierInternalLayerNoTerminalPromotion =
  refl

data U1Gate2FriedrichsAuthorityCitation : Set where
  reedSimonVol2X23FriedrichsExtensionAuthority :
    U1Gate2FriedrichsAuthorityCitation

data U1Gate2FriedrichsExtensionTarget : Set where
  friedrichsExtensionTargetFromSymmetricDenseSemiboundedHYM :
    U1Gate2FriedrichsExtensionTarget

record U1Gate2FriedrichsSelfAdjointAuthorityReceipt : Setω where
  field
    gateName :
      String

    gateNameIsGate2 :
      gateName
      ≡
      "Gate 2"

    denseDomainSymmetryReceipt :
      U1Gate2DenseDomainHYMSymmetryFailClosedReceipt

    denseDomainSymmetryReceiptIsCanonical :
      Bool

    denseDomainSymmetryReceiptIsCanonicalIsTrue :
      denseDomainSymmetryReceiptIsCanonical ≡ true

    finiteCasimirLayerReceipt :
      U1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt

    finiteCasimirLayerReceiptIsCanonical :
      Bool

    finiteCasimirLayerReceiptIsCanonicalIsTrue :
      finiteCasimirLayerReceiptIsCanonical ≡ true

    authorityCitation :
      U1Gate2FriedrichsAuthorityCitation

    authorityCitationIsReedSimonVol2X23 :
      authorityCitation
      ≡
      reedSimonVol2X23FriedrichsExtensionAuthority

    authorityCitationName :
      String

    authorityCitationNameIsReedSimonVol2X23 :
      authorityCitationName
      ≡
      "Reed-Simon Vol.2 X.23"

    authorityCitedOnly :
      Bool

    authorityCitedOnlyIsTrue :
      authorityCitedOnly ≡ true

    symmetricDenseHYMInputName :
      String

    symmetricDenseHYMInputNameIsCanonical :
      symmetricDenseHYMInputName
      ≡
      "symmetric dense H_YM"

    semiboundedFiniteCasimirInputName :
      String

    semiboundedFiniteCasimirInputNameIsCanonical :
      semiboundedFiniteCasimirInputName
      ≡
      "semibounded finite Casimir input"

    friedrichsExtensionTarget :
      U1Gate2FriedrichsExtensionTarget

    friedrichsExtensionTargetIsCanonical :
      friedrichsExtensionTarget
      ≡
      friedrichsExtensionTargetFromSymmetricDenseSemiboundedHYM

    conditionalArrowRecorded :
      Bool

    conditionalArrowRecordedIsTrue :
      conditionalArrowRecorded ≡ true

    denseDomainConstructed :
      Bool

    denseDomainConstructedIsFalse :
      denseDomainConstructed ≡ false

    symmetricHYMConstructed :
      Bool

    symmetricHYMConstructedIsFalse :
      symmetricHYMConstructed ≡ false

    semiboundedFiniteCasimirInputConstructed :
      Bool

    semiboundedFiniteCasimirInputConstructedIsFalse :
      semiboundedFiniteCasimirInputConstructed ≡ false

    friedrichsExtensionConstructed :
      Bool

    friedrichsExtensionConstructedIsFalse :
      friedrichsExtensionConstructed ≡ false

    selfAdjointYangMillsHamiltonianConstructed :
      Bool

    selfAdjointYangMillsHamiltonianConstructedIsFalse :
      selfAdjointYangMillsHamiltonianConstructed ≡ false

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    authorityBoundary :
      List String

open U1Gate2FriedrichsSelfAdjointAuthorityReceipt public

canonicalU1Gate2FriedrichsSelfAdjointAuthorityReceipt :
  U1Gate2FriedrichsSelfAdjointAuthorityReceipt
canonicalU1Gate2FriedrichsSelfAdjointAuthorityReceipt =
  record
    { gateName =
        "Gate 2"
    ; gateNameIsGate2 =
        refl
    ; denseDomainSymmetryReceipt =
        canonicalU1Gate2DenseDomainHYMSymmetryFailClosedReceipt
    ; denseDomainSymmetryReceiptIsCanonical =
        true
    ; denseDomainSymmetryReceiptIsCanonicalIsTrue =
        refl
    ; finiteCasimirLayerReceipt =
        canonicalU1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt
    ; finiteCasimirLayerReceiptIsCanonical =
        true
    ; finiteCasimirLayerReceiptIsCanonicalIsTrue =
        refl
    ; authorityCitation =
        reedSimonVol2X23FriedrichsExtensionAuthority
    ; authorityCitationIsReedSimonVol2X23 =
        refl
    ; authorityCitationName =
        "Reed-Simon Vol.2 X.23"
    ; authorityCitationNameIsReedSimonVol2X23 =
        refl
    ; authorityCitedOnly =
        true
    ; authorityCitedOnlyIsTrue =
        refl
    ; symmetricDenseHYMInputName =
        "symmetric dense H_YM"
    ; symmetricDenseHYMInputNameIsCanonical =
        refl
    ; semiboundedFiniteCasimirInputName =
        "semibounded finite Casimir input"
    ; semiboundedFiniteCasimirInputNameIsCanonical =
        refl
    ; friedrichsExtensionTarget =
        friedrichsExtensionTargetFromSymmetricDenseSemiboundedHYM
    ; friedrichsExtensionTargetIsCanonical =
        refl
    ; conditionalArrowRecorded =
        true
    ; conditionalArrowRecordedIsTrue =
        refl
    ; denseDomainConstructed =
        false
    ; denseDomainConstructedIsFalse =
        refl
    ; symmetricHYMConstructed =
        false
    ; symmetricHYMConstructedIsFalse =
        refl
    ; semiboundedFiniteCasimirInputConstructed =
        false
    ; semiboundedFiniteCasimirInputConstructedIsFalse =
        refl
    ; friedrichsExtensionConstructed =
        false
    ; friedrichsExtensionConstructedIsFalse =
        refl
    ; selfAdjointYangMillsHamiltonianConstructed =
        false
    ; selfAdjointYangMillsHamiltonianConstructedIsFalse =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; authorityBoundary =
        "Gate 2 records the conditional Friedrichs authority surface: symmetric dense H_YM plus semibounded finite Casimir input targets a Friedrichs extension"
        ∷ "The only named functional-analysis authority here is Reed-Simon Vol.2 X.23"
        ∷ "The authority is cited only; no DASHI operator/domain API is manufactured from the citation"
        ∷ "The prior Gate 2 dense-domain receipt still records density, quotient inner product, H_YM action, and symmetry as unconstructed"
        ∷ "The finite Casimir layer still records exact finite H_YM spectrum, Casimir domination, positive Delta, and finite-volume uniformity as unconstructed"
        ∷ "selfAdjointYangMillsHamiltonianConstructed remains false because the actual H_YM operator/domain API is absent"
        ∷ "No S8 spectral gap, continuum Clay mass gap, or terminal claim is promoted"
        ∷ []
    }

u1Gate2FriedrichsAuthorityDoesNotConstructSelfAdjointHYM :
  selfAdjointYangMillsHamiltonianConstructed
    canonicalU1Gate2FriedrichsSelfAdjointAuthorityReceipt
  ≡
  false
u1Gate2FriedrichsAuthorityDoesNotConstructSelfAdjointHYM =
  refl

data U1Gate2ContinuumSpectralBoundTransportCondition : Set where
  conditionUniformBalabanOrAgawaIRFixedPoint :
    U1Gate2ContinuumSpectralBoundTransportCondition

data U1Gate2ContinuumSpectralBoundTransportTarget : Set where
  continuumSpectralBoundTransportTargetUnderUniformBalabanOrAgawa :
    U1Gate2ContinuumSpectralBoundTransportTarget

record U1Gate2ContinuumSpectralBoundTransportConditionalReceipt : Setω where
  field
    friedrichsAuthorityReceipt :
      U1Gate2FriedrichsSelfAdjointAuthorityReceipt

    friedrichsAuthorityReceiptIsCanonical :
      Bool

    friedrichsAuthorityReceiptIsCanonicalIsTrue :
      friedrichsAuthorityReceiptIsCanonical ≡ true

    uniformBalabanOrAgawaAuthorityReceipt :
      MassGap.UniformBalabanOrAgawaIRFixedPointFailClosedReceipt

    uniformBalabanOrAgawaAuthorityReceiptIsCanonical :
      Bool

    uniformBalabanOrAgawaAuthorityReceiptIsCanonicalIsTrue :
      uniformBalabanOrAgawaAuthorityReceiptIsCanonical ≡ true

    transportCondition :
      U1Gate2ContinuumSpectralBoundTransportCondition

    transportConditionIsUniformBalabanOrAgawa :
      transportCondition
      ≡
      conditionUniformBalabanOrAgawaIRFixedPoint

    transportConditionName :
      String

    transportConditionNameIsUniformBalabanOrAgawa :
      transportConditionName
      ≡
      "UniformBalaban-or-AgawaIRFixedPoint"

    continuumSpectralBoundTransportTarget :
      U1Gate2ContinuumSpectralBoundTransportTarget

    continuumSpectralBoundTransportTargetIsCanonical :
      continuumSpectralBoundTransportTarget
      ≡
      continuumSpectralBoundTransportTargetUnderUniformBalabanOrAgawa

    finiteCasimirBoundInputName :
      String

    finiteCasimirBoundInputNameIsCanonical :
      finiteCasimirBoundInputName
      ≡
      "finite Casimir spectral-bound input"

    continuumSpectralBoundConditionalRecorded :
      Bool

    continuumSpectralBoundConditionalRecordedIsTrue :
      continuumSpectralBoundConditionalRecorded ≡ true

    uniformBalabanOrAgawaAccepted :
      Bool

    uniformBalabanOrAgawaAcceptedIsFalse :
      uniformBalabanOrAgawaAccepted ≡ false

    finiteCasimirBoundTransportedToContinuum :
      Bool

    finiteCasimirBoundTransportedToContinuumIsFalse :
      finiteCasimirBoundTransportedToContinuum ≡ false

    continuumSpectralBoundConstructed :
      Bool

    continuumSpectralBoundConstructedIsFalse :
      continuumSpectralBoundConstructed ≡ false

    selfAdjointYangMillsHamiltonianConstructed :
      Bool

    selfAdjointYangMillsHamiltonianConstructedIsFalse :
      selfAdjointYangMillsHamiltonianConstructed ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    transportBoundary :
      List String

open U1Gate2ContinuumSpectralBoundTransportConditionalReceipt public

canonicalU1Gate2ContinuumSpectralBoundTransportConditionalReceipt :
  U1Gate2ContinuumSpectralBoundTransportConditionalReceipt
canonicalU1Gate2ContinuumSpectralBoundTransportConditionalReceipt =
  record
    { friedrichsAuthorityReceipt =
        canonicalU1Gate2FriedrichsSelfAdjointAuthorityReceipt
    ; friedrichsAuthorityReceiptIsCanonical =
        true
    ; friedrichsAuthorityReceiptIsCanonicalIsTrue =
        refl
    ; uniformBalabanOrAgawaAuthorityReceipt =
        MassGap.canonicalUniformBalabanOrAgawaIRFixedPointFailClosedReceipt
    ; uniformBalabanOrAgawaAuthorityReceiptIsCanonical =
        true
    ; uniformBalabanOrAgawaAuthorityReceiptIsCanonicalIsTrue =
        refl
    ; transportCondition =
        conditionUniformBalabanOrAgawaIRFixedPoint
    ; transportConditionIsUniformBalabanOrAgawa =
        refl
    ; transportConditionName =
        "UniformBalaban-or-AgawaIRFixedPoint"
    ; transportConditionNameIsUniformBalabanOrAgawa =
        refl
    ; continuumSpectralBoundTransportTarget =
        continuumSpectralBoundTransportTargetUnderUniformBalabanOrAgawa
    ; continuumSpectralBoundTransportTargetIsCanonical =
        refl
    ; finiteCasimirBoundInputName =
        "finite Casimir spectral-bound input"
    ; finiteCasimirBoundInputNameIsCanonical =
        refl
    ; continuumSpectralBoundConditionalRecorded =
        true
    ; continuumSpectralBoundConditionalRecordedIsTrue =
        refl
    ; uniformBalabanOrAgawaAccepted =
        MassGap.acceptedContinuumAuthoritySupplied
          MassGap.canonicalUniformBalabanOrAgawaIRFixedPointFailClosedReceipt
    ; uniformBalabanOrAgawaAcceptedIsFalse =
        MassGap.acceptedContinuumAuthoritySuppliedIsFalse
          MassGap.canonicalUniformBalabanOrAgawaIRFixedPointFailClosedReceipt
    ; finiteCasimirBoundTransportedToContinuum =
        false
    ; finiteCasimirBoundTransportedToContinuumIsFalse =
        refl
    ; continuumSpectralBoundConstructed =
        false
    ; continuumSpectralBoundConstructedIsFalse =
        refl
    ; selfAdjointYangMillsHamiltonianConstructed =
        false
    ; selfAdjointYangMillsHamiltonianConstructedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; transportBoundary =
        "Gate 2 records continuum spectral-bound transport only as a conditional target under UniformBalaban-or-AgawaIRFixedPoint"
        ∷ "The UniformBalaban/Agawa receipt remains fail-closed: no accepted continuum authority token is supplied"
        ∷ "The finite Casimir spectral-bound input is not transported to the continuum in this module"
        ∷ "No continuum spectral bound, self-adjoint Yang-Mills Hamiltonian, continuum Clay mass gap, or terminal claim is promoted"
        ∷ []
    }

u1Gate2ContinuumSpectralBoundTransportRemainsConditional :
  finiteCasimirBoundTransportedToContinuum
    canonicalU1Gate2ContinuumSpectralBoundTransportConditionalReceipt
  ≡
  false
u1Gate2ContinuumSpectralBoundTransportRemainsConditional =
  refl

u1Gate2ContinuumSpectralBoundTransportDoesNotPromoteClay :
  continuumClayMassGapPromoted
    canonicalU1Gate2ContinuumSpectralBoundTransportConditionalReceipt
  ≡
  false
u1Gate2ContinuumSpectralBoundTransportDoesNotPromoteClay =
  refl

record S8PressureBelow15ToYangMillsSpectralGapTheorem : Setω where
  field
    hypotheses :
      PressureToSpectralGapHypothesisPackage

    pressureBelow :
      14 < 15

    pressureNotSaturatedAt15 :
      ¬ (14 ≡ 15)

    pressureDeficitIsCarrierUnit :
      15 ∸ 14 ≡ 1

    subThresholdSpectralGapDependency :
      S8SubThresholdSpectralGapDependency hypotheses

    spectralGapWitness :
      Set

    spectralGapWitnessInhabited :
      spectralGapWitness

s8CarrierTheoremSpectralGapWitness :
  PressureToSpectralGapHypothesisPackage →
  Set
s8CarrierTheoremSpectralGapWitness hypotheses =
  (ψ : State hypotheses) →
  nonVacuum hypotheses ψ →
  orthogonalToVacuum hypotheses ψ →
  _≤E_ hypotheses
    (gapUnit hypotheses)
    (hamiltonianEnergy hypotheses ψ)

s8PressureBelow15ToYangMillsSpectralGapTheoremFromCarrier :
  (hypotheses : PressureToSpectralGapHypothesisPackage) →
  SelfAdjointYangMillsHamiltonianOnCarrierQuotient hypotheses →
  S8PressureBelow15ToYangMillsSpectralGapTheorem
s8PressureBelow15ToYangMillsSpectralGapTheoremFromCarrier
  hypotheses
  carrierTheorem =
  record
    { hypotheses =
        hypotheses
    ; pressureBelow =
        Probe.fourteenBelowFifteen
    ; pressureNotSaturatedAt15 =
        Probe.canonicalPressureNotSaturatedAt15
    ; pressureDeficitIsCarrierUnit =
        Probe.canonicalPressureDeficitIs1
    ; subThresholdSpectralGapDependency =
        selfAdjointYangMillsCarrierSubThresholdDependency
          hypotheses
          carrierTheorem
    ; spectralGapWitness =
        s8CarrierTheoremSpectralGapWitness hypotheses
    ; spectralGapWitnessInhabited =
        subThresholdLowerBoundTransport carrierTheorem
    }

record PressureBelow15SpectralGapReceipt
  (theorem : S8PressureBelow15ToYangMillsSpectralGapTheorem)
  : Setω where
  field
    spectralGapWitness :
      Set

    spectralGapWitnessMatchesTheorem :
      spectralGapWitness
      ≡
      S8PressureBelow15ToYangMillsSpectralGapTheorem.spectralGapWitness theorem

    spectralGapWitnessInhabited :
      spectralGapWitness

    receiptBoundary :
      List String

gapReceiptFromInhabitedS8Theorem :
  (theorem : S8PressureBelow15ToYangMillsSpectralGapTheorem) →
  PressureBelow15SpectralGapReceipt theorem
gapReceiptFromInhabitedS8Theorem theorem =
  record
    { spectralGapWitness =
        S8PressureBelow15ToYangMillsSpectralGapTheorem.spectralGapWitness theorem
    ; spectralGapWitnessMatchesTheorem =
        refl
    ; spectralGapWitnessInhabited =
        S8PressureBelow15ToYangMillsSpectralGapTheorem.spectralGapWitnessInhabited theorem
    ; receiptBoundary =
        "Gap receipt is constructible only from an inhabited S8 pressure-below-15 to Yang-Mills spectral-gap theorem"
        ∷ "No canonical receipt is constructed by the obstruction surface"
        ∷ []
    }

record PressureBelow15SpectralTheoremStatement : Setω where
  field
    probe :
      Probe.PressureBelow15SpectralProbe

    yangMillsHamiltonianTarget :
      Set₁

    yangMillsHamiltonianTargetName :
      String

    hypotheses :
      PressureToSpectralGapHypothesisPackage

    pressureBelow :
      Probe.pressureBound probe < Probe.canonicalDim probe

    pressureDeficitIsCarrierUnit :
      Probe.canonicalPressureDeficit ≡ 1

    theoremTarget :
      Set

record PressureBelow15SpectralTheoremObstruction : Setω where
  field
    probe :
      Probe.PressureBelow15SpectralProbe

    probeSelection :
      PressureBelow15SpectralObstructionSelection

    yangMillsHamiltonianTarget :
      Set₁

    yangMillsHamiltonianTargetName :
      String

    globalCarrierBlocker :
      S8GlobalYangMillsHamiltonianCarrierBlocker

    firstGlobalCarrierMissing :
      S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    firstGlobalCarrierMissingIsSelfAdjointYangMillsHamiltonian :
      firstGlobalCarrierMissing
      ≡
      missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    pressureBelow :
      Probe.pressureBound probe < Probe.canonicalDim probe

    pressureDeficit :
      Nat

    pressureDeficitIsCarrierUnit :
      pressureDeficit ≡ 1

    pressureNotSaturatedAt15 :
      ¬ (Probe.pressureBound probe ≡ Probe.canonicalDim probe)

    pressureBoundNot15 :
      ¬ (Probe.pressureBound probe ≡ 15)

    theoremStatementSelection :
      PressureBelow15SpectralObstructionSelection

    exactMissingTheorem :
      PressureBelow15SpectralExactMissingTheorem

    exactMissingTheoremName :
      String

    gapReceiptPolicy :
      PressureBelow15SpectralGapReceiptPolicy

    gapReceiptTypeName :
      String

    exactMissingHypotheses :
      List PressureBelow15SpectralRequiredHypothesis

    exactMissingHypothesesAreCanonical :
      exactMissingHypotheses
      ≡
      canonicalPressureBelow15SpectralRequiredHypotheses

    s8PackageMechanicalVerdict :
      S8PressurePackageMechanicalVerdict

    s8SubobligationSurfaceName :
      String

    s8LocalTheoremFields :
      List S8PressureBelow15LocalTheoremField

    s8LocalTheoremFieldsAreCanonical :
      s8LocalTheoremFields
      ≡
      canonicalS8PressureBelow15LocalTheoremFields

    s8FirstLocalMissing :
      S8PressureBelow15LocalTheoremField

    s8FirstLocalMissingIsCoercivityWitness :
      s8FirstLocalMissing
      ≡
      s8PressureEnergyCoercivityWitnessField

    s8EvidenceIndex :
      S8PressureBelow15EvidenceIndex

    s8EvidenceIndexSurfacesAreCanonical :
      S8PressureBelow15EvidenceIndex.searchedLocalCandidateSurfaces
        s8EvidenceIndex
      ≡
      canonicalS8PressureBelow15SearchedLocalCandidateSurfaces

    s8EvidenceIndexFirstMissingIsCoercivity :
      S8PressureBelow15EvidenceIndex.firstMissingWitness
        s8EvidenceIndex
      ≡
      s8PressureEnergyCoercivityWitnessField

    s8CoercivityPrimitiveRequest :
      S8PressureEnergyCoercivityPrimitiveRequest

    s8CoercivityPrimitiveRequestIsCanonical :
      s8CoercivityPrimitiveRequest
      ≡
      canonicalS8PressureEnergyCoercivityPrimitiveRequest

    s8FirstCoercivityPrimitiveMissing :
      S8PressureEnergyCoercivityPrimitiveField

    s8FirstCoercivityPrimitiveMissingIsLaneHamiltonianDominance :
      s8FirstCoercivityPrimitiveMissing
      ≡
      s8LaneHamiltonianDominatesPressureNormField

    firstMissing :
      Probe.PressureBelow15SpectralMissingField

    firstMissingIsPressureToSpectral :
      firstMissing
      ≡
      Probe.missingPressureBelowDimToSpectralGapTheorem

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    obstructionBoundary :
      List String

open PressureBelow15SpectralTheoremObstruction public

canonicalPressureBelow15SpectralTheoremObstruction :
  PressureBelow15SpectralTheoremObstruction
canonicalPressureBelow15SpectralTheoremObstruction =
  record
    { probe =
        Probe.canonicalPressureBelow15SpectralProbe
    ; probeSelection =
        canonicalProbeSelected
    ; yangMillsHamiltonianTarget =
        Set
    ; yangMillsHamiltonianTargetName =
        "SelfAdjointYangMillsHamiltonianOnCarrierQuotient"
    ; globalCarrierBlocker =
        canonicalS8GlobalYangMillsHamiltonianCarrierBlocker
    ; firstGlobalCarrierMissing =
        missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; firstGlobalCarrierMissingIsSelfAdjointYangMillsHamiltonian =
        refl
    ; pressureBelow =
        Probe.w9PressureBoundBelowCanonicalDim
    ; pressureDeficit =
        Probe.canonicalPressureDeficit
    ; pressureDeficitIsCarrierUnit =
        Probe.canonicalPressureDeficitIs1
    ; pressureNotSaturatedAt15 =
        Probe.canonicalPressureNotSaturatedAt15
    ; pressureBoundNot15 =
        Probe.canonicalPressureBoundNot15
    ; theoremStatementSelection =
        sharpenedTheoremStatementSelected
    ; exactMissingTheorem =
        s8PressureBelow15ToYangMillsSpectralGapTheoremMissing
    ; exactMissingTheoremName =
        "S8PressureBelow15ToYangMillsSpectralGapTheorem"
    ; gapReceiptPolicy =
        gapReceiptOnlyFromInhabitedS8Theorem
    ; gapReceiptTypeName =
        "PressureBelow15SpectralGapReceipt"
    ; exactMissingHypotheses =
        canonicalPressureBelow15SpectralRequiredHypotheses
    ; exactMissingHypothesesAreCanonical =
        refl
    ; s8PackageMechanicalVerdict =
        packageDoesNotMechanicallyYieldGapReceipt
    ; s8SubobligationSurfaceName =
        "S8PressureBelow15SubobligationSurface"
    ; s8LocalTheoremFields =
        canonicalS8PressureBelow15LocalTheoremFields
    ; s8LocalTheoremFieldsAreCanonical =
        refl
    ; s8FirstLocalMissing =
        s8PressureEnergyCoercivityWitnessField
    ; s8FirstLocalMissingIsCoercivityWitness =
        refl
    ; s8EvidenceIndex =
        canonicalS8PressureBelow15EvidenceIndex
    ; s8EvidenceIndexSurfacesAreCanonical =
        refl
    ; s8EvidenceIndexFirstMissingIsCoercivity =
        refl
    ; s8CoercivityPrimitiveRequest =
        canonicalS8PressureEnergyCoercivityPrimitiveRequest
    ; s8CoercivityPrimitiveRequestIsCanonical =
        refl
    ; s8FirstCoercivityPrimitiveMissing =
        s8LaneHamiltonianDominatesPressureNormField
    ; s8FirstCoercivityPrimitiveMissingIsLaneHamiltonianDominance =
        refl
    ; firstMissing =
        Probe.missingPressureBelowDimToSpectralGapTheorem
    ; firstMissingIsPressureToSpectral =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; obstructionBoundary =
        "The repo proves pressureBound = 14, canonicalDim = 15, 14 < 15, and 15 - 14 = 1"
        ∷ "The strongest local negative fact is pressureBound /= 15; no pressureAtDim API exists in the inspected surfaces"
        ∷ "The exact missing theorem is S8PressureBelow15ToYangMillsSpectralGapTheorem"
        ∷ "The package does not mechanically yield the gap receipt; it yields only lower-bound transport"
        ∷ "Below S8, the typed split is S8PressureBelow15LocalTheoremFields with first local missing pressureEnergyCoercivityWitness"
        ∷ "The pressureEnergyCoercivityWitness is further narrowed to laneHamiltonianDominatesPressureNorm plus a compiler into the opaque package field"
        ∷ "The attempted Nat-order route is recorded as blocked: no Energy -> Nat interpretation or _<=E_ preservation/reflection law is available locally"
        ∷ "The final internal compiler is s8LaneSumDominanceCompilerFromOrderCompatibility; external six-witness input is consumed only through S8LaneSumDominanceExternalLemmaInterface and that compiler"
        ∷ "No existing primitive supplies a Yang-Mills Hamiltonian carrier with vacuum orthogonality and an ordered energy codomain"
        ∷ "The first global carrier theorem missing below S8 is SelfAdjointYangMillsHamiltonianOnCarrierQuotient"
        ∷ "No canonical local primitive inhabits pressureEnergyCoercive, carrierUnitNormalization, or a Yang-Mills spectral witness"
        ∷ "S8PressureBelow15EvidenceIndex records the searched local Agda surfaces and the first missing witness exactly"
        ∷ "PressureBelow15SpectralGapReceipt is constructible only from an inhabited S8 theorem"
        ∷ "This module therefore sharpens the missing theorem instead of constructing a spectral gap"
        ∷ "No spectral gap, terminal claim, W3/W4/W5 authority, or continuum Clay mass-gap promotion is constructed here"
        ∷ []
    }

pressureBelow15SpectralExactMissingHypotheses :
  exactMissingHypotheses canonicalPressureBelow15SpectralTheoremObstruction
  ≡
  canonicalPressureBelow15SpectralRequiredHypotheses
pressureBelow15SpectralExactMissingHypotheses =
  refl

pressureBelow15SpectralExactMissingTheorem :
  exactMissingTheorem canonicalPressureBelow15SpectralTheoremObstruction
  ≡
  s8PressureBelow15ToYangMillsSpectralGapTheoremMissing
pressureBelow15SpectralExactMissingTheorem =
  refl

pressureBelow15FirstGlobalCarrierMissing :
  firstGlobalCarrierMissing canonicalPressureBelow15SpectralTheoremObstruction
  ≡
  missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
pressureBelow15FirstGlobalCarrierMissing =
  refl

pressureBelow15FirstGlobalCarrierMissingField :
  firstMissingCarrierTheoremField
    canonicalS8GlobalYangMillsHamiltonianCarrierBlocker
  ≡
  s8SelfAdjointHamiltonianOnCarrierQuotientField
pressureBelow15FirstGlobalCarrierMissingField =
  refl

pressureBelow15NextGlobalCarrierMissingFieldAfterSelfAdjoint :
  nextCarrierTheoremFieldAfterFirstMissing
    canonicalS8GlobalYangMillsHamiltonianCarrierBlocker
  ≡
  s8VacuumSectorField
pressureBelow15NextGlobalCarrierMissingFieldAfterSelfAdjoint =
  refl

pressureBelow15NextGlobalCarrierMissingFieldAfterVacuum :
  nextCarrierTheoremFieldAfterVacuum
    canonicalS8GlobalYangMillsHamiltonianCarrierBlocker
  ≡
  s8NonVacuumSectorPredicateField
pressureBelow15NextGlobalCarrierMissingFieldAfterVacuum =
  refl

pressureBelow15NextGlobalCarrierMissingFieldAfterNonVacuum :
  nextCarrierTheoremFieldAfterNonVacuum
    canonicalS8GlobalYangMillsHamiltonianCarrierBlocker
  ≡
  s8VacuumOrthogonalityPredicateField
pressureBelow15NextGlobalCarrierMissingFieldAfterNonVacuum =
  refl

pressureBelow15NextGlobalCarrierMissingFieldAfterVacuumOrthogonality :
  nextCarrierTheoremFieldAfterVacuumOrthogonality
    canonicalS8GlobalYangMillsHamiltonianCarrierBlocker
  ≡
  s8EnergyOrderAndPositiveGapUnitField
pressureBelow15NextGlobalCarrierMissingFieldAfterVacuumOrthogonality =
  refl

pressureBelow15NextGlobalCarrierMissingFieldAfterEnergyOrderAndPositiveGapUnit :
  nextCarrierTheoremFieldAfterEnergyOrderAndPositiveGapUnit
    canonicalS8GlobalYangMillsHamiltonianCarrierBlocker
  ≡
  s8SubThresholdLowerBoundTransportField
pressureBelow15NextGlobalCarrierMissingFieldAfterEnergyOrderAndPositiveGapUnit =
  refl

pressureBelow15NextGlobalCarrierMissingFieldAfterSubThresholdLowerBoundTransport :
  nextCarrierTheoremFieldAfterSubThresholdLowerBoundTransport
    canonicalS8GlobalYangMillsHamiltonianCarrierBlocker
  ≡
  s8PressureEnergyCoercivityWitnessField
pressureBelow15NextGlobalCarrierMissingFieldAfterSubThresholdLowerBoundTransport =
  refl

pressureBelow15NextGlobalCarrierMissingFieldAfterPressureEnergyCoercivity :
  nextCarrierTheoremFieldAfterPressureEnergyCoercivity
    canonicalS8GlobalYangMillsHamiltonianCarrierBlocker
  ≡
  s8CarrierUnitNormalizationField
pressureBelow15NextGlobalCarrierMissingFieldAfterPressureEnergyCoercivity =
  refl

pressureBelow15SpectralPressureBoundNot15 :
  ¬ (Probe.pressureBound Probe.canonicalPressureBelow15SpectralProbe ≡ 15)
pressureBelow15SpectralPressureBoundNot15 =
  Probe.canonicalPressureBoundNot15
