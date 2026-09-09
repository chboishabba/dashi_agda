module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGSourceValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGAuthorityClosureExact as Authority
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGModelProvenanceBidiExact as Provenance
import DASHI.Physics.ExoticGravity.SuperconductingChargeMassCurrentBidiExact as Current
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryStressEnergyScopeBidiExact as Scope
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryStressEnergyCompilationExact as Compilation
import DASHI.Physics.ExoticGravity.LiTorr1991CombinedFieldSourceEntitlementExact as LT1991
import DASHI.Physics.ExoticGravity.LiTorr1992CoupledPotentialSourceEntitlementExact as LT1992
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScalingModelDiscriminatorExact as Scaling

------------------------------------------------------------------------
-- MODEL ORIGIN / ATTRIBUTION
------------------------------------------------------------------------

internalAuthorityShapeIsClosed :
  Authority.internalAuthorityShapeClosed
    Authority.canonicalMaterialEffectiveGAuthorityClosureBoundary ≡ true
internalAuthorityShapeIsClosed = refl

authorityClosureDoesNotValidatePhysics :
  Authority.authorityClosureEqualsPhysicalValidation
    Authority.canonicalMaterialEffectiveGAuthorityClosureBoundary ≡ false
authorityClosureDoesNotValidatePhysics = refl

authorityClosureDoesNotPaySourceCurrent :
  Authority.authorityClosurePaysSourceCurrent
    Authority.canonicalMaterialEffectiveGAuthorityClosureBoundary ≡ false
authorityClosureDoesNotPaySourceCurrent = refl

authorityClosureDoesNotPayStressEnergy :
  Authority.authorityClosurePaysStressEnergy
    Authority.canonicalMaterialEffectiveGAuthorityClosureBoundary ≡ false
authorityClosureDoesNotPayStressEnergy = refl

historicalLiTorrClaimIsNotDASHIEffectiveG :
  Provenance.liTorrHistoricalClaimEqualsDASHIEffectiveGInterpretation
    Provenance.canonicalModelProvenanceBoundary ≡ false
historicalLiTorrClaimIsNotDASHIEffectiveG = refl

exactLiTorrEquationDoesNotEntitleDASHIEffectiveG :
  Provenance.exactLiTorrEquationAutomaticallyEntitlesDASHIEffectiveGModel
    Provenance.canonicalModelProvenanceBoundary ≡ false
exactLiTorrEquationDoesNotEntitleDASHIEffectiveG = refl

internalDASHIModelNeedsProofLineage :
  Provenance.dashiEffectiveGModelNeedsInternalProofLineage
    Provenance.canonicalModelProvenanceBoundary ≡ true
internalDASHIModelNeedsProofLineage = refl

------------------------------------------------------------------------
-- HISTORICAL SOURCE ENTITLEMENT DOES NOT PROMOTE PHYSICS
------------------------------------------------------------------------

primary1991AbstractDoesNotProveEnhancement :
  LT1991.sourceEntitlementProvesSuperconductingEnhancement
    LT1991.canonicalLiTorr1991SourceEntitlementBoundary ≡ false
primary1991AbstractDoesNotProveEnhancement = refl

primary1991AbstractDoesNotProveNegativeG :
  LT1991.sourceEntitlementProvesMaterialEffectiveNegativeG
    LT1991.canonicalLiTorr1991SourceEntitlementBoundary ≡ false
primary1991AbstractDoesNotProveNegativeG = refl

secondary1992CarrierIsNotPrimaryAPS :
  LT1992.secondaryInspectionEqualsPrimaryPublisherCustody
    LT1992.canonicalCoupledPotentialAttributionBoundary ≡ false
secondary1992CarrierIsNotPrimaryAPS = refl

secondary1992EquationShapeDoesNotProveNegativeG :
  LT1992.equationShapeAttributionProvesMaterialEffectiveNegativeG
    LT1992.canonicalCoupledPotentialAttributionBoundary ≡ false
secondary1992EquationShapeDoesNotProveNegativeG = refl

------------------------------------------------------------------------
-- CHARGE CURRENT != MASS CURRENT
------------------------------------------------------------------------

netElectricalCurrentDoesNotDetermineMassCurrent :
  Current.netElectricalCurrentDeterminesMassCurrent
    Current.canonicalChargeMassCurrentBoundary ≡ false
netElectricalCurrentDoesNotDetermineMassCurrent = refl

measuredSupercurrentDoesNotPaySourceCurrent :
  Current.measuredSupercurrentAlonePaysSourceCurrentLeaf
    Current.canonicalChargeMassCurrentBoundary ≡ false
measuredSupercurrentDoesNotPaySourceCurrent = refl

massCurrentNeedsComponentResolvedSource :
  Current.componentResolvedSourceReconstructionRequired
    Current.canonicalChargeMassCurrentBoundary ≡ true
massCurrentNeedsComponentResolvedSource = refl

massCurrentDoesNotConstructFullStressEnergy :
  Current.massCurrentReceiptAutomaticallyConstructsFullStressEnergy
    Current.canonicalChargeMassCurrentBoundary ≡ false
massCurrentDoesNotConstructFullStressEnergy = refl

------------------------------------------------------------------------
-- LABORATORY T_mn != THEOREM-FACING W4 T_mn
------------------------------------------------------------------------

sameTensorNameDoesNotFixStressEnergyConsumer :
  Scope.sameTensorNameMeansSameConsumer
    Scope.canonicalLaboratoryStressEnergyScopeBoundary ≡ false
sameTensorNameDoesNotFixStressEnergyConsumer = refl

labStressEnergyDoesNotPayW4 :
  Scope.laboratoryReceiptPaysW4MatterInterface
    Scope.canonicalLaboratoryStressEnergyScopeBoundary ≡ false
labStressEnergyDoesNotPayW4 = refl

w4DoesNotPayLabMeasurement :
  Scope.w4MatterInterfacePaysLaboratorySourceMeasurement
    Scope.canonicalLaboratoryStressEnergyScopeBoundary ≡ false
w4DoesNotPayLabMeasurement = refl

labStressEnergyRequiredForComparator :
  Scope.laboratoryStressEnergyRequiredForSameApparatusGRComparator
    Scope.canonicalLaboratoryStressEnergyScopeBoundary ≡ true
labStressEnergyRequiredForComparator = refl

------------------------------------------------------------------------
-- J_m -> T_mn COMPILATION IS A REAL SECOND STAGE
------------------------------------------------------------------------

massCurrentAloneDoesNotConstructStressEnergy :
  Compilation.massCurrentAloneConstructsStressEnergy
    Compilation.canonicalLaboratoryStressEnergyCompilationBoundary ≡ false
massCurrentAloneDoesNotConstructStressEnergy = refl

energyDensityStillRequiredAfterMassCurrent :
  Compilation.energyDensityStillRequired
    Compilation.canonicalLaboratoryStressEnergyCompilationBoundary ≡ true
energyDensityStillRequiredAfterMassCurrent = refl

stressComponentsStillRequiredAfterMassCurrent :
  Compilation.stressComponentsStillRequired
    Compilation.canonicalLaboratoryStressEnergyCompilationBoundary ≡ true
stressComponentsStillRequiredAfterMassCurrent = refl

tensorAssemblyStillRequiredAfterMassCurrent :
  Compilation.tensorAssemblyStillRequired
    Compilation.canonicalLaboratoryStressEnergyCompilationBoundary ≡ true
tensorAssemblyStillRequiredAfterMassCurrent = refl

compiledLabStressEnergyStillDoesNotPayW4 :
  Compilation.compiledLabStressEnergyPaysW4Interface
    Compilation.canonicalLaboratoryStressEnergyCompilationBoundary ≡ false
compiledLabStressEnergyStillDoesNotPayW4 = refl

compiledLabStressEnergyDoesNotProveNegativeG :
  Compilation.compiledLabStressEnergyProvesNegativeEffectiveG
    Compilation.canonicalLaboratoryStressEnergyCompilationBoundary ≡ false
compiledLabStressEnergyDoesNotProveNegativeG = refl

------------------------------------------------------------------------
-- MODEL IDENTIFIABILITY STILL OPEN
------------------------------------------------------------------------

sourceDependentAdditiveCanStillMimicMultiplicative :
  Scaling.sourceDependentAdditiveCanMimicMultiplicativeSignature
    Scaling.canonicalScalingModelDiscriminatorBoundary ≡ true
sourceDependentAdditiveCanStillMimicMultiplicative = refl
