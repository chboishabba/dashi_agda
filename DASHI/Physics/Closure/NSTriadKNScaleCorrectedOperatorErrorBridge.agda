module DASHI.Physics.Closure.NSTriadKNScaleCorrectedOperatorErrorBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat using (_≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; *-identityʳ)
open import Relation.Nullary using (¬_)

import DASHI.Physics.Closure.NSTriadKNQGapTransfer as QGap
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom as ScaleHeadroom
import DASHI.Physics.Closure.NSTriadKNScaledOperatorErrorAudit as Audit
import DASHI.Physics.Closure.NSTriadKNVariationalRigidityOperatorRefinement as Variational
import DASHI.Physics.Closure.NSTriadKNAdmissibleConstrainedSpectralAudit as SpectralAudit
import DASHI.Physics.Closure.NSTriadKNAdmissibleFourierTriadCarrier as FourierTriad
import DASHI.Physics.Closure.NSTriadKNRetainedPositiveSectorKernelOperator as RetainedKernel

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

four : Nat
four = suc three

Carrier : Set
Carrier = ResidueNorm.ResidueEnergyCarrier one

residueEnergy : Carrier → Nat
residueEnergy = ResidueNorm.residueEnergy

canonicalCompatibilityScale : ScaleHeadroom.CompatibilityScale one
canonicalCompatibilityScale =
  ScaleHeadroom.mkCompatibilityScale four (s≤s (s≤s z≤n))

canonicalScaleSqIsFour :
  ScaleHeadroom.CompatibilityScale.scaleSq canonicalCompatibilityScale ≡ four
canonicalScaleSqIsFour = refl

canonicalScaledOperatorErrorTarget : Set
canonicalScaledOperatorErrorTarget =
  QGap.scaledOperatorErrorBridgeTarget
    canonicalCompatibilityScale
    residueEnergy
    residueEnergy
    four

canonicalScaledOperatorErrorProof : canonicalScaledOperatorErrorTarget
canonicalScaledOperatorErrorProof x = ≤-refl

canonicalScaledOperatorErrorBridge :
  QGap.ScaledOperatorErrorBridge one Carrier
canonicalScaledOperatorErrorBridge =
  QGap.mkScaledOperatorErrorBridge
    canonicalCompatibilityScale
    residueEnergy
    residueEnergy
    four
    canonicalScaledOperatorErrorProof

canonicalScaledOperatorErrorBridgeClosed : Bool
canonicalScaledOperatorErrorBridgeClosed = true

canonicalScaledOperatorErrorBridgeClosedIsTrue :
  canonicalScaledOperatorErrorBridgeClosed ≡ true
canonicalScaledOperatorErrorBridgeClosedIsTrue = refl

scaledErrorConstantAtUnitForcesFourOrMore :
  (C : Nat) → four * one ≤ C * one → four ≤ C
scaledErrorConstantAtUnitForcesFourOrMore C proof
  rewrite *-identityʳ four
        | *-identityʳ C = proof

canonicalCorrectedErrorConstantIsSharp : four * one ≤ four * one
canonicalCorrectedErrorConstantIsSharp = ≤-refl

canonicalCurrentModelHasNoStrictGap :
  (A C : Nat) →
  A * one ≤ four * one →
  four * one ≤ C * one →
  ¬ (C < A)
canonicalCurrentModelHasNoStrictGap =
  Audit.canonicalUnitScaleHasNoStrictMargin

canonicalCompatibilityRouteClosed : Bool
canonicalCompatibilityRouteClosed = false

canonicalCompatibilityRouteClosedIsFalse :
  canonicalCompatibilityRouteClosed ≡ false
canonicalCompatibilityRouteClosedIsFalse = refl

canonicalSharperScaledOperatorErrorTarget : Set
canonicalSharperScaledOperatorErrorTarget =
  QGap.sharperScaledOperatorErrorBridgeTarget
    canonicalCompatibilityScale
    residueEnergy
    residueEnergy
    three

canonicalSharperScaledOperatorErrorClosed : Bool
canonicalSharperScaledOperatorErrorClosed = false

canonicalSharperScaledOperatorErrorClosedIsFalse :
  canonicalSharperScaledOperatorErrorClosed ≡ false
canonicalSharperScaledOperatorErrorClosedIsFalse = refl

------------------------------------------------------------------------
-- Implemented analytic, carrier, enumeration and operator routes.
------------------------------------------------------------------------

variationalRouteImplemented : Bool
variationalRouteImplemented = true

variationalRouteImplementedIsTrue : variationalRouteImplemented ≡ true
variationalRouteImplementedIsTrue = refl

compactnessRigidityRouteImplemented : Bool
compactnessRigidityRouteImplemented = true

compactnessRigidityRouteImplementedIsTrue :
  compactnessRigidityRouteImplemented ≡ true
compactnessRigidityRouteImplementedIsTrue = refl

refinedOperatorRouteImplemented : Bool
refinedOperatorRouteImplemented = true

refinedOperatorRouteImplementedIsTrue : refinedOperatorRouteImplemented ≡ true
refinedOperatorRouteImplementedIsTrue = refl

constrainedSpectralAuditRouteImplemented : Bool
constrainedSpectralAuditRouteImplemented =
  SpectralAudit.constrainedSpectralAuditImplemented

constrainedSpectralAuditRouteImplementedIsTrue :
  constrainedSpectralAuditRouteImplemented ≡ true
constrainedSpectralAuditRouteImplementedIsTrue =
  SpectralAudit.constrainedSpectralAuditImplementedIsTrue

admissibleFourierTriadCarrierRouteImplemented : Bool
admissibleFourierTriadCarrierRouteImplemented =
  FourierTriad.admissibleFourierTriadCarrierImplemented

admissibleFourierTriadCarrierRouteImplementedIsTrue :
  admissibleFourierTriadCarrierRouteImplemented ≡ true
admissibleFourierTriadCarrierRouteImplementedIsTrue =
  FourierTriad.admissibleFourierTriadCarrierImplementedIsTrue

richStage3OperatorHandoffRouteImplemented : Bool
richStage3OperatorHandoffRouteImplemented =
  FourierTriad.richStage3OperatorHandoffImplemented

richStage3OperatorHandoffRouteImplementedIsTrue :
  richStage3OperatorHandoffRouteImplemented ≡ true
richStage3OperatorHandoffRouteImplementedIsTrue =
  FourierTriad.richStage3OperatorHandoffImplementedIsTrue

retainedPositiveSectorFiberRouteImplemented : Bool
retainedPositiveSectorFiberRouteImplemented =
  RetainedKernel.retainedPositiveSectorFiberConstructionImplemented

retainedPositiveSectorFiberRouteImplementedIsTrue :
  retainedPositiveSectorFiberRouteImplemented ≡ true
retainedPositiveSectorFiberRouteImplementedIsTrue =
  RetainedKernel.retainedPositiveSectorFiberConstructionImplementedIsTrue

finiteRetainedWeightedAggregateRouteImplemented : Bool
finiteRetainedWeightedAggregateRouteImplemented =
  RetainedKernel.finiteWeightedAggregateImplemented

finiteRetainedWeightedAggregateRouteImplementedIsTrue :
  finiteRetainedWeightedAggregateRouteImplemented ≡ true
finiteRetainedWeightedAggregateRouteImplementedIsTrue =
  RetainedKernel.finiteWeightedAggregateImplementedIsTrue

retainedFiberRichOperatorConstructionImplemented : Bool
retainedFiberRichOperatorConstructionImplemented =
  RetainedKernel.retainedFiberToRichOperatorImplemented

retainedFiberRichOperatorConstructionImplementedIsTrue :
  retainedFiberRichOperatorConstructionImplemented ≡ true
retainedFiberRichOperatorConstructionImplementedIsTrue =
  RetainedKernel.retainedFiberToRichOperatorImplementedIsTrue

------------------------------------------------------------------------
-- Honest live boundary.
------------------------------------------------------------------------

canonicalGeneralizedEigenvalueSaturationConfirmed :
  SpectralAudit.canonicalQError SpectralAudit.canonicalUnit
    ≡ SpectralAudit.canonicalQBase SpectralAudit.canonicalUnit
canonicalGeneralizedEigenvalueSaturationConfirmed =
  SpectralAudit.canonicalGeneralizedEigenvalueIsOne

canonicalActualStage3MatrixStillMissing :
  SpectralAudit.canonicalActualStage3MatrixExposed ≡ false
canonicalActualStage3MatrixStillMissing =
  SpectralAudit.canonicalActualStage3MatrixExposedIsFalse

canonicalEnergyCarrierConstraintLossConfirmed :
  SpectralAudit.canonicalEnergyCarrierCanEncodePhysicalConstraints ≡ false
canonicalEnergyCarrierConstraintLossConfirmed =
  SpectralAudit.canonicalEnergyCarrierCanEncodePhysicalConstraintsIsFalse

canonicalPhysicalRetainedFiberStillMissing :
  RetainedKernel.canonicalPhysicalRetainedFiberInhabited ≡ false
canonicalPhysicalRetainedFiberStillMissing =
  RetainedKernel.canonicalPhysicalRetainedFiberInhabitedIsFalse

actualRetainedTriadEnumerationStillMissing :
  FourierTriad.actualRetainedTriadEnumerationConnected ≡ false
actualRetainedTriadEnumerationStillMissing =
  FourierTriad.actualRetainedTriadEnumerationConnectedIsFalse

actualRichStage3OperatorStillOpen :
  FourierTriad.actualRichStage3OperatorClosed ≡ false
actualRichStage3OperatorStillOpen =
  FourierTriad.actualRichStage3OperatorClosedIsFalse

canonicalRayleighSaturationConfirmed :
  Variational.canonicalRayleighRatioSaturated ≡ true
canonicalRayleighSaturationConfirmed =
  Variational.canonicalRayleighRatioSaturatedIsTrue

canonicalVariationalCompatibilityStillOpen :
  Variational.canonicalVariationalCompatibilityClosed ≡ false
canonicalVariationalCompatibilityStillOpen =
  Variational.canonicalVariationalCompatibilityClosedIsFalse
