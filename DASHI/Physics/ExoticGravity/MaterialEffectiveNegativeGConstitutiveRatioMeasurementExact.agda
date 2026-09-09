module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGConstitutiveRatioMeasurementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as SignedG
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryGRComparatorCompilationExact as GR
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryOrdinaryModelClosureWeldExact as Ordinary
import DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact as Split
import DASHI.Physics.ExoticGravity.SuperconductingConstitutiveNegativeGScopeWeldExact as NegativeG
import DASHI.Physics.ExoticGravity.SuperconductingResidualCouplingNegativeGInterpretationBidiExact as Interpretation
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeBidiExact as Scope

------------------------------------------------------------------------
-- TYPED PAYMENT FOR constitutiveRatioLeaf
--
-- The historical eta_C formula is string-valued.  This owner supplies the
-- same-object measurement carrier required before its sign can feed the
-- existing material-effective negative-G interpretation weld.
------------------------------------------------------------------------

record ConstitutiveRatioMeasurementReceipt
    (prediction : GR.OrdinaryGRPredictionReceipt) : Set₂ where
  constructor constitutive-ratio-measurement-receipt
  field
    ordinaryModelClosure : Ordinary.TypedOrdinaryModelClosureWeld prediction

    apparatusIdentity : String
    observableChannel : String
    factorization : Split.SourceConstitutiveFactorization

    OrdinaryRegimeResponseReceipt : Set
    ordinaryRegimeResponseReceipt : OrdinaryRegimeResponseReceipt

    CoherentRegimeResponseReceipt : Set
    coherentRegimeResponseReceipt : CoherentRegimeResponseReceipt

    FixedMeasuredSourceComparison : Set
    fixedMeasuredSourceComparison : FixedMeasuredSourceComparison

    SameGeometryReceipt : Set
    sameGeometryReceipt : SameGeometryReceipt

    SameObservableChannelReceipt : Set
    sameObservableChannelReceipt : SameObservableChannelReceipt

    SameCalibrationReceipt : Set
    sameCalibrationReceipt : SameCalibrationReceipt

    StandardCoefficientNonzeroReceipt : Set
    standardCoefficientNonzeroReceipt : StandardCoefficientNonzeroReceipt

    standardCoefficientSign : SignedG.CouplingSign
    standardCoefficientIsPositive :
      standardCoefficientSign ≡ SignedG.positiveCoupling

    candidateCoefficientSign : SignedG.CouplingSign
    candidateCoefficientIsNegative :
      candidateCoefficientSign ≡ SignedG.negativeCoupling

    IndependentReplicationReceipt : Set
    independentReplicationReceipt : IndependentReplicationReceipt

    ConstitutiveSignMapping : Set
    constitutiveSignMapping : ConstitutiveSignMapping

    SamePredictionIdentityReceipt : Set
    samePredictionIdentityReceipt : SamePredictionIdentityReceipt

open ConstitutiveRatioMeasurementReceipt public

------------------------------------------------------------------------
-- Direct compiler into the existing negative-G interpretation carrier.
------------------------------------------------------------------------

compileConstitutiveNegativeGReceipt :
  {prediction : GR.OrdinaryGRPredictionReceipt} →
  ConstitutiveRatioMeasurementReceipt prediction →
  NegativeG.ConstitutiveNegativeGReceipt
compileConstitutiveNegativeGReceipt receipt =
  NegativeG.constitutive-negative-g-receipt
    (ConstitutiveRatioMeasurementReceipt.factorization receipt)
    Split.constitutiveChange
    refl
    (ConstitutiveRatioMeasurementReceipt.FixedMeasuredSourceComparison receipt)
    (ConstitutiveRatioMeasurementReceipt.fixedMeasuredSourceComparison receipt)
    (ConstitutiveRatioMeasurementReceipt.standardCoefficientSign receipt)
    (ConstitutiveRatioMeasurementReceipt.standardCoefficientIsPositive receipt)
    (ConstitutiveRatioMeasurementReceipt.candidateCoefficientSign receipt)
    (ConstitutiveRatioMeasurementReceipt.candidateCoefficientIsNegative receipt)
    Interpretation.materialEffectiveGCouplingModification
    refl
    Scope.materialEffectiveCoupling
    refl
    (ConstitutiveRatioMeasurementReceipt.ConstitutiveSignMapping receipt)
    (ConstitutiveRatioMeasurementReceipt.constitutiveSignMapping receipt)

------------------------------------------------------------------------
-- Non-collapse / promotion firewall.
------------------------------------------------------------------------

record ConstitutiveRatioMeasurementBoundary : Set where
  constructor constitutive-ratio-measurement-boundary
  field
    etaCStringAlonePaysConstitutiveRatio : Bool
    oneRegimeResponseAlonePaysConstitutiveRatio : Bool
    ordinaryModelClosureAlonePaysConstitutiveRatio : Bool
    fixedMeasuredSourceRequired : Bool
    sameGeometryRequired : Bool
    sameObservableChannelRequired : Bool
    sameCalibrationRequired : Bool
    nonzeroStandardCoefficientRequired : Bool
    coefficientSignReceiptRequired : Bool
    independentReplicationRequired : Bool
    typedRatioMayCompileExistingNegativeGWeld : Bool
    compiledNegativeGWeldProvesUniversalNegativeG : Bool
    compiledNegativeGWeldProvesPhysicalCorrectness : Bool

canonicalConstitutiveRatioMeasurementBoundary :
  ConstitutiveRatioMeasurementBoundary
canonicalConstitutiveRatioMeasurementBoundary =
  constitutive-ratio-measurement-boundary
    false false false true true true true true true true true false false
