module DASHI.Physics.ExoticGravity.SuperconductingConstitutiveNegativeGScopeWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Interop.SourceAttributionShapePolicyExact as Shape
import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as SignedG
import DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact as Split
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeBidiExact as Scope
import DASHI.Physics.ExoticGravity.SuperconductingResidualCouplingNegativeGInterpretationBidiExact as Interpretation

------------------------------------------------------------------------
-- CONSTITUTIVE SIGN REVERSAL -> MATERIAL-EFFECTIVE NEGATIVE-G INTERPRETATION
--
-- This is a DASHI internal model weld, not an externally attributed scientific
-- claim.  The source/constitutive split already exists in-repo.  We add only
-- the missing sign and scope coordinates required before a constitutive change
-- can be interpreted as a material-effective negative gravitational coupling.
------------------------------------------------------------------------

record ConstitutiveNegativeGReceipt : Set₁ where
  constructor constitutive-negative-g-receipt
  field
    factorization : Split.SourceConstitutiveFactorization

    enhancementCoordinate : Split.EnhancementCoordinate
    enhancementIsConstitutive :
      enhancementCoordinate ≡ Split.constitutiveChange

    FixedMeasuredSourceComparison : Set
    fixedMeasuredSourceComparison : FixedMeasuredSourceComparison

    standardCoefficientSign : SignedG.CouplingSign
    standardCoefficientIsPositive :
      standardCoefficientSign ≡ SignedG.positiveCoupling

    candidateCoefficientSign : SignedG.CouplingSign
    candidateCoefficientIsNegative :
      candidateCoefficientSign ≡ SignedG.negativeCoupling

    residualInterpretation : Interpretation.ResidualInterpretation
    interpretationIsMaterialEffective :
      residualInterpretation
        ≡ Interpretation.materialEffectiveGCouplingModification

    couplingScope : Scope.CouplingScope
    couplingScopeIsMaterialEffective :
      couplingScope ≡ Scope.materialEffectiveCoupling

    ConstitutiveSignMapping : Set
    constitutiveSignMapping : ConstitutiveSignMapping

open ConstitutiveNegativeGReceipt public

------------------------------------------------------------------------
-- Coarse-product collision.
--
-- The sign of eta_B = eta_C * eta_J cannot tell whether the source factor or
-- constitutive factor supplied the negative sign.
------------------------------------------------------------------------

data FactorSign : Set where
  positiveFactor negativeFactor : FactorSign

data SignFactorWorld : Set where
  negativeSourcePositiveConstitutive : SignFactorWorld
  positiveSourceNegativeConstitutive : SignFactorWorld

data CoarseFieldSign : Set where
  negativeFieldRatio : CoarseFieldSign

data SignOrigin : Set where
  sourceSignOrigin constitutiveSignOrigin : SignOrigin

coarseFieldSign : SignFactorWorld → CoarseFieldSign
coarseFieldSign _ = negativeFieldRatio

sourceFactorSign : SignFactorWorld → FactorSign
sourceFactorSign negativeSourcePositiveConstitutive = negativeFactor
sourceFactorSign positiveSourceNegativeConstitutive = positiveFactor

constitutiveFactorSign : SignFactorWorld → FactorSign
constitutiveFactorSign negativeSourcePositiveConstitutive = positiveFactor
constitutiveFactorSign positiveSourceNegativeConstitutive = negativeFactor

signOrigin : SignFactorWorld → SignOrigin
signOrigin negativeSourcePositiveConstitutive = sourceSignOrigin
signOrigin positiveSourceNegativeConstitutive = constitutiveSignOrigin

coarseFieldCollision :
  coarseFieldSign negativeSourcePositiveConstitutive
    ≡ coarseFieldSign positiveSourceNegativeConstitutive
coarseFieldCollision = refl

fieldSignDoesNotDetermineSignOrigin :
  signOrigin negativeSourcePositiveConstitutive
    ≡ signOrigin positiveSourceNegativeConstitutive → ⊥
fieldSignDoesNotDetermineSignOrigin ()

record RefinedFactorSignObserver : Set where
  constructor refined-factor-sign-observer
  field
    sourceSign : FactorSign
    constitutiveSign : FactorSign
    origin : SignOrigin

refinedObserve : SignFactorWorld → RefinedFactorSignObserver
refinedObserve world =
  refined-factor-sign-observer
    (sourceFactorSign world)
    (constitutiveFactorSign world)
    (signOrigin world)

refinedWorldsDistinct :
  refinedObserve negativeSourcePositiveConstitutive
    ≡ refinedObserve positiveSourceNegativeConstitutive → ⊥
refinedWorldsDistinct ()

------------------------------------------------------------------------
-- Attribution shape: this is an internal derived theorem/model adapter.
------------------------------------------------------------------------

attributionShape : Shape.RequiredAttributionShape
attributionShape = Shape.requiredAttributionShape Shape.internalDerivedTheorem

record ConstitutiveNegativeGBoundary : Set where
  constructor constitutive-negative-g-boundary
  field
    negativeTotalFieldRatioAutomaticallyMeansNegativeEffectiveG : Bool
    constitutiveChangeWithoutSignReceiptMeansNegativeEffectiveG : Bool
    fixedMeasuredSourceRequired : Bool
    coefficientSignReversalRequired : Bool
    materialEffectiveScopeRequired : Bool
    sourceSignReversalEqualsConstitutiveSignReversal : Bool
    internalWeldNeedsFreshExternalCitation : Bool
    materialEffectiveInterpretationProvesUniversalNegativeG : Bool

canonicalConstitutiveNegativeGBoundary : ConstitutiveNegativeGBoundary
canonicalConstitutiveNegativeGBoundary =
  constitutive-negative-g-boundary
    false false true true true false false false
