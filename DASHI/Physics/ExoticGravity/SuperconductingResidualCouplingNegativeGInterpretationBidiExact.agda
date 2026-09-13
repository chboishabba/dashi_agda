module DASHI.Physics.ExoticGravity.SuperconductingResidualCouplingNegativeGInterpretationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.SuperconductingGravityCouplingResidualBidiExact as Alpha
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeBidiExact as Scope
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- RESIDUAL COUPLING != EFFECTIVE NEGATIVE G
--
-- alpha_SC->grav is already an in-repo diagnostic residual coefficient.  A
-- material-effective G interpretation is a stronger constitutive/model claim.
-- No sign or magnitude of alpha is silently re-labelled as G_eff.
------------------------------------------------------------------------

data ResidualInterpretation : Set where
  additiveGravityChannelResidual : ResidualInterpretation
  materialEffectiveGCouplingModification : ResidualInterpretation
  sourceSpecificGravityResponseModification : ResidualInterpretation
  interpretationUnresolved : ResidualInterpretation

record ResidualInterpretationReceipt : Set where
  constructor residual-interpretation-receipt
  field
    residualModel : Alpha.CouplingResidualModel
    interpretation : ResidualInterpretation
    interpretationCarrier : String
    ConstitutiveMapping : Set
    constitutiveMappingReceipt : ConstitutiveMapping

open ResidualInterpretationReceipt public

------------------------------------------------------------------------
-- Only the material-effective interpretation may be considered for the
-- materialEffectiveCoupling scope, and even then an explicit mapping receipt is
-- required.  The existing alpha model itself does not provide that mapping.
------------------------------------------------------------------------

record MaterialEffectiveGInterpretationWeld
    (receipt : ResidualInterpretationReceipt) : Set where
  constructor material-effective-g-interpretation-weld
  field
    interpretationMatches :
      interpretation receipt ≡ materialEffectiveGCouplingModification
    couplingScope : Scope.CouplingScope
    couplingScopeMatches : couplingScope ≡ Scope.materialEffectiveCoupling
    MappingFromResidualToEffectiveG : Set
    mappingFromResidualToEffectiveG : MappingFromResidualToEffectiveG

open MaterialEffectiveGInterpretationWeld public

------------------------------------------------------------------------
-- Introspective collision: the same coarse reproducible residual-scaling
-- surface can feed different model interpretations.
------------------------------------------------------------------------

data InterpretationFixture : Set where
  additiveResidualFixture effectiveGFixture : InterpretationFixture

data CoarseResidualSurface : Set where
  sameReproducibleResidualScaling : CoarseResidualSurface

coarseObserve : InterpretationFixture → CoarseResidualSurface
coarseObserve _ = sameReproducibleResidualScaling

fixtureInterpretation : InterpretationFixture → ResidualInterpretation
fixtureInterpretation additiveResidualFixture = additiveGravityChannelResidual
fixtureInterpretation effectiveGFixture = materialEffectiveGCouplingModification

coarseResidualCollision :
  coarseObserve additiveResidualFixture ≡ coarseObserve effectiveGFixture
coarseResidualCollision = refl

residualScalingDoesNotDetermineInterpretation :
  fixtureInterpretation additiveResidualFixture
    ≡ fixtureInterpretation effectiveGFixture → ⊥
residualScalingDoesNotDetermineInterpretation ()

------------------------------------------------------------------------
-- Reverse proof-search residuals.
------------------------------------------------------------------------

data ResidualNegativeGInterpretationResidual : Set where
  missingResidualClosure : ResidualNegativeGInterpretationResidual
  missingConstitutiveMapping : ResidualNegativeGInterpretationResidual
  missingEffectiveGScopeIdentity : ResidualNegativeGInterpretationResidual
  missingSameObservableGRComparator : ResidualNegativeGInterpretationResidual
  missingRegimeContrast : ResidualNegativeGInterpretationResidual
  missingScalingDiscriminator : ResidualNegativeGInterpretationResidual
  interpretationContradictionOpen : ResidualNegativeGInterpretationResidual

producerForResidualNegativeGInterpretationResidual :
  ResidualNegativeGInterpretationResidual → Search.ProducerClass
producerForResidualNegativeGInterpretationResidual missingResidualClosure = Search.empiricalEvidenceProducer
producerForResidualNegativeGInterpretationResidual missingConstitutiveMapping = Search.propositionSourceProducer
producerForResidualNegativeGInterpretationResidual missingEffectiveGScopeIdentity = Search.identityProducer
producerForResidualNegativeGInterpretationResidual missingSameObservableGRComparator = Search.identityProducer
producerForResidualNegativeGInterpretationResidual missingRegimeContrast = Search.discriminatorProducer
producerForResidualNegativeGInterpretationResidual missingScalingDiscriminator = Search.discriminatorProducer
producerForResidualNegativeGInterpretationResidual interpretationContradictionOpen = Search.contradictionProducer

record ResidualNegativeGInterpretationBoundary : Set where
  constructor residual-negative-g-interpretation-boundary
  field
    nonzeroAlphaAutomaticallyMeansNegativeEffectiveG : Bool
    negativeResidualAutomaticallyMeansNegativeEffectiveG : Bool
    reproducibleScalingAutomaticallyMeansNegativeEffectiveG : Bool
    explicitConstitutiveMappingRequired : Bool
    materialEffectiveScopeIdentityRequired : Bool
    sameObservableOrdinaryGRComparatorRequired : Bool
    materialRegimeContrastStillRequired : Bool
    effectiveGInterpretationAutomaticallyProvesUniversalNegativeG : Bool
    effectiveGInterpretationAutomaticallyProvesAmyOrLiTorrMechanism : Bool

canonicalResidualNegativeGInterpretationBoundary :
  ResidualNegativeGInterpretationBoundary
canonicalResidualNegativeGInterpretationBoundary =
  residual-negative-g-interpretation-boundary
    false false false true true true true false false

existingAlphaBoundary : Alpha.CouplingPromotionBoundary
existingAlphaBoundary = Alpha.canonicalCouplingPromotionBoundary
