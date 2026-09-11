module DASHI.Reasoning.FibreRoutingProjectionAdequacyCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.FibreRoutingGrokkingMoEBrainCrossPollinationExact as Fibre
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Admissible
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Interop.AdicHypervoxelArgumentTransportBridgeExact as Adic
import DASHI.Wikimedia.NativeConcreteQidGraphProjectionExact as QID
import DASHI.Moonshine.JInvariantFormulaic369FibreObserverRepairExact as Fibre369

------------------------------------------------------------------------
-- FIBRE ROUTING / PROJECTION ADEQUACY CROSS-POLLINATION
------------------------------------------------------------------------

data FlyConsumerQuery : Set where
  hardIdentityQuery : FlyConsumerQuery
  overlapProfileQuery : FlyConsumerQuery

data FlyConsumerAnswer : Set where
  hardIdentityAnswer : Fibre.HardPaintedIdentity → FlyConsumerAnswer
  overlapProfileAnswer : Fibre.PaintedOverlapProfile → FlyConsumerAnswer

flyConsumerAnswer :
  FlyConsumerQuery → Fibre.SelectedROISpecimen → FlyConsumerAnswer
flyConsumerAnswer hardIdentityQuery state =
  hardIdentityAnswer (Fibre.hardPaintedIdentity state)
flyConsumerAnswer overlapProfileQuery state =
  overlapProfileAnswer (Fibre.paintedOverlapProfile state)

flyConsumerSemantics :
  Query.QuerySemantics Fibre.SelectedROISpecimen FlyConsumerQuery FlyConsumerAnswer
flyConsumerSemantics = Query.querySemantics flyConsumerAnswer

hardWinnerAdequateForHardIdentity :
  Query.AdequateFor
    Fibre.hardPaintedIdentity
    flyConsumerSemantics
    hardIdentityQuery
hardWinnerAdequateForHardIdentity =
  Query.factorsForQuery
    (λ identity → hardIdentityAnswer identity)
    (λ state → refl)

hardWinnerOverlapDefect :
  Query.QueryAdequacyDefect
    Fibre.hardPaintedIdentity
    flyConsumerSemantics
    overlapProfileQuery
hardWinnerOverlapDefect =
  Query.queryAdequacyDefect
    Fibre.overlappingROI
    Fibre.parentOnlyROI
    refl
    (λ ())

hardWinnerCannotAnswerOverlapQuery :
  Query.AdequateFor
    Fibre.hardPaintedIdentity
    flyConsumerSemantics
    overlapProfileQuery → ⊥
hardWinnerCannotAnswerOverlapQuery =
  Query.queryAdequacyDefectBlocksFactorisation hardWinnerOverlapDefect

softOverlapAdequateForOverlapQuery :
  Query.AdequateFor
    Fibre.paintedOverlapProfile
    flyConsumerSemantics
    overlapProfileQuery
softOverlapAdequateForOverlapQuery =
  Query.factorsForQuery
    (λ profile → overlapProfileAnswer profile)
    (λ state → refl)

hardWinnerOverlapNonFactorability :
  NonFactor.NonFactorabilityWitness
    Fibre.hardPaintedIdentity
    Fibre.paintedOverlapProfile
hardWinnerOverlapNonFactorability =
  NonFactor.nonFactorabilityWitness
    Fibre.overlappingROI
    Fibre.parentOnlyROI
    refl
    (λ ())

hardWinnerRechartCannotRecoverOverlap :
  ∀ {Recharted : Set} →
  (rechart : Fibre.HardPaintedIdentity → Recharted) →
  NonFactor.FactorsThrough
    (λ state → rechart (Fibre.hardPaintedIdentity state))
    Fibre.paintedOverlapProfile → ⊥
hardWinnerRechartCannotRecoverOverlap rechart =
  NonFactor.rechartingCannotRecoverErasedPhenomenon
    rechart hardWinnerOverlapNonFactorability

data Unit : Set where unit : Unit

data FlyProjectionModel : Set where
  hardWinnerModel : FlyProjectionModel
  softOverlapModel : FlyProjectionModel

projectionAdmissible : FlyProjectionModel → Set
projectionAdmissible hardWinnerModel = Unit
projectionAdmissible softOverlapModel = Unit

projectionConsumerAdequate : FlyProjectionModel → Set₁
projectionConsumerAdequate hardWinnerModel =
  Query.AdequateFor
    Fibre.hardPaintedIdentity
    flyConsumerSemantics
    overlapProfileQuery
projectionConsumerAdequate softOverlapModel =
  Query.AdequateFor
    Fibre.paintedOverlapProfile
    flyConsumerSemantics
    overlapProfileQuery

projectionDescriptionLength : FlyProjectionModel → Nat
projectionDescriptionLength hardWinnerModel = 1
projectionDescriptionLength softOverlapModel = 2

data ProjectionRefines : FlyProjectionModel → FlyProjectionModel → Set where
  hardReflexive : ProjectionRefines hardWinnerModel hardWinnerModel
  softReflexive : ProjectionRefines softOverlapModel softOverlapModel
  hardToSoft : ProjectionRefines hardWinnerModel softOverlapModel

projectionModelReference : FlyProjectionModel → String
projectionModelReference hardWinnerModel =
  "unique-maximum painted-domain projection"
projectionModelReference softOverlapModel =
  "overlapping painted-domain profile"

flyProjectionProblem : Admissible.ConsumerMDLProblem
flyProjectionProblem =
  Admissible.consumerMDLProblem
    FlyProjectionModel
    projectionAdmissible
    projectionConsumerAdequate
    projectionDescriptionLength
    ProjectionRefines
    projectionModelReference
    "finite illustrative code length; ranking only after admissibility and consumer adequacy"
    "Fly overlap-profile consumer"

-- Keep the universe-polymorphic query defect as the proof of insufficiency, but
-- use a first-order token for ConsumerCounterexample's Set-sized witness field.
data HardOverlapFailureWitness : Set where
  hardOverlapFailureWitness : HardOverlapFailureWitness

hardProjectionCounterexample :
  Admissible.ConsumerCounterexample flyProjectionProblem hardWinnerModel
hardProjectionCounterexample =
  Admissible.consumerCounterexample
    HardOverlapFailureWitness
    hardOverlapFailureWitness
    hardWinnerCannotAnswerOverlapQuery
    "hard winner identifies overlappingROI and parentOnlyROI"
    "the overlap-profile consumer distinguishes those states; exact query defect retained in hardWinnerOverlapDefect"

hardToSoftLocalRepair :
  Admissible.LocalRefinementRepair
    flyProjectionProblem
    hardWinnerModel
    softOverlapModel
hardToSoftLocalRepair =
  Admissible.localRefinementRepair
    hardProjectionCounterexample
    hardToSoft
    unit
    softOverlapAdequateForOverlapQuery
    "retain the same-point overlap fibre that the hard winner erased"

softRepairIsEligible :
  Admissible.Eligible flyProjectionProblem softOverlapModel
softRepairIsEligible =
  Admissible.repairProvidesEligibleRefinement hardToSoftLocalRepair

repairRemainsConsumerIndexed :
  Repair.repairIsConsumerIndexed Repair.canonicalConsumerFibreRepairBoundary ≡ true
repairRemainsConsumerIndexed = refl

repairOneWitnessDoesNotProveGlobalSufficiency :
  Repair.separatingOneWitnessAloneProvesGlobalSufficiency
    Repair.canonicalConsumerFibreRepairBoundary ≡ false
repairOneWitnessDoesNotProveGlobalSufficiency = refl

adicRefinementNeedsTypedSourceTarget :
  Adic.refinementNeedsTypedSourceTarget
    Adic.canonicalAdicArgumentTransportBoundary ≡ true
adicRefinementNeedsTypedSourceTarget = refl

adicProjectedShadowIsNotDefinitionalIdentity :
  Adic.projectedShadowEqualsDefinitionalIdentity
    Adic.canonicalAdicArgumentTransportBoundary ≡ false
adicProjectedShadowIsNotDefinitionalIdentity = refl

recursiveAddressDoesNotCreatePAdicPhysics :
  Admissible.recursiveAddressAutomaticallyMeansPAdicPhysics
    Admissible.canonicalAdmissibleConsumerMDLBoundary ≡ false
recursiveAddressDoesNotCreatePAdicPhysics =
  Admissible.recursiveAddressAutomaticallyMeansPAdicPhysicsIsFalse
    Admissible.canonicalAdmissibleConsumerMDLBoundary

qidProjectionIsIntentionallyLossy :
  QID.projectionRetainsWholeNativeStatementLanguage
    QID.canonicalNativeConcreteProjectionBoundary ≡ false
qidProjectionIsIntentionallyLossy = refl

qidProjectionDoesNotAdmitArbitraryProperties :
  QID.arbitraryPropertiesProjectToKernel
    QID.canonicalNativeConcreteProjectionBoundary ≡ false
qidProjectionDoesNotAdmitArbitraryProperties = refl

nineObserverMayNeedSamePointContext :
  Fibre369.c9MayDependOnSamePointContext
    Fibre369.canonicalFibreObserverRepairBoundary ≡ true
nineObserverMayNeedSamePointContext = refl

legacyPhaseOnlyAgreementIsNotAutomatic :
  Fibre369.legacyPhaseOnlyAgreementAutomatic
    Fibre369.canonicalFibreObserverRepairBoundary ≡ false
legacyPhaseOnlyAgreementIsNotAutomatic = refl

record ProjectionRepairCrossPollinationBoundary : Set where
  constructor projectionRepairCrossPollinationBoundary
  field
    adequacyIsConsumerIndexed : Bool
    collisionCanRefuteAdequacy : Bool
    postprocessingCoarseProjectionCanRecoverErasedAxis : Bool
    admissibilityAndAdequacyPrecedeRanking : Bool
    localCounterexampleMayDriveTypedRefinement : Bool
    oneLocalRepairProvesUniversalSufficiency : Bool
    refinementKeepsTypedSourceTarget : Bool
    recursiveRefinementAutomaticallyMeansPAdicPhysics : Bool
    lossyProjectionMayStillServeDeclaredConsumer : Bool
    lossyProjectionBecomesSourceAuthority : Bool
    samePointContextMayBeRequiredBeyondCoarseObserver : Bool
    nuisanceControlAutomaticallyEstablishesPhysicalMechanism : Bool

canonicalProjectionRepairCrossPollinationBoundary :
  ProjectionRepairCrossPollinationBoundary
canonicalProjectionRepairCrossPollinationBoundary =
  projectionRepairCrossPollinationBoundary
    true
    true
    false
    true
    true
    false
    true
    false
    true
    false
    true
    false
