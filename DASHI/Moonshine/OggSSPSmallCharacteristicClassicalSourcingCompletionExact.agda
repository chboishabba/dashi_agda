module DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourcingCompletionExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC CLASSICAL SOURCING COMPLETION
--
-- "Complete classical sourcing" has a fail-closed meaning here:
--
--   * every claim actually found in the classical literature has a typed
--     source match;
--   * every repository reconstruction is labelled repository-only;
--   * no citation is allowed to promote the exact DASHI 3-state/10-state
--     presentations to classical same-object theorems.
--
-- Thus sourcing can be complete while same-object identification remains
-- false/open.  This is intentional and follows the repository attribution rule.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Atlas
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalClaimMatchExact as Claims
import DASHI.Moonshine.OggSSPP3F9ExtensionQuotientSourceExact as P3Source
import DASHI.Moonshine.OggSSPP2RetainedCMMarkedSourceExact as P2Source
import DASHI.Moonshine.OggSSPArithmeticTo369InhabitedExact as Inhabited
import DASHI.Moonshine.OggSSPArithmeticIndependent369FrontierExact as Frontier
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as P3Local
import DASHI.Moonshine.OggSSPP2Gamma04DrinfeldLevelNoGoExact as P2Gamma04
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as P2Inertia
import DASHI.Moonshine.OggSSPP2OrientedInertiaTenStateRecognitionExact as P2Ten
import DASHI.Moonshine.OggSSPP2OrientedUnorientedInertiaStackCandidateExact as P2Stack
import DASHI.Moonshine.OggSSPClassicalCarrierToIndependent369RecognitionExact as Classical369
import DASHI.Moonshine.OggSSPP3DeligneRapoportStratumCodeExact as P3StratumCode
import DASHI.Moonshine.OggSSPP2OrientedInertiaModuliProblemExact as P2Moduli

------------------------------------------------------------------------
-- 1. Canonical sourced surfaces.
------------------------------------------------------------------------

atlasBoundary :
  Atlas.SmallCharacteristicClassicalSourcingBoundary
atlasBoundary =
  Atlas.canonicalSmallCharacteristicClassicalSourcingBoundary

claimBoundary :
  Claims.ClassicalClaimMatchBoundary
claimBoundary =
  Claims.canonicalClassicalClaimMatchBoundary

p3SourceBoundary :
  P3Source.P3ExtensionQuotientSourceBoundary
p3SourceBoundary =
  P3Source.canonicalP3ExtensionQuotientSourceBoundary

p2SourceBoundary :
  P2Source.P2RetainedCMMarkedSourceBoundary
p2SourceBoundary =
  P2Source.canonicalP2RetainedCMMarkedSourceBoundary

inhabitedBoundary :
  Inhabited.ArithmeticTo369InhabitedBoundary
inhabitedBoundary =
  Inhabited.canonicalArithmeticTo369InhabitedBoundary

frontierBoundary :
  Frontier.ArithmeticIndependent369Frontier
frontierBoundary =
  Frontier.canonicalArithmeticIndependent369Frontier

------------------------------------------------------------------------
-- 2. Completion policy.
------------------------------------------------------------------------

record ClassicalSourcingCompletion : Set where
  constructor classical-sourcing-completion
  field
    coarseP2ClassificationSourced : Bool
    coarseP3ClassificationSourced : Bool
    smallCharacteristicAutomorphismsSourced : Bool
    deuringReductionSourced : Bool
    normalizedOptimalEmbeddingSourced : Bool
    badPrimeDrinfeldLevelFrameworkSourced : Bool
    gamma0PrimePowerStackFrameworkSourced : Bool
    inertiaStackConjugacyFrameworkSourced : Bool
    p3DeligneRapoportLocalStrataSourced : Bool
    p2UniqueGamma04DrinfeldLevelSourced : Bool
    p2TwoOrientationFactorSourced : Bool
    p2BinaryTetrahedralSevenClassesSourced : Bool
    oggContextSourced : Bool

    p3InternalSourceInhabited : Bool
    p2InternalSourceInhabited : Bool
    p3ForwardRecognitionInhabited : Bool
    p2ForwardRecognitionInhabited : Bool

    p3AbstractThreeStateC2SetClassicallyRealized : Bool
    p3F9CoordinateGeometricallyIdentified : Bool
    p3F9StratumCodeInterpretationPaid : Bool
    p2Gamma04TenPointInterpretationRejected : Bool
    p2FiveInertiaOrbitCarrierConstructed : Bool
    p2TenStateHasClassicallySourcedFactorization : Bool
    p2OrientedUnorientedInertiaProductNamedClassically : Bool
    p2SpecificEnrichedModuliProblemDefined : Bool
    p3ClassicalCarrierTo369RecognitionPaid : Bool
    p2ClassicalCarrierTo369RecognitionPaid : Bool
    p3ExactThreeStatePresentationAttributedAsClassical : Bool
    p2ExactTenStatePresentationAttributedAsClassical : Bool

    everySupportedClassicalClaimHasSourceMatch : Bool
    everyUnsupportedPromotionExplicitlyBlocked : Bool
    classicalSourcingComplete : Bool

canonicalClassicalSourcingCompletion :
  ClassicalSourcingCompletion
canonicalClassicalSourcingCompletion =
  classical-sourcing-completion
    true true true true true true true true true true true true true
    true true true true
    true false true true true true false true true true false false
    true true true

------------------------------------------------------------------------
-- 3. Completion does not collapse attribution grades.
------------------------------------------------------------------------

data SourcingCompletionMeansSameObjectIdentification : Set where
data SourcingCompletionMeansFiniteCarrierIsClassical : Set where
data SourcingCompletionMeansCitationsImportProof : Set where

sourcingCompletionDoesNotMeanSameObjectIdentification :
  SourcingCompletionMeansSameObjectIdentification -> ⊥
sourcingCompletionDoesNotMeanSameObjectIdentification ()

sourcingCompletionDoesNotMakeFiniteCarrierClassical :
  SourcingCompletionMeansFiniteCarrierIsClassical -> ⊥
sourcingCompletionDoesNotMakeFiniteCarrierClassical ()

sourcingCompletionDoesNotMeanCitationsImportProof :
  SourcingCompletionMeansCitationsImportProof -> ⊥
sourcingCompletionDoesNotMeanCitationsImportProof ()

------------------------------------------------------------------------
-- 4. Live interpretation.
------------------------------------------------------------------------

classicalSourcingComplete : Bool
classicalSourcingComplete =
  ClassicalSourcingCompletion.classicalSourcingComplete
    canonicalClassicalSourcingCompletion

classicalSourcingCompleteIsTrue :
  classicalSourcingComplete ≡ true
classicalSourcingCompleteIsTrue = refl

p3ClassicalSameObjectStillFalse : Bool
p3ClassicalSameObjectStillFalse = false

p2ClassicalSameObjectStillFalse : Bool
p2ClassicalSameObjectStillFalse = false
