module DASHI.Moonshine.MonsterExceptionalActorScopedMaxCutExact where

------------------------------------------------------------------------
-- ACTOR-SCOPED MONSTER -> EXCEPTIONAL MAX-CUT
--
-- The 53 residual and the 12+78 normalizer decomposition are not the same
-- representation-theoretic statement. Current source-backed repo authority
-- says:
--
--   * central C3 observer:      65663 = 65610 + 53;
--   * full N(3B)/Suz observer:  65663 = 65520 + 143;
--   * the published 143 is irreducible at the latter level.
--
-- Thus 143 = 90 + 53 is reconciliation arithmetic, not a normalizer-stable
-- 90 ⊕ 53 theorem. The exceptional programme therefore forks by actor:
--
--   central-C3 / conformal-fixed-line:
--       actual 53 residual -> reduced Albert/F4 same-action recognition;
--
--   full normalizer:
--       actual Fin90 inertia -> 12 + 78 -> E6 -> F4 + 26 recognition.
--
-- Source attribution remains with the Wilson/Barraclough--Wilson source owners
-- imported below.  The generic actor-scoped recognition contract consumed in
-- this file is a DASHI formalization/adapter and does not replace source
-- representation-theoretic authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)

import DASHI.Foundations.ActorScopedSameObjectExact as ActorScoped
import DASHI.Wikimedia.IbrahimMonster53ActorRestrictionWilsonSnowballCorrectionExact as Actor53
import DASHI.Moonshine.Base369MonsterFiftyFourFiveModeResidualActionBidiExact as Residual54
import DASHI.Moonshine.MonsterAlbertF4ProofRelevantRecognitionExact as F4
import DASHI.Moonshine.MonsterAlbertFiftyThreeProofRelevantWeldExact as Weld
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Ninety
import DASHI.Moonshine.Base369Monster3BSeventyEightExceptionalE6BidiExact as E6

------------------------------------------------------------------------
-- 1. Source-backed actor split.
------------------------------------------------------------------------

data ExceptionalActorScope : Set where
  centralC3Scope : ExceptionalActorScope
  conformalFixedLineScope : ExceptionalActorScope
  fullNormalizerScope : ExceptionalActorScope
  suzukiCoverScope : ExceptionalActorScope

scopePromotionStatus : ExceptionalActorScope → Actor53.ActorPromotionStatus
scopePromotionStatus centralC3Scope = Actor53.carrierAvailableActionUnpaid
scopePromotionStatus conformalFixedLineScope = Actor53.carrierAvailableActionUnpaid
scopePromotionStatus fullNormalizerScope = Actor53.publishedIrreducibilityBlocksNaiveSplit
scopePromotionStatus suzukiCoverScope = Actor53.publishedIrreducibilityBlocksNaiveSplit

centralC3ResidualLaneIsActionUnpaid :
  scopePromotionStatus centralC3Scope ≡ Actor53.carrierAvailableActionUnpaid
centralC3ResidualLaneIsActionUnpaid = refl

fullNormalizerBlocksNaive53Split :
  scopePromotionStatus fullNormalizerScope
  ≡ Actor53.publishedIrreducibilityBlocksNaiveSplit
fullNormalizerBlocksNaive53Split = refl

suzukiCoverBlocksNaive53Split :
  scopePromotionStatus suzukiCoverScope
  ≡ Actor53.publishedIrreducibilityBlocksNaiveSplit
suzukiCoverBlocksNaive53Split = refl

------------------------------------------------------------------------
-- 2. Central-C3 / conformal-fixed-line target.
------------------------------------------------------------------------

record CentralResidualExceptionalRecognition : Set₁ where
  constructor central-residual-exceptional-recognition
  field
    actorScope : ExceptionalActorScope
    scopeIsAdmissibleResidualActor :
      (actorScope ≡ centralC3Scope) ⊎
      (actorScope ≡ conformalFixedLineScope)

    strictAlbertF4Recognition :
      F4.ProofRelevantMonsterAlbertF4Recognition

    ActualActorScopeWitness : Set
    actualActorReallyHasSelectedScope : ActualActorScopeWitness

open CentralResidualExceptionalRecognition public

centralActualResidualAction :
  CentralResidualExceptionalRecognition →
  Residual54.ActualFiftyFourFiveModeResidualActionRecognition
centralActualResidualAction recognition =
  Weld.recognition
    (F4.transportedMonsterAction
      (strictAlbertF4Recognition recognition))

------------------------------------------------------------------------
-- 3. Full-normalizer exceptional target: 90 -> 12+78 -> E6 -> F4+26.
------------------------------------------------------------------------

record NormalizerE6F4Recognition {source}
  (attachment : Ninety.ActualMultiplicityTwelveSeventyEightAttachment source)
  : Set₁ where
  constructor normalizer-e6-f4-recognition
  field
    e6Recognition : E6.ActualSeventyEightE6Recognition attachment

    F4Carrier : Set
    TracelessAlbert26 : Set

    f4Action :
      Ninety.MultiplicityInertia attachment → F4Carrier → F4Carrier
    traceless26Action :
      Ninety.MultiplicityInertia attachment →
      TracelessAlbert26 → TracelessAlbert26

    splitE6 :
      E6.E6Carrier e6Recognition →
      F4Carrier ⊎ TracelessAlbert26
    combineE6 :
      F4Carrier ⊎ TracelessAlbert26 →
      E6.E6Carrier e6Recognition

    combineAfterSplit :
      (state : E6.E6Carrier e6Recognition) →
      combineE6 (splitE6 state) ≡ state
    splitAfterCombine :
      (state : F4Carrier ⊎ TracelessAlbert26) →
      splitE6 (combineE6 state) ≡ state

    f4SummandStableUnderSameE6Action :
      (inertia : Ninety.MultiplicityInertia attachment) →
      (state : F4Carrier) →
      splitE6
        (E6.e6Action e6Recognition inertia (combineE6 (inj₁ state)))
      ≡ inj₁ (f4Action inertia state)

    traceless26StableUnderSameE6Action :
      (inertia : Ninety.MultiplicityInertia attachment) →
      (state : TracelessAlbert26) →
      splitE6
        (E6.e6Action e6Recognition inertia (combineE6 (inj₂ state)))
      ≡ inj₂ (traceless26Action inertia state)

open NormalizerE6F4Recognition public

normalizerActorScopedDecomposition :
  {source : Set} →
  {attachment : Ninety.ActualMultiplicityTwelveSeventyEightAttachment source} →
  (recognition : NormalizerE6F4Recognition attachment) →
  ActorScoped.ActorScopedSumDecomposition
    (Ninety.MultiplicityInertia attachment)
    (E6.E6Carrier (e6Recognition recognition))
    (F4Carrier recognition)
    (TracelessAlbert26 recognition)
    (E6.e6Action (e6Recognition recognition))
    (f4Action recognition)
    (traceless26Action recognition)
normalizerActorScopedDecomposition {attachment = attachment} recognition =
  ActorScoped.actor-scoped-sum-decomposition
    (ActorScoped.actor-scoped-same-object
      (splitE6 recognition)
      (combineE6 recognition)
      (combineAfterSplit recognition)
      (splitAfterCombine recognition)
      intertwines)
  where
  intertwines :
    (inertia : Ninety.MultiplicityInertia attachment) →
    (state : E6.E6Carrier (e6Recognition recognition)) →
    splitE6 recognition
      (E6.e6Action (e6Recognition recognition) inertia state)
    ≡ ActorScoped.sumAction
        (f4Action recognition)
        (traceless26Action recognition)
        inertia
        (splitE6 recognition state)
  intertwines inertia state with splitE6 recognition state
  ... | inj₁ left =
    f4SummandStableUnderSameE6Action recognition inertia left
  ... | inj₂ right =
    traceless26StableUnderSameE6Action recognition inertia right

------------------------------------------------------------------------
-- 4. Wrong-type firewalls.
------------------------------------------------------------------------

data Arithmetic143Equals90Plus53CreatesNormalizerSubmodules : Set where
data CentralResidualCreatesSuzukiStableResidual : Set where
data E6Dimension78CreatesE6ActionRecognition : Set where
data NormalizerE6RecognitionCreatesCentralResidual53 : Set where

arithmetic143DoesNotCreateNormalizerSplit :
  Arithmetic143Equals90Plus53CreatesNormalizerSubmodules → ⊥
arithmetic143DoesNotCreateNormalizerSplit ()

centralResidualDoesNotCreateSuzukiResidual :
  CentralResidualCreatesSuzukiStableResidual → ⊥
centralResidualDoesNotCreateSuzukiResidual ()

e6DimensionDoesNotCreateAction :
  E6Dimension78CreatesE6ActionRecognition → ⊥
e6DimensionDoesNotCreateAction ()

normalizerE6DoesNotBackCreateCentral53 :
  NormalizerE6RecognitionCreatesCentralResidual53 → ⊥
normalizerE6DoesNotBackCreateCentral53 ()

------------------------------------------------------------------------
-- 5. Terminal status.
------------------------------------------------------------------------

record ActorScopedExceptionalBoundary : Set where
  constructor actor-scoped-exceptional-boundary
  field
    centralC3ResidualCharacterPaid : Bool
    finite53CarrierDeletionPaid : Bool
    fullNormalizer65520Plus143Paid : Bool
    published143IrreducibilityRespected : Bool
    normalizerNative12Plus78TargetAvailable : Bool
    centralResidualAndNormalizer90Separated : Bool
    centralLaneUsesSingleActualActionObject : Bool
    normalizerF4Plus26RequiresLiteralStabilityEquations : Bool
    genericActorScopedDecompositionConsumed : Bool

    central53ActualActionPaid : Bool
    strictCentralMonsterF4IntertwinerPaid : Bool
    actualFin90InertiaAttachmentPaid : Bool
    actual78E6IntertwinerPaid : Bool
    normalizerE6ToF4Plus26IntertwinerPaid : Bool

canonicalActorScopedExceptionalBoundary : ActorScopedExceptionalBoundary
canonicalActorScopedExceptionalBoundary =
  actor-scoped-exceptional-boundary
    true true true true true true true true true
    false false false false false
