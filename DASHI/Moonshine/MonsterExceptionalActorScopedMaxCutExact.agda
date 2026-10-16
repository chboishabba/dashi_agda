module DASHI.Moonshine.MonsterExceptionalActorScopedMaxCutExact where

------------------------------------------------------------------------
-- ACTOR-SCOPED MONSTER -> EXCEPTIONAL MAX-CUT
--
-- The 53 residual and the 12+78 normalizer decomposition are not the same
-- representation-theoretic statement.  Current source-backed repo authority
-- says:
--
--   * under the central C3 observer the fixed sector is 65610 + 53;
--   * under the full N(3B)/Suz observer it is 65520 + 143, with the 143
--     published as irreducible at that level;
--   * 143 = 90 + 53 is therefore reconciliation arithmetic, not a stable
--     N(3B)/Suz direct sum.
--
-- Consequently the exceptional programme must fork by actor:
--
--   central-C3 / conformal-fixed-line lane:
--       actual 53 residual -> reduced Albert/F4 same-action target;
--
--   full-normalizer lane:
--       actual Fin90 inertia -> 12 + 78 -> E6 -> F4 + 26 target.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum.Base using (_⊎_)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimMonster53ActorRestrictionWilsonSnowballCorrectionExact as Actor53
import DASHI.Moonshine.Base369MonsterFiftyFourFiveModeResidualActionBidiExact as Residual54
import DASHI.Moonshine.MonsterAlbertF4ProofRelevantRecognitionExact as F4
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Ninety
import DASHI.Moonshine.Base369Monster3BSeventyEightExceptionalE6BidiExact as E6

------------------------------------------------------------------------
-- 1. The source-backed actor split is executable, not prose.
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

    actualResidualAction :
      Residual54.ActualFiftyFourFiveModeResidualActionRecognition

    strictAlbertF4Recognition :
      F4.ProofRelevantMonsterAlbertF4Recognition

    SameActualActionWitness : Set
    sameActualAction : SameActualActionWitness

open CentralResidualExceptionalRecognition public

------------------------------------------------------------------------
-- 3. Full-normalizer exceptional target: 90 -> 12+78 -> E6 -> F4+26.
--
-- This is the correct place for the normalizer-native exceptional comparison.
-- It never routes through a putative normalizer-stable 53 summand.
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

    F4Plus26StabilityWitness : Set
    f4Plus26StableUnderSameNormalizerAction : F4Plus26StabilityWitness

    SameE6ActionWitness : Set
    sameE6Action : SameE6ActionWitness

open NormalizerE6F4Recognition public

------------------------------------------------------------------------
-- 4. Wrong-type firewalls.
------------------------------------------------------------------------

data Arithmetic143Equals90Plus53CreatesNormalizerSubmodules : Set where
data CentralResidualCreatesSuzukiStableResidual : Set where
data E6Dimension78CreatesE6ActionRecognition : Set where

arithmetic143DoesNotCreateNormalizerSplit :
  Arithmetic143Equals90Plus53CreatesNormalizerSubmodules → ⊥
arithmetic143DoesNotCreateNormalizerSplit ()

centralResidualDoesNotCreateSuzukiResidual :
  CentralResidualCreatesSuzukiStableResidual → ⊥
centralResidualDoesNotCreateSuzukiResidual ()

e6DimensionDoesNotCreateAction :
  E6Dimension78CreatesE6ActionRecognition → ⊥
e6DimensionDoesNotCreateAction ()

------------------------------------------------------------------------
-- 5. Terminal status: actor scoping itself is paid; both actual action
--    recognitions remain proof obligations.
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

    central53ActualActionPaid : Bool
    strictCentralMonsterF4IntertwinerPaid : Bool
    actualFin90InertiaAttachmentPaid : Bool
    actual78E6IntertwinerPaid : Bool
    normalizerE6ToF4Plus26IntertwinerPaid : Bool

canonicalActorScopedExceptionalBoundary : ActorScopedExceptionalBoundary
canonicalActorScopedExceptionalBoundary =
  actor-scoped-exceptional-boundary
    true true true true true true
    false false false false false
