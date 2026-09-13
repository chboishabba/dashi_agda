module DASHI.Wikimedia.IbrahimMonster53ActorRestrictionWilsonSnowballCorrectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Moonshine.Monster3BWilsonPublishedRestrictionReconciliationExact as Wilson
import DASHI.Moonshine.Monster3BRegularC3BulkResidualFiftyThreeBidiExact as C3Residual
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Multiplicity
import DASHI.Wikimedia.IbrahimZetaBase53ExceptionalSkeletonCompletionExact as Carrier53
import DASHI.Wikimedia.IbrahimMonster3BTwelveSeventyEightExceptionalOEISSourceSnowballExact as Exceptional90

------------------------------------------------------------------------
-- ACTOR-TYPED CORRECTION FOR THE 53 RESIDUAL
--
-- There are two legitimate observers of the same fixed 3B degree:
--
--   central C3 observer:      65663 = 65610 + 53
--   full normalizer observer: 65663 = 65520 + 143.
--
-- Wilson's published normalizer restriction identifies 143 as an irreducible
-- constituent at the Suzuki-cover level.  Therefore
--
--   143 = 90 + 53
--
-- is exact arithmetic/reconciliation, NOT a Suz-stable direct-sum theorem.
--
-- The finite Zeta/Base/Albert 54->53 square now has exact carrier maps, but it
-- may only be promoted under an actor for which the deleted line and residual
-- are invariant.  Central-C3/conformal reduction is a candidate context;
-- full N(3B)/Suz stability is explicitly unpaid and contradicted by treating
-- the published irreducible 143 as if it split 90+53.
------------------------------------------------------------------------

centralObserver : Nat
centralObserver = 65610 + 53

normalizerObserver : Nat
normalizerObserver = 65520 + 143

centralObserverIs65663 : centralObserver ≡ 65663
centralObserverIs65663 = refl

normalizerObserverIs65663 : normalizerObserver ≡ 65663
normalizerObserverIs65663 = refl

ninetyPlusFiftyThreeIs143 : 90 + 53 ≡ 143
ninetyPlusFiftyThreeIs143 = Wilson.ninetyTransferIntoOneFortyThree

twelvePlusSeventyEightIs90 : 12 + 78 ≡ 90
twelvePlusSeventyEightIs90 = Exceptional90.twelvePlusSeventyEightIsNinety

------------------------------------------------------------------------
-- Actor classification.
------------------------------------------------------------------------

data ResidualActorClass : Set where
  centralC3Actor : ResidualActorClass
  conformalFixedLineActor : ResidualActorClass
  fullNormalizerActor : ResidualActorClass
  suzukiCoverActor : ResidualActorClass

data ActorPromotionStatus : Set where
  arithmeticObserverOnly : ActorPromotionStatus
  carrierAvailableActionUnpaid : ActorPromotionStatus
  publishedIrreducibilityBlocksNaiveSplit : ActorPromotionStatus

actorStatus : ResidualActorClass → ActorPromotionStatus
actorStatus centralC3Actor = carrierAvailableActionUnpaid
actorStatus conformalFixedLineActor = carrierAvailableActionUnpaid
actorStatus fullNormalizerActor = publishedIrreducibilityBlocksNaiveSplit
actorStatus suzukiCoverActor = publishedIrreducibilityBlocksNaiveSplit

------------------------------------------------------------------------
-- Primary/source attribution snowball.
------------------------------------------------------------------------

wilsonOddLocalSource : Attribution.AttributedSource
wilsonOddLocalSource = Attribution.mkDOISource
  "Robert A. Wilson"
  "The odd-local subgroups of the Monster"
  "Journal of the Australian Mathematical Society 44(1), 1-16"
  "1988"
  "10.1017/S1446788700031323"
  "https://doi.org/10.1017/S1446788700031323"
  Attribution.academicArticleSource
  "primary source for the Monster odd-local subgroup structure and the published 3B-normalizer restriction pattern used by the repo; does not license a 143=90+53 invariant-submodule split"
  Attribution.publicAttribution

barracloughWilsonCharacterTableSource : Attribution.AttributedSource
barracloughWilsonCharacterTableSource = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "primary/computational character-table provenance for N(3B), inertia groups, quotient map, and class fusions; character data do not by themselves construct a DASHI state-space intertwiner"
  Attribution.publicAttribution

wilsonAttribution =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt wilsonOddLocalSource
barracloughWilsonAttribution =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt barracloughWilsonCharacterTableSource

record Monster53ActorExternalCoordinates : Set where
  constructor monster53-actor-external-coordinates
  field
    wilsonOddLocalDOI : String
    normalizerCharacterTableDOI : String
    monsterQid : String
    suzukiSporadicQid : String
    centralC3Qid : String
    sameObjectOEIS : String
    wilsonSourceDewey : String
    characterTableSourceDewey : String
    qidsResolvedWithoutGuessing : Bool
    oeisPromotesActorStability : Bool
    deweyPromotesActorStability : Bool
open Monster53ActorExternalCoordinates public

canonicalMonster53ActorExternalCoordinates : Monster53ActorExternalCoordinates
canonicalMonster53ActorExternalCoordinates = monster53-actor-external-coordinates
  "10.1017/S1446788700031323"
  "10.1112/S1461157000001352"
  "unresolved exact Monster-group QID in this owner; retain existing repo QID if later located"
  "unresolved exact Suzuki-sporadic QID in this owner; do not confuse with Suzuki groups of Lie type"
  "unresolved exact C3 QID in this owner"
  "no same-object OEIS action sequence located; A005052 and exceptional-dimension sequences remain arithmetic/discovery coordinates only"
  "unresolved authoritative catalogue Dewey for Wilson 1988"
  "unresolved authoritative catalogue Dewey for Barraclough-Wilson 2007"
  false false false

------------------------------------------------------------------------
-- Existing theorem-bearing objects remain authoritative.
------------------------------------------------------------------------

centralResidualBoundary : C3Residual.RegularC3ResidualBoundary
centralResidualBoundary = C3Residual.canonicalRegularC3ResidualBoundary

wilsonBoundary : Wilson.WilsonRestrictionBoundary
wilsonBoundary = Wilson.canonicalWilsonRestrictionBoundary

multiplicityBoundary : Multiplicity.MultiplicityInertiaTwelveSeventyEightBoundary
multiplicityBoundary = Multiplicity.canonicalMultiplicityInertiaTwelveSeventyEightBoundary

carrier53Completion : Carrier53.CarrierDeletionCompletion
carrier53Completion = Carrier53.currentCarrierDeletionCompletion

------------------------------------------------------------------------
-- WrongType / impossible promotion boundaries.
------------------------------------------------------------------------

data Arithmetic143SplitCreatesSuzSubmodule : Set where
data CentralC3ResidualCreatesNormalizerResidual : Set where
data Carrier53CreatesFullNormalizerAction : Set where
data Exceptional53ArithmeticCreatesMonsterIntertwiner : Set where

arithmetic143DoesNotCreateSuzSplit : Arithmetic143SplitCreatesSuzSubmodule → ⊥
arithmetic143DoesNotCreateSuzSplit ()

centralResidualDoesNotCreateNormalizerResidual : CentralC3ResidualCreatesNormalizerResidual → ⊥
centralResidualDoesNotCreateNormalizerResidual ()

carrier53DoesNotCreateNormalizerAction : Carrier53CreatesFullNormalizerAction → ⊥
carrier53DoesNotCreateNormalizerAction ()

exceptional53DoesNotCreateMonsterIntertwiner : Exceptional53ArithmeticCreatesMonsterIntertwiner → ⊥
exceptional53DoesNotCreateMonsterIntertwiner ()

record ActorTyped53Frontier : Set where
  constructor actor-typed53-frontier
  field
    centralC3Residual53CharacterPaid : Bool
    finite53CarrierDeletionSquarePaid : Bool
    wilson65520Plus143RestrictionPaid : Bool
    published143IrreducibilityBoundaryRetained : Bool
    fullNormalizer53StableSubmodulePaid : Bool
    naive143As90Plus53PromotionRejected : Bool
    normalizerNative90As12Plus78SourceBacked : Bool
    actualFin90InertiaActionPaid : Bool
    exactActionIntertwinerPaid : Bool
    nextResidual : String
open ActorTyped53Frontier public

currentActorTyped53Frontier : ActorTyped53Frontier
currentActorTyped53Frontier = actor-typed53-frontier
  true true true true false true true false false
  "stop promoting the 53 lane at full N(3B)/Suz level. Rejoin the source-backed normalizer route at the actual zeta-sector recognition: construct W_zeta|E as H_zeta tensor Fin90, transport the actual inertia action to Fin90, and reconstruct its all-class multiplicity character. The published 12+78 pattern is the normalizer-native target. Revisit the 53 carrier only under a specifically named smaller actor or conformal-fixed-line restriction with a proved same-action inclusion."
