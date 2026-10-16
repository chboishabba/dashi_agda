module DASHI.Moonshine.MonsterAlbertFiftyThreeProofRelevantWeldExact where

------------------------------------------------------------------------
-- PROOF-RELEVANT MONSTER/BASE369 <-> ALBERT 54 -> 53 WELD
--
-- Current master already pays the whole finite carrier/deletion geometry:
--
--   Base.SecondaryCell54 <-> Zeta54Site <-> AlbertPair54
--   Base.ResidualCell53  <-> ZetaResidual53 <-> ReducedAlbertPair53
--
-- with exact round trips, the removed distinguished point, and commuting
-- residual inclusions.  An older generic interface stored two promotion
-- obligations merely as values of type Set.  This owner does not count those
-- proposition-types as proofs.  It re-exposes the concrete equalities as
-- proof-bearing fields and shows that, once an actual Monster 54/53 action
-- recognition is supplied, its actions can be transported onto the already
-- identified Albert-shaped finite carriers without another cardinality step.
--
-- This still does NOT identify the transported action with the classical F4
-- automorphism action or manufacture an Albert/Jordan product.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum.Base using (inj₁)
open import Data.Empty using (⊥)

import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Moonshine.Base369MonsterFiftyFourFiveModeResidualActionBidiExact as Base
import DASHI.Wikimedia.IbrahimZeta54AlbertPair53SnowballAttributionBidiExact as Albert
import DASHI.Wikimedia.IbrahimZetaBase53ExceptionalSkeletonCompletionExact as Completion
import DASHI.Wikimedia.IbrahimZetaSixByNineFiveMode54CarrierSnowballExact as Chart

------------------------------------------------------------------------
-- 1. Proof-bearing finite carrier/deletion certificate.
------------------------------------------------------------------------

record ProofRelevantBaseZetaAlbertDeletionWeld : Set where
  constructor proof-relevant-base-zeta-albert-deletion-weld
  field
    base54ToAlbert54 : Base.SecondaryCell54 → Albert.CubeAlbertPair54
    albert54ToBase54 : Albert.CubeAlbertPair54 → Base.SecondaryCell54
    base54RoundTrip :
      (s : Base.SecondaryCell54) → albert54ToBase54 (base54ToAlbert54 s) ≡ s
    albert54RoundTrip :
      (a : Albert.CubeAlbertPair54) → base54ToAlbert54 (albert54ToBase54 a) ≡ a

    base53ToAlbert53 : Base.ResidualCell53 → Albert.CubeReducedAlbert53
    albert53ToBase53 : Albert.CubeReducedAlbert53 → Base.ResidualCell53
    base53RoundTrip :
      (s : Base.ResidualCell53) → albert53ToBase53 (base53ToAlbert53 s) ≡ s
    albert53RoundTrip :
      (a : Albert.CubeReducedAlbert53) → base53ToAlbert53 (albert53ToBase53 a) ≡ a

    removedInvariantReallyMapsToAlbertScalar :
      base54ToAlbert54 Base.distinguishedInvariant54
      ≡ inj₁ (inj₁ Exceptional.scalarLine)

    baseResidualReallyCommutesWithZetaInclusion :
      (s : Base.ResidualCell53) →
      Chart.zeta54ToBase54
        (Albert.includeZetaResidual53 (Completion.base53ToZeta53 s))
      ≡ Base.includeResidual53 s

    zetaResidualReallyCommutesWithAlbertInclusion :
      (s : Albert.ZetaResidual53) →
      Albert.zeta54ToAlbertPair54 (Albert.includeZetaResidual53 s)
      ≡ Albert.includeReducedAlbert53 (Albert.zetaResidual53ToAlbert53 s)

open ProofRelevantBaseZetaAlbertDeletionWeld public

canonicalProofRelevantBaseZetaAlbertDeletionWeld :
  ProofRelevantBaseZetaAlbertDeletionWeld
canonicalProofRelevantBaseZetaAlbertDeletionWeld =
  proof-relevant-base-zeta-albert-deletion-weld
    Completion.base54ToAlbert54
    Completion.albert54ToBase54
    Completion.base54Albert54RoundTrip
    Completion.albert54Base54RoundTrip
    Completion.base53ToAlbert53
    Completion.albert53ToBase53
    Completion.base53Albert53RoundTrip
    Completion.albert53Base53RoundTrip
    Completion.baseRemovedInvariantMapsToAlbertRemovedScalar
    Completion.baseResidualInclusionCommutes
    Albert.residualInclusionCommutes

------------------------------------------------------------------------
-- 2. Transport an ACTUAL Monster-side 54/53 recognition onto the Albert-shaped
--    finite carriers.  This compiler requires the actual action recognition;
--    it does not infer one from the carrier chart.
------------------------------------------------------------------------

record TransportedMonsterAlbertAction : Set₁ where
  constructor transported-monster-albert-action
  field
    recognition : Base.ActualFiftyFourFiveModeResidualActionRecognition

    actAlbert54 :
      Base.Actor recognition → Albert.CubeAlbertPair54 → Albert.CubeAlbertPair54
    actAlbert53 :
      Base.Actor recognition → Albert.CubeReducedAlbert53 → Albert.CubeReducedAlbert53

    actual54ToAlbert54 :
      Base.Actual54 recognition → Albert.CubeAlbertPair54
    albert54ToActual54 :
      Albert.CubeAlbertPair54 → Base.Actual54 recognition

    actual53ToAlbert53 :
      Base.Actual53 recognition → Albert.CubeReducedAlbert53
    albert53ToActual53 :
      Albert.CubeReducedAlbert53 → Base.Actual53 recognition

open TransportedMonsterAlbertAction public

transportActual54ToAlbert54 :
  (r : Base.ActualFiftyFourFiveModeResidualActionRecognition) →
  Base.Actual54 r → Albert.CubeAlbertPair54
transportActual54ToAlbert54 r x =
  Completion.base54ToAlbert54 (Base.toSkeleton54 r x)

transportAlbert54ToActual54 :
  (r : Base.ActualFiftyFourFiveModeResidualActionRecognition) →
  Albert.CubeAlbertPair54 → Base.Actual54 r
transportAlbert54ToActual54 r a =
  Base.fromSkeleton54 r (Completion.albert54ToBase54 a)

transportActual53ToAlbert53 :
  (r : Base.ActualFiftyFourFiveModeResidualActionRecognition) →
  Base.Actual53 r → Albert.CubeReducedAlbert53
transportActual53ToAlbert53 r x =
  Completion.base53ToAlbert53 (Base.toResidual53 r x)

transportAlbert53ToActual53 :
  (r : Base.ActualFiftyFourFiveModeResidualActionRecognition) →
  Albert.CubeReducedAlbert53 → Base.Actual53 r
transportAlbert53ToActual53 r a =
  Base.fromResidual53 r (Completion.albert53ToBase53 a)

transportAlbert54Action :
  (r : Base.ActualFiftyFourFiveModeResidualActionRecognition) →
  Base.Actor r → Albert.CubeAlbertPair54 → Albert.CubeAlbertPair54
transportAlbert54Action r actor a =
  transportActual54ToAlbert54 r
    (Base.act54 r actor (transportAlbert54ToActual54 r a))

transportAlbert53Action :
  (r : Base.ActualFiftyFourFiveModeResidualActionRecognition) →
  Base.Actor r → Albert.CubeReducedAlbert53 → Albert.CubeReducedAlbert53
transportAlbert53Action r actor a =
  transportActual53ToAlbert53 r
    (Base.act53 r actor (transportAlbert53ToActual53 r a))

compileTransportedMonsterAlbertAction :
  (r : Base.ActualFiftyFourFiveModeResidualActionRecognition) →
  TransportedMonsterAlbertAction
compileTransportedMonsterAlbertAction r =
  transported-monster-albert-action
    r
    (transportAlbert54Action r)
    (transportAlbert53Action r)
    (transportActual54ToAlbert54 r)
    (transportAlbert54ToActual54 r)
    (transportActual53ToAlbert53 r)
    (transportAlbert53ToActual53 r)

------------------------------------------------------------------------
-- 3. What remains for an exceptional SAME-ACTION theorem is now explicit.
------------------------------------------------------------------------

record MonsterAlbertF4SameActionRecognition : Set₁ where
  constructor monster-albert-f4-same-action-recognition
  field
    transportedMonsterAction : TransportedMonsterAlbertAction

    AlbertJordanProduct : Set
    F4Actor : Set
    f4Act54 : F4Actor → Albert.CubeAlbertPair54 → Albert.CubeAlbertPair54
    f4Act53 : F4Actor → Albert.CubeReducedAlbert53 → Albert.CubeReducedAlbert53

    jordanProductIsSameAlbertCarrier : Set
    classicalF4ActionPreservesJordanProduct : Set
    monsterActorToF4Actor :
      Base.Actor (recognition transportedMonsterAction) → F4Actor
    same54ActionIntertwiner : Set
    same53ActionIntertwiner : Set
    sameRemovedInvariant : Set
    sameResidualRestriction : Set

------------------------------------------------------------------------
-- 4. Non-promotion boundaries.
------------------------------------------------------------------------

data TransportedActionIsClassicalF4Action : Set where
data AlbertCarrierChartCreatesJordanProduct : Set where

transportDoesNotManufactureF4 : TransportedActionIsClassicalF4Action → ⊥
transportDoesNotManufactureF4 ()

carrierChartDoesNotManufactureJordanProduct : AlbertCarrierChartCreatesJordanProduct → ⊥
carrierChartDoesNotManufactureJordanProduct ()

record MonsterAlbertFiftyThreeBoundary : Set where
  constructor monster-albert-fifty-three-boundary
  field
    full54CarrierBijectionProofRelevant : Bool
    residual53CarrierBijectionProofRelevant : Bool
    removedPointEqualityProofRelevant : Bool
    bothInclusionSquaresProofRelevant : Bool
    actualMonsterActionTransportCompilerPaid : Bool
    classicalF4SameActionPaid : Bool
    jordanProductSameObjectPaid : Bool

canonicalMonsterAlbertFiftyThreeBoundary : MonsterAlbertFiftyThreeBoundary
canonicalMonsterAlbertFiftyThreeBoundary =
  monster-albert-fifty-three-boundary
    true true true true true false false
