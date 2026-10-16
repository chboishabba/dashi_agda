module DASHI.Moonshine.MonsterAlbertF4ProofRelevantRecognitionExact where

------------------------------------------------------------------------
-- PROOF-RELEVANT MONSTER <-> ALBERT/F4 SAME-ACTION TARGET
--
-- The carrier/deletion weld and conditional transport compiler are already
-- paid by MonsterAlbertFiftyThreeProofRelevantWeldExact.  This owner removes
-- the last proposition-valued placeholder from the exceptional action target:
-- every substantive action claim below is an inhabited equality family.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Sum.Base using (inj₁)

import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Moonshine.Base369MonsterFiftyFourFiveModeResidualActionBidiExact as Base
import DASHI.Moonshine.MonsterAlbertFiftyThreeProofRelevantWeldExact as Weld
import DASHI.Wikimedia.IbrahimZeta54AlbertPair53SnowballAttributionBidiExact as Albert

record ProofRelevantMonsterAlbertF4Recognition : Set₁ where
  constructor proof-relevant-monster-albert-f4-recognition
  field
    transportedMonsterAction : Weld.TransportedMonsterAlbertAction

    AlbertJordanProduct :
      Albert.CubeAlbertPair54 →
      Albert.CubeAlbertPair54 →
      Albert.CubeAlbertPair54

    F4Actor : Set
    f4Act54 : F4Actor → Albert.CubeAlbertPair54 → Albert.CubeAlbertPair54
    f4Act53 : F4Actor → Albert.CubeReducedAlbert53 → Albert.CubeReducedAlbert53

    classicalF4ActionPreservesJordanProduct :
      (actor : F4Actor) →
      (x y : Albert.CubeAlbertPair54) →
      f4Act54 actor (AlbertJordanProduct x y)
      ≡ AlbertJordanProduct (f4Act54 actor x) (f4Act54 actor y)

    monsterActorToF4Actor :
      Base.Actor (Weld.recognition transportedMonsterAction) → F4Actor

    same54ActionIntertwiner :
      (actor : Base.Actor (Weld.recognition transportedMonsterAction)) →
      (state : Albert.CubeAlbertPair54) →
      Weld.actAlbert54 transportedMonsterAction actor state
      ≡ f4Act54 (monsterActorToF4Actor actor) state

    same53ActionIntertwiner :
      (actor : Base.Actor (Weld.recognition transportedMonsterAction)) →
      (state : Albert.CubeReducedAlbert53) →
      Weld.actAlbert53 transportedMonsterAction actor state
      ≡ f4Act53 (monsterActorToF4Actor actor) state

    f4FixesRemovedAlbertScalar :
      (actor : F4Actor) →
      f4Act54 actor (inj₁ (inj₁ Exceptional.scalarLine))
      ≡ inj₁ (inj₁ Exceptional.scalarLine)

    f4ResidualRestrictionIsSameAction :
      (actor : F4Actor) →
      (state : Albert.CubeReducedAlbert53) →
      Albert.includeReducedAlbert53 (f4Act53 actor state)
      ≡ f4Act54 actor (Albert.includeReducedAlbert53 state)

open ProofRelevantMonsterAlbertF4Recognition public

record ProofRelevantMonsterAlbertF4Boundary : Set where
  constructor proof-relevant-monster-albert-f4-boundary
  field
    carrierAndDeletionAlreadyPaid : Bool
    actualMonsterActionTransportCompilerAlreadyPaid : Bool
    jordanPreservationRequiresProof : Bool
    full54IntertwinerRequiresProof : Bool
    residual53IntertwinerRequiresProof : Bool
    removedScalarFixedRequiresProof : Bool
    residualRestrictionRequiresProof : Bool
    recognitionInhabitedHere : Bool

canonicalProofRelevantMonsterAlbertF4Boundary :
  ProofRelevantMonsterAlbertF4Boundary
canonicalProofRelevantMonsterAlbertF4Boundary =
  proof-relevant-monster-albert-f4-boundary
    true true true true true true true false
