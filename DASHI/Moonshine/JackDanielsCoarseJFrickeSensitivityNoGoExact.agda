module DASHI.Moonshine.JackDanielsCoarseJFrickeSensitivityNoGoExact where

------------------------------------------------------------------------
-- JACK DANIEL'S: COARSE-j CANNOT REPLACE FINE FRICKE DATA
--
-- ATTRIBUTION / CLAIM BOUNDARY
--
-- `ModularCurveJFrickeInterfaceExact` already attributes the literal modular-
-- curve/Fricke ingredients to Katz--Mazur, Ogg, and Duncan--Ono.  The theorem
-- below is a DASHI type-theoretic consequence of that interface: a symmetric
-- observation of the source/target j-values is Fricke invariant, so a consumer
-- which distinguishes a point from its Fricke partner cannot descend through
-- that coarse observation.
--
-- This is NOT a claim that every Monster datum is Fricke-sensitive.  It says
-- exactly what must be proved before coarse j may be used for a particular
-- Monster consumer, and why jFine / level-structure residuals must be retained
-- by default in the Jack Daniel's recognition programme.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular
import DASHI.Biology.JCoarseFineConsumerReductionBridgeExact as Consumer
import DASHI.Moonshine.JInvariantRiemannObserverResidualSufficiencyBidiExact as Residual

------------------------------------------------------------------------
-- 1. A downstream consumer on literal fine modular points.
------------------------------------------------------------------------

record FrickeSensitiveConsumer
    (system : Modular.ModularJFrickeSystem) : Set₁ where
  constructor fricke-sensitive-consumer
  field
    ConsumerDatum : Set
    consume : Modular.FinePoint system -> ConsumerDatum
    witnessPoint : Modular.FinePoint system
    frickeChangesConsumer :
      consume (Modular.fricke system witnessPoint)
      ≡ consume witnessPoint -> ⊥

open FrickeSensitiveConsumer public

------------------------------------------------------------------------
-- 2. What it would mean for that consumer to factor through a symmetric
--    coarse-j observation.
------------------------------------------------------------------------

record SymmetricJConsumerFactorization
    {system : Modular.ModularJFrickeSystem}
    (observation : Modular.SymmetricJObservation system)
    (consumer : FrickeSensitiveConsumer system) : Set₁ where
  constructor symmetric-j-consumer-factorization
  field
    consumeObserved :
      Modular.Observation observation -> ConsumerDatum consumer

    factors :
      (point : Modular.FinePoint system) ->
      consumeObserved (Modular.observeUnoriented system observation point)
      ≡ consume consumer point

open SymmetricJConsumerFactorization public

------------------------------------------------------------------------
-- 3. Exact no-go.
------------------------------------------------------------------------

frickeSensitiveConsumerCannotFactorThroughSymmetricJ :
  ∀ {system : Modular.ModularJFrickeSystem}
    (observation : Modular.SymmetricJObservation system)
    (consumer : FrickeSensitiveConsumer system) ->
  SymmetricJConsumerFactorization observation consumer -> ⊥
frickeSensitiveConsumerCannotFactorThroughSymmetricJ
  {system} observation consumer factorization =
  frickeChangesConsumer consumer monsterSame
  where
    p = witnessPoint consumer

    observedSame :
      Modular.observeUnoriented system observation (Modular.fricke system p)
      ≡ Modular.observeUnoriented system observation p
    observedSame =
      Modular.observeUnorientedIsFrickeInvariant system observation p

    monsterSame :
      consume consumer (Modular.fricke system p)
      ≡ consume consumer p
    monsterSame =
      trans
        (sym (factors factorization (Modular.fricke system p)))
        (trans
          (cong (consumeObserved factorization) observedSame)
          (factors factorization p))

------------------------------------------------------------------------
-- 4. Existing finite observer evidence points in the same direction: the local
--    27 observer has an explicit collision and cannot recover arbitrary fine
--    consumers.  This is imported as a separate exact finite no-go, not as a
--    proof about literal modular curves.
------------------------------------------------------------------------

localJ27FailsAnExplicitFineConsumer :
  Residual.ConsumerSufficient
    Residual.localJObserver
    (Residual.fineFieldAt Residual.q11) -> ⊥
localJ27FailsAnExplicitFineConsumer =
  Residual.localJ27CannotSufficeForQ11Consumer

jCoarseFineConsumerBoundary : Consumer.JCoarseFineConsumerReductionBoundary
jCoarseFineConsumerBoundary = Consumer.canonicalJCoarseFineConsumerReductionBoundary

------------------------------------------------------------------------
-- 5. Machine-readable consequence for Jack Daniel's.
------------------------------------------------------------------------

record CoarseJFrickeSensitivityBoundary : Set where
  constructor coarse-j-fricke-sensitivity-boundary
  field
    symmetricJIsFrickeInvariant : Bool
    frickeSensitiveConsumerNoGoPaid : Bool
    explicitFiniteFineResidualCollisionAlreadyPaid : Bool
    fineResidualRetainedByDefault : Bool
    coarseJAloneLicensedForEveryMonsterConsumer : Bool

canonicalCoarseJFrickeSensitivityBoundary : CoarseJFrickeSensitivityBoundary
canonicalCoarseJFrickeSensitivityBoundary =
  coarse-j-fricke-sensitivity-boundary
    true true true true false
