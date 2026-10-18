module DASHI.Physics.CondensedMatter.YbSbTwoMajoranaMaxCutBoundaryExact where

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- MATHEMATICAL CLOSURES NOW PRESENT IN-REPO:
--   * exact B4 Majorana braid action with inverses;
--   * both adjacent Yang-Baxter relations;
--   * far commutativity;
--   * explicit adjacent noncommutativity;
--   * four-Majorana even-parity logical qubit;
--   * finite two-Majorana Fock/Clifford action;
--   * number-projector idempotence;
--   * Ising/Majorana braiding-alone universality boundary.
--
-- PHYSICAL / SOURCE IDENTIFICATION REMAINS OPEN:
--   * YbSb2 surface branch -> isolated manipulable Majorana zero modes;
--   * physical exchange in YbSb2 -> the exact B4 action formalised here;
--   * parity-protected encoded readout in YbSb2;
--   * an independent universality-completion resource;
--   * experimentally demonstrated device-level computation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Physics.CondensedMatter.MajoranaB4BraidExact as B4
import DASHI.Physics.CondensedMatter.MajoranaParityQubitExact as Qubit
import DASHI.Physics.CondensedMatter.MajoranaFockActionExact as Fock
import DASHI.Physics.CondensedMatter.IsingMajoranaUniversalityBoundaryExact as Ising

record MajoranaMathematicsClosed : Set₁ where
  field
    yb12 :
      (x : B4.SignedMajorana4) →
      B4.sigma1 (B4.sigma2 (B4.sigma1 x))
      ≡
      B4.sigma2 (B4.sigma1 (B4.sigma2 x))

    yb23 :
      (x : B4.SignedMajorana4) →
      B4.sigma2 (B4.sigma3 (B4.sigma2 x))
      ≡
      B4.sigma3 (B4.sigma2 (B4.sigma3 x))

    far13 :
      (x : B4.SignedMajorana4) →
      B4.sigma1 (B4.sigma3 x)
      ≡
      B4.sigma3 (B4.sigma1 x)

    adjacentNoncommuting :
      ((x : B4.SignedMajorana4) →
        B4.sigma1 (B4.sigma2 x)
        ≡
        B4.sigma2 (B4.sigma1 x))
      →
      ⊥

    logicalCarrier : Set
    encodeLogical :
      logicalCarrier →
      Qubit.EvenParityState
    decodeLogical :
      Qubit.EvenParityState →
      logicalCarrier

    gamma12Anticommute :
      (x : Fock.BasisState) →
      Fock.gamma1 (Fock.gamma2 x)
      ≡
      Fock.negateState (Fock.gamma2 (Fock.gamma1 x))

    numberIdempotent :
      (v : Fock.FockVector) →
      Fock.liftNumber (Fock.liftNumber v)
      ≡
      Fock.liftNumber v

canonicalMajoranaMathematicsClosed :
  MajoranaMathematicsClosed
canonicalMajoranaMathematicsClosed =
  record
    { yb12 = B4.yangBaxter12
    ; yb23 = B4.yangBaxter23
    ; far13 = B4.farCommutation13
    ; adjacentNoncommuting = B4.adjacent12Noncommuting
    ; logicalCarrier = Qubit.LogicalQubit
    ; encodeLogical = Qubit.encodeLogical
    ; decodeLogical = Qubit.decodeLogical
    ; gamma12Anticommute = Fock.gamma12Anticommute
    ; numberIdempotent = Fock.numberIdempotent
    }

isingBraidingAloneStillNotUniversal :
  Ising.BraidingAloneUniversal
    Ising.canonicalIsingMajoranaUniversalitySourceClaim
  →
  ⊥
isingBraidingAloneStillNotUniversal =
  Ising.notUniversalByBraidingAlone
    Ising.canonicalIsingMajoranaUniversalitySourceClaim

record YbSbTwoMajoranaPhysicalResiduals : Set₁ where
  field
    IsolatedManipulableMajoranas : Set
    PhysicalExchangeRealizesExactB4 : Set
    ParityProtectedReadout : Set
    UniversalityCompletionResource : Set
    ExperimentalDeviceComputation : Set

-- Deliberately no canonical inhabitant.
