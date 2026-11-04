{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOSRealEuclideanTimeSeparationExact where

------------------------------------------------------------------------
-- P03/P07: FAIL-CLOSED REAL-TIME UNITARY VS EUCLIDEAN OS TRANSFER.
--
-- The ORIGINAL source-owned TSVFOSSameSelectedClockIterateExact has a
-- oneStepIntertwines field which commutes observerStep and osStep under
-- a two-sided state carrier embedding. That is valid as finite ALGEBRA,
-- but osStep must NOT automatically be interpreted as a positive-time
-- Euclidean OS transfer exp(-tau H) if observerStep is a real-time
-- norm-preserving unitary exp(-i t H / hbar) and the OS state contains
-- a genuinely strictly decaying positive-energy excitation.
--
-- Source-weld below: it consumes exactly the existing
-- OriginalTSVFToOSClock.oneStepIntertwines, *without* making a parallel
-- clock, and proves that its isometric physical specialization is
-- incompatible with a strictly contracting Euclidean transfer on the
-- same selected non-vacuum state.
--
-- The correct P07 physical bridge compares the same self-adjoint H,
-- with a real-time unitary U(t)=exp(-i t H/hbar) and the Euclidean
-- contraction T(tau)=exp(-tau H/hbar) at physical SI time tau, related
-- by the justified Wick/OS spectral analytic continuation. One-step
-- equality does not prove shared generator, analytic continuation,
-- self-adjointness or domain equality.
--
-- The finite witness below is a discrete *qualitative* negative control
-- and NOT exp(-tau H) at finite tau. The general no-go applies to any
-- actual strictly norm-decreasing selected Euclidean OS step.
--
-- Original sources: Osterwalder--Schrader; Stone; original DASHI
-- OS/R331 and TSVF/observer-clock theorem owners.
-- No local postulates, holes, terminating overrides or fake PHYSICAL.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans; subst)

import DASHI.Quantum.TSVF as TSVF
import DASHI.Physics.Foundations.TSVFOSSameSelectedClockIterateExact as Clock
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS

-- From the *original clock's* one-step equation, isometry of the
-- observer-to-OS identification, and norm preservation by observer
-- evolution, derive the exact opposite of strict OS contraction.
originalClockDirectEuclideanNormMustBeEqual :
  ∀ {F Q E Observable Point Scalar system reconstruction Energy}
  (clock : Clock.OriginalTSVFToOSClock {F} {Q} E
    {Observable} {Point} {Scalar} {system} reconstruction Energy) →
  (Norm : Set)
  (observerNorm : TSVF.QuantumSurface.Ket Q → Norm)
  (osNorm : Clock.OSState clock → Norm)
  (identificationPreservesNorm :
    ∀ x →
    osNorm (Clock.embedObserver clock x) ≡ observerNorm x)
  (selectedExcitation : TSVF.QuantumSurface.Ket Q)
  (observerRealTimeIsometric :
    observerNorm (Clock.observerStep clock selectedExcitation)
    ≡ observerNorm selectedExcitation) →
  osNorm (Clock.osStep clock
    (Clock.embedObserver clock selectedExcitation))
  ≡ osNorm (Clock.embedObserver clock selectedExcitation)
originalClockDirectEuclideanNormMustBeEqual clock Norm
    observerNorm osNorm normMap excited unitary =
  trans
    (sym
      (cong osNorm (Clock.oneStepIntertwines clock excited)))
    (trans
      (normMap (Clock.observerStep clock excited))
      (trans unitary (sym (normMap excited))))

-- The no-go is mathematically independent of a particular scalar norm
-- backend: the missing PHYSICAL source must supply a *real* strictly
-- ordered norm and the strict contraction on a selected excitation.
-- Such evidence is incompatible with direct stepwise unitary matching.
originalClockCannotIdentifyStrictEuclideanDecay :
  ∀ {F Q E Observable Point Scalar system reconstruction Energy}
  (clock : Clock.OriginalTSVFToOSClock {F} {Q} E
    {Observable} {Point} {Scalar} {system} reconstruction Energy) →
  (Norm : Set)
  (observerNorm : TSVF.QuantumSurface.Ket Q → Norm)
  (osNorm : Clock.OSState clock → Norm)
  (StrictlyLess : Norm → Norm → Set)
  (strictIrreflexive :
    ∀ value → StrictlyLess value value → ⊥)
  (identificationPreservesNorm :
    ∀ x →
    osNorm (Clock.embedObserver clock x) ≡ observerNorm x)
  (selectedExcitation : TSVF.QuantumSurface.Ket Q)
  (observerRealTimeIsometric :
    observerNorm (Clock.observerStep clock selectedExcitation)
    ≡ observerNorm selectedExcitation)
  (euclideanTransferStrictlyContracts :
    StrictlyLess
      (osNorm (Clock.osStep clock
        (Clock.embedObserver clock selectedExcitation)))
      (osNorm (Clock.embedObserver clock selectedExcitation))) →
  ⊥
originalClockCannotIdentifyStrictEuclideanDecay clock Norm
    observerNorm osNorm StrictlyLess irreflexive normMap
    excited unitary strict =
  let
    sameNorm :
      osNorm (Clock.osStep clock (Clock.embedObserver clock excited))
      ≡ osNorm (Clock.embedObserver clock excited)
    sameNorm =
      originalClockDirectEuclideanNormMustBeEqual
        clock Norm observerNorm osNorm normMap excited unitary

    contradiction :
      StrictlyLess
        (osNorm (Clock.embedObserver clock excited))
        (osNorm (Clock.embedObserver clock excited))
    contradiction =
      subst
        (λ value →
          StrictlyLess value
            (osNorm (Clock.embedObserver clock excited)))
        sameNorm strict
  in
  irreflexive _ contradiction

------------------------------------------------------------------------
-- Independent concrete finite nonpromotion example.
--
-- Three sector labels are a *discrete* witness of the logical gap,
-- NOT an actual Euclidean exp(-tau H) at a finite physical time:
-- a norm-preserving excitation permutation and a norm-reducing map
-- cannot be identified on a non-vacuum state.
------------------------------------------------------------------------

data FiniteEnergySector : Set where
  vacuum excitedPositive excitedNegative : FiniteEnergySector

sectorNormSquared : FiniteEnergySector → Nat
sectorNormSquared vacuum = zero
sectorNormSquared excitedPositive = suc zero
sectorNormSquared excitedNegative = suc zero

finiteRealUnitaryPermutation : FiniteEnergySector → FiniteEnergySector
finiteRealUnitaryPermutation vacuum = vacuum
finiteRealUnitaryPermutation excitedPositive = excitedNegative
finiteRealUnitaryPermutation excitedNegative = excitedPositive

finiteEuclideanRankDrop : FiniteEnergySector → FiniteEnergySector
finiteEuclideanRankDrop vacuum = vacuum
finiteEuclideanRankDrop excitedPositive = vacuum
finiteEuclideanRankDrop excitedNegative = vacuum

finiteObserverNormPreserved :
  ∀ state →
  sectorNormSquared (finiteRealUnitaryPermutation state)
    ≡ sectorNormSquared state
finiteObserverNormPreserved vacuum = refl
finiteObserverNormPreserved excitedPositive = refl
finiteObserverNormPreserved excitedNegative = refl

finiteEuclideanExcitationNormDrops :
  sectorNormSquared (finiteEuclideanRankDrop excitedPositive)
  ≡ zero
finiteEuclideanExcitationNormDrops = refl

finiteDirectStepwiseIdentificationImpossible :
  ((state : FiniteEnergySector) →
    finiteRealUnitaryPermutation state
    ≡ finiteEuclideanRankDrop state) →
  ⊥
finiteDirectStepwiseIdentificationImpossible same
  with same excitedPositive
... | ()
