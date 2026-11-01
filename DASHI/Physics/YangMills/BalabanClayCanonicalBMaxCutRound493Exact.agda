{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBMaxCutRound493Exact where

------------------------------------------------------------------------
-- ROUND493 / SOURCE-CORRECT CANONICAL B MAX-CUT
--
-- R491/R492 correct the preferred Wilson route:
--
--   B-WEXT:
--     |Cov(W_L,W_R)| <= rootedShell(d(W_L,W_R))
--
--   B-H:
--     the q = 1/2 decay coordinate is attached to the SAME reconstructed
--     Hamiltonian/transfer-energy coordinate consumed by the spectral theorem.
--
-- Historical B proof search repeatedly compressed the live frontier to a
-- source-facing MIN-CUT.  That was useful for least-privilege interfaces, but
-- it is the wrong scheduling policy here: after the printed-J correction the
-- two surviving physical coordinates are independent and should remain visible
-- in parallel.
--
-- This owner therefore formalises the preferred proof-search policy as a
-- CONSUMER-EXPOSURE MAX-CUT:
--
--   * retain every independent live physical payment on the current B cut;
--   * expose the union of its declared downstream consumers;
--   * do not assign a parent's whole fanout to one prerequisite;
--   * do not let fanout manufacture theorem closure;
--   * keep historical selected-J min-cut machinery as provenance only.
--
-- "Max-cut" here is proof-search terminology: maximize the live theorem-bearing
-- consumer surface exposed by the cut.  It is not a claim that an arbitrary
-- weighted graph MaxCut optimization problem has been solved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayCanonicalBSourceCorrectRound492Exact as R492

------------------------------------------------------------------------
-- Live source-correct physical leaves.
------------------------------------------------------------------------

data BMaxCutLeaf : Set where
  bWEXT : BMaxCutLeaf
  bSameHamiltonian : BMaxCutLeaf

data BMaxCutConsumer : Set where
  rootedShellBoundConsumer : BMaxCutConsumer
  geometricHalfRateDecayConsumer : BMaxCutConsumer
  spectralHalfRatePremiseConsumer : BMaxCutConsumer
  reconstructedHamiltonianConsumer : BMaxCutConsumer
  physicalMassGapCertificateConsumer : BMaxCutConsumer

leafConsumers : BMaxCutLeaf → List BMaxCutConsumer
leafConsumers bWEXT =
  rootedShellBoundConsumer
  ∷ geometricHalfRateDecayConsumer
  ∷ spectralHalfRatePremiseConsumer
  ∷ []
leafConsumers bSameHamiltonian =
  reconstructedHamiltonianConsumer
  ∷ physicalMassGapCertificateConsumer
  ∷ []

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

leafFanout : BMaxCutLeaf → Nat
leafFanout leaf = listLength (leafConsumers leaf)

maxCutLeaves : List BMaxCutLeaf
maxCutLeaves = bWEXT ∷ bSameHamiltonian ∷ []

maxCutWidth : Nat
maxCutWidth = listLength maxCutLeaves

-- The declared consumer sets are intentionally disjoint in this owner, so the
-- joint exposure is their additive fanout.  This is scheduling metadata only.
maxCutConsumerExposure : Nat
maxCutConsumerExposure =
  leafFanout bWEXT + leafFanout bSameHamiltonian
  where
  _+_ : Nat → Nat → Nat
  zero + n = n
  suc m + n = suc (m + n)

bWEXTFanoutIsThree :
  leafFanout bWEXT ≡ suc (suc (suc zero))
bWEXTFanoutIsThree = refl

bSameHamiltonianFanoutIsTwo :
  leafFanout bSameHamiltonian ≡ suc (suc zero)
bSameHamiltonianFanoutIsTwo = refl

maxCutWidthIsTwo :
  maxCutWidth ≡ suc (suc zero)
maxCutWidthIsTwo = refl

maxCutConsumerExposureIsFive :
  maxCutConsumerExposure ≡
    suc (suc (suc (suc (suc zero))))
maxCutConsumerExposureIsFive = refl

------------------------------------------------------------------------
-- Proof-level projection from the source-correct R492 board.
------------------------------------------------------------------------

bWEXTLevel : ProofLevel
bWEXTLevel = R492.bWilsonTwoInsertionConnectedShellLevel

bSameHamiltonianLevel : ProofLevel
bSameHamiltonianLevel = R492.bSameHamiltonianTransferCoordinateLevel

bGeometricDecayCompilerLevel : ProofLevel
bGeometricDecayCompilerLevel =
  R492.bConnectedShellToGeometricDecayCompilerLevel

bStandardSpectralTransferLevel : ProofLevel
bStandardSpectralTransferLevel =
  R492.bStandardClusteringToMassGapTransferLevel

------------------------------------------------------------------------
-- Max-cut scheduling boundary.
------------------------------------------------------------------------

preferredBSearchPolicyIsConsumerExposureMaxCut : Bool
preferredBSearchPolicyIsConsumerExposureMaxCut = true

historicalSelectedJMinCutMandatory : Bool
historicalSelectedJMinCutMandatory = false

shortestSerialCutPreferredOverParallelPhysicalCut : Bool
shortestSerialCutPreferredOverParallelPhysicalCut = false

maxCutPreservesIndependentWEXTAndHamiltonianPayments : Bool
maxCutPreservesIndependentWEXTAndHamiltonianPayments = true

maxCutAutomaticallyProvesEitherPhysicalLeaf : Bool
maxCutAutomaticallyProvesEitherPhysicalLeaf = false

maxCutMayPromotePrintedJObservableIdentification : Bool
maxCutMayPromotePrintedJObservableIdentification = false

maxCutMayDropSameHamiltonianAttachment : Bool
maxCutMayDropSameHamiltonianAttachment = false

maxCutMayDropWilsonExtensionPayment : Bool
maxCutMayDropWilsonExtensionPayment = false

maxCutAddsNewYangMillsTheorem : Bool
maxCutAddsNewYangMillsTheorem = false

round493MaxCutSchedulerLevel : ProofLevel
round493MaxCutSchedulerLevel = machineChecked

preferredBSearchPolicyIsConsumerExposureMaxCutIsTrue :
  preferredBSearchPolicyIsConsumerExposureMaxCut ≡ true
preferredBSearchPolicyIsConsumerExposureMaxCutIsTrue = refl

historicalSelectedJMinCutMandatoryIsFalse :
  historicalSelectedJMinCutMandatory ≡ false
historicalSelectedJMinCutMandatoryIsFalse = refl

shortestSerialCutPreferredOverParallelPhysicalCutIsFalse :
  shortestSerialCutPreferredOverParallelPhysicalCut ≡ false
shortestSerialCutPreferredOverParallelPhysicalCutIsFalse = refl

maxCutPreservesIndependentWEXTAndHamiltonianPaymentsIsTrue :
  maxCutPreservesIndependentWEXTAndHamiltonianPayments ≡ true
maxCutPreservesIndependentWEXTAndHamiltonianPaymentsIsTrue = refl

maxCutAutomaticallyProvesEitherPhysicalLeafIsFalse :
  maxCutAutomaticallyProvesEitherPhysicalLeaf ≡ false
maxCutAutomaticallyProvesEitherPhysicalLeafIsFalse = refl

maxCutMayPromotePrintedJObservableIdentificationIsFalse :
  maxCutMayPromotePrintedJObservableIdentification ≡ false
maxCutMayPromotePrintedJObservableIdentificationIsFalse = refl

maxCutMayDropSameHamiltonianAttachmentIsFalse :
  maxCutMayDropSameHamiltonianAttachment ≡ false
maxCutMayDropSameHamiltonianAttachmentIsFalse = refl

maxCutMayDropWilsonExtensionPaymentIsFalse :
  maxCutMayDropWilsonExtensionPayment ≡ false
maxCutMayDropWilsonExtensionPaymentIsFalse = refl

maxCutAddsNewYangMillsTheoremIsFalse :
  maxCutAddsNewYangMillsTheorem ≡ false
maxCutAddsNewYangMillsTheoremIsFalse = refl
