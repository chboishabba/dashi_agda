module DASHI.Physics.StandardModel.FiniteInternalAlgebraPruning where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Physics.StandardModel.FiniteRealStarAlgebraCandidates

------------------------------------------------------------------------
-- C1-C5 pruning surface.
--
-- This module distinguishes three statuses:
--   survives  : structurally compatible with the named gate;
--   rejected  : ruled out by the named gate;
--   held      : requires a theorem not supplied here.
--
-- In particular, the Standard-Model spine is a survivor/candidate, not yet a
-- uniquely derived algebra.
------------------------------------------------------------------------

data InternalGate : Set where
  reality
  grading
  firstOrder
  commutant
  anomalyFreedom
  minimality
  : InternalGate

data GateVerdict : Set where
  survives rejected held : GateVerdict

record GateReceipt : Set where
  constructor gateReceipt
  field
    candidate : FiniteRealStarAlgebra
    gate : InternalGate
    verdict : GateVerdict
    reason : String

open GateReceipt public

------------------------------------------------------------------------
-- Explicit factor-presence probes for the finite candidate list.
------------------------------------------------------------------------

hasComplexOne : FiniteRealStarAlgebra → Bool
hasComplexOne [] = false
hasComplexOne (matrixFactor complex 1 ∷ _) = true
hasComplexOne (_ ∷ fs) = hasComplexOne fs

hasQuaternionOne : FiniteRealStarAlgebra → Bool
hasQuaternionOne [] = false
hasQuaternionOne (matrixFactor quaternion 1 ∷ _) = true
hasQuaternionOne (_ ∷ fs) = hasQuaternionOne fs

hasComplexThree : FiniteRealStarAlgebra → Bool
hasComplexThree [] = false
hasComplexThree (matrixFactor complex 3 ∷ _) = true
hasComplexThree (_ ∷ fs) = hasComplexThree fs

record StandardModelFactorProfile (A : FiniteRealStarAlgebra) : Set where
  field
    hyperchargeFactor : hasComplexOne A ≡ true
    weakFactor : hasQuaternionOne A ≡ true
    colourFactor : hasComplexThree A ≡ true

open StandardModelFactorProfile public

standardModelFactorProfile : StandardModelFactorProfile standardModelSpine
standardModelFactorProfile =
  record
    { hyperchargeFactor = refl
    ; weakFactor = refl
    ; colourFactor = refl
    }

------------------------------------------------------------------------
-- Coarse pruning receipts.
-- These are not substitutes for a real spectral-triple representation proof.
------------------------------------------------------------------------

realOnlyRejectedForHypercharge : GateReceipt
realOnlyRejectedForHypercharge =
  gateReceipt
    realOnly
    anomalyFreedom
    rejected
    "No complex U(1) lane is present, so this candidate cannot carry the SM hypercharge representation."

complexOnlyRejectedForWeakChirality : GateReceipt
complexOnlyRejectedForWeakChirality =
  gateReceipt
    complexOnly
    reality
    rejected
    "No quaternionic factor is present for the minimal real chiral weak lane."

quaternionOnlyRejectedForColour : GateReceipt
quaternionOnlyRejectedForColour =
  gateReceipt
    quaternionOnly
    minimality
    rejected
    "No rank-three complex factor is present for the colour lane."

weakHyperchargeHeldAtColour : GateReceipt
weakHyperchargeHeldAtColour =
  gateReceipt
    weakHyperchargeCandidate
    minimality
    held
    "The weak and abelian lanes are present, but the rank-three colour factor is absent."

standardModelRealityReceipt : GateReceipt
standardModelRealityReceipt =
  gateReceipt
    standardModelSpine
    reality
    survives
    "The C-H-M3(C) spine contains the real/complex/quaternionic factor types needed by the candidate real structure."

standardModelFirstOrderReceipt : GateReceipt
standardModelFirstOrderReceipt =
  gateReceipt
    standardModelSpine
    firstOrder
    held
    "A concrete finite Hilbert bimodule and internal Dirac operator are still required to prove the first-order condition."

standardModelCommutantReceipt : GateReceipt
standardModelCommutantReceipt =
  gateReceipt
    standardModelSpine
    commutant
    held
    "A concrete representation and charge-conjugation operator are still required to prove the order-zero condition."

standardModelAnomalyReceipt : GateReceipt
standardModelAnomalyReceipt =
  gateReceipt
    standardModelSpine
    anomalyFreedom
    held
    "Hypercharge assignments and fermion multiplicities must be supplied before anomaly cancellation can be proved."

standardModelMinimalityReceipt : GateReceipt
standardModelMinimalityReceipt =
  gateReceipt
    standardModelSpine
    minimality
    held
    "Uniqueness among all finite real star-algebra candidates is the remaining classification theorem."

------------------------------------------------------------------------
-- Honest boundary: structural survival does not imply uniqueness.
------------------------------------------------------------------------

data UniquenessOpen : Set where
  finiteInternalAlgebraClassificationOpen : UniquenessOpen

standardModelSpineIsCandidate : Set
standardModelSpineIsCandidate = ⊤

standardModelSpineIsCandidateWitness : standardModelSpineIsCandidate
standardModelSpineIsCandidateWitness = tt

standardModelUniquenessOpen : UniquenessOpen
standardModelUniquenessOpen = finiteInternalAlgebraClassificationOpen
