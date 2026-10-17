module DASHI.Biology.IITFaceAwarePyPhiGoldenCalibrationExact where

------------------------------------------------------------------------
-- CANONICAL PYPHI XOR GOLDEN FIXTURE / FACE-AWARE CONTROL SAME-TPM RECEIPT
--
-- Upstream source:
--   https://github.com/wmayner/pyphi
--   inspected source commit:
--     134a8f31b49db512322465ed3ba5da7194d362fd
--   pyphi/examples.py :: xor_substrate
--   test/data/golden/v1/xor_iit4_2023.json
--
-- The upstream canonical XOR substrate is exactly the three-node update
--
--   A' = B xor C
--   B' = A xor C
--   C' = A xor B
--
-- at state 000.  That is literally the pairwise control already used by
-- IITFaceAwareTriadicCausalPairExact.  The theorem below pays the local
-- same-transition-law identification; the external numerical values remain a
-- source receipt, not an Agda proof of PyPhi's computation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IITFaceAwareTriadicCausalPairExact as Face

------------------------------------------------------------------------
-- 1. Re-expression of the published/current upstream XOR example law.
------------------------------------------------------------------------

pyphiCanonicalXorStep : Face.BitTriple → Face.BitTriple
pyphiCanonicalXorStep state = Face.bits
  (Face.xorB (Face.bitB state) (Face.bitC state))
  (Face.xorB (Face.bitA state) (Face.bitC state))
  (Face.xorB (Face.bitA state) (Face.bitB state))

pairwiseControlIsCanonicalPyPhiXorTPM :
  (state : Face.BitTriple) →
  Face.pairwiseStep state ≡ pyphiCanonicalXorStep state
pairwiseControlIsCanonicalPyPhiXorTPM state = refl

pyphiGoldenState : Face.BitTriple
pyphiGoldenState = Face.zeros

pairwiseGoldenStateTransition :
  Face.pairwiseStep pyphiGoldenState ≡ Face.zeros
pairwiseGoldenStateTransition = refl

------------------------------------------------------------------------
-- 2. External numerical source receipt.  Strings preserve decimal/exact text
--    without manufacturing an internal real-number theorem.
------------------------------------------------------------------------

record PyPhiXOR2023GoldenSourceReceipt : Set where
  constructor pyphi-xor-2023-golden-source-receipt
  field
    repository : String
    inspectedSourceCommit : String
    goldenPath : String
    formalism : String
    mechanismMeasure : String
    goldenState : String
    systemPhi : String
    distinctionCount : Nat
    relationCount : Nat
    sumDistinctionPhi : String
    sumRelationPhi : String
    bigPhi : String
    sameTransitionLawKernelWitnessPresent : Bool
    externalNumericalResultIsAgdaKernelTheorem : Bool
open PyPhiXOR2023GoldenSourceReceipt public

canonicalPyPhiXOR2023GoldenSourceReceipt : PyPhiXOR2023GoldenSourceReceipt
canonicalPyPhiXOR2023GoldenSourceReceipt =
  pyphi-xor-2023-golden-source-receipt
    "https://github.com/wmayner/pyphi"
    "134a8f31b49db512322465ed3ba5da7194d362fd"
    "test/data/golden/v1/xor_iit4_2023.json"
    "IIT_4_0_2023"
    "GENERALIZED_INTRINSIC_DIFFERENCE"
    "000"
    "1.5"
    4
    15
    "2.5"
    "7.0"
    "9.5"
    true
    false

record PyPhiGoldenCalibrationBoundary : Set where
  constructor pyphi-golden-calibration-boundary
  field
    pairwiseControlSameTPMAsCanonicalXOR : Bool
    goldenFixtureCanCalibrateFiniteReference : Bool
    matchingGoldenFixtureAutomaticallyProvesAllOtherTPMs : Bool
    pyphiRemainsExternalNumericalAuthority : Bool
open PyPhiGoldenCalibrationBoundary public

canonicalPyPhiGoldenCalibrationBoundary : PyPhiGoldenCalibrationBoundary
canonicalPyPhiGoldenCalibrationBoundary =
  pyphi-golden-calibration-boundary true true false true
