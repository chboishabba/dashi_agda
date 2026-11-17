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
--   test/data/golden/v1/xor_iit4_2026.json
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
--
-- The two upstream golden files also sharpen the version boundary: the 2026
-- intrinsic-information requirement collapses deterministic XOR system phi_s
-- from 1.5 to 0, while the same four distinctions, 15 relations and big-Phi
-- 9.5 remain present in the phi-structure.  Thus "system phi_s = 0" is not the
-- same claim as "the cause-effect structure is empty".
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
-- 2. External numerical source receipts.  Strings preserve decimal/exact text
--    without manufacturing internal real-number theorems.
------------------------------------------------------------------------

record PyPhiXORGoldenSourceReceipt : Set where
  constructor pyphi-xor-golden-source-receipt
  field
    repository : String
    inspectedSourceCommit : String
    goldenPath : String
    formalism : String
    mechanismMeasure : String
    systemMeasure : String
    goldenState : String
    systemPhi : String
    distinctionCount : Nat
    relationCount : Nat
    sumDistinctionPhi : String
    sumRelationPhi : String
    bigPhi : String
    sameTransitionLawKernelWitnessPresent : Bool
    externalNumericalResultIsAgdaKernelTheorem : Bool
open PyPhiXORGoldenSourceReceipt public

canonicalPyPhiXOR2023GoldenSourceReceipt : PyPhiXORGoldenSourceReceipt
canonicalPyPhiXOR2023GoldenSourceReceipt =
  pyphi-xor-golden-source-receipt
    "https://github.com/wmayner/pyphi"
    "134a8f31b49db512322465ed3ba5da7194d362fd"
    "test/data/golden/v1/xor_iit4_2023.json"
    "IIT_4_0_2023"
    "GENERALIZED_INTRINSIC_DIFFERENCE"
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

canonicalPyPhiXOR2026GoldenSourceReceipt : PyPhiXORGoldenSourceReceipt
canonicalPyPhiXOR2026GoldenSourceReceipt =
  pyphi-xor-golden-source-receipt
    "https://github.com/wmayner/pyphi"
    "134a8f31b49db512322465ed3ba5da7194d362fd"
    "test/data/golden/v1/xor_iit4_2026.json"
    "IIT_4_0_2026"
    "GENERALIZED_INTRINSIC_DIFFERENCE"
    "INTRINSIC_INFORMATION"
    "000"
    "0.0"
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
    golden2023CanCalibrateFiniteReference : Bool
    golden2026SeparatesSystemPhiFromPhiStructure : Bool
    deterministicSystemPhiZeroImpliesEmptyCES : Bool
    matchingGoldenFixtureAutomaticallyProvesAllOtherTPMs : Bool
    pyphiRemainsExternalNumericalAuthority : Bool
open PyPhiGoldenCalibrationBoundary public

canonicalPyPhiGoldenCalibrationBoundary : PyPhiGoldenCalibrationBoundary
canonicalPyPhiGoldenCalibrationBoundary =
  pyphi-golden-calibration-boundary true true true false false true
