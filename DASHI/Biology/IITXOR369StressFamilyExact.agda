module DASHI.Biology.IITXOR369StressFamilyExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IITMatchedFabricGateExperimentExact as Matched
import DASHI.Biology.IIT369MatchedAlgebraControlExact as Algebra
import DASHI.Biology.IIT4FiniteExecutableKernelExact as Kernel
import DASHI.Biology.IIT4FiniteCauseEffectStructureExact as Structure

------------------------------------------------------------------------
-- VERSIONED XOR / 369 STRESS FAMILY
--
-- This is a stress-test carrier, not a consciousness ranking. It juxtaposes
-- finite fixtures whose system-phi profiles are computed under the same
-- reference implementation while retaining alphabet/formalism metadata.
--
-- The 369 family is intentionally broader than 3^n cardinalities: both the
-- six-state HexTruth/S3 carrier control and the nine-state C9/C3^2 control are
-- represented explicitly.
------------------------------------------------------------------------

record StressFamilyReceipt : Set where
  constructor stressFamilyReceipt
  field
    binaryRecurrentXor2023 : String
    binaryXorGrid2023 : String
    ternaryRecurrentTriXor2023 : String
    z6RecurrentAddition2023 : String
    s3RecurrentComposition2023 : String
    z9RecurrentAddition2023 : String
    f3SquaredRecurrentAddition2023 : String
    deterministic2026Status : String
    scanner : String

open StressFamilyReceipt public

currentStressFamilyReceipt : StressFamilyReceipt
currentStressFamilyReceipt =
  stressFamilyReceipt
    "binary recurrent XOR: phi_s=2 on all states"
    "repo 2x2 XOR grid: phi_s in {0,0.5}"
    "ternary recurrent triXor: phi_s=log2(9) on all states"
    "Z6 / HexTruth recurrent addition: phi_s=log2(36) on all states"
    "S3 recurrent permutation composition: phi_s=log2(36) on all states"
    "Z9 recurrent addition: phi_s=log2(81) on all states"
    "F3^2 recurrent addition: phi_s=log2(81) on all states"
    "all listed deterministic fixtures: IIT_4_0_2026 system phi_s=0"
    "scripts/iit_xor_369_stress_scan.py"

record IITXOR369StressBoundary : Set where
  constructor iitXor369StressBoundary
  field
    formalismVersionRecorded : Bool
    alphabetSizeRecorded : Bool
    sixStateAlgebraControlIncluded : Bool
    nineStateAlgebraControlIncluded : Bool
    systemPhiAndBigPhiRemainSeparate : Bool
    systemPhiOrderingIsConsciousnessOrdering : Bool
    historicalIITQuantityEqualsIIT4BigPhi : Bool
    deterministicZeroSystemPhiErasesCauseEffectStructureByDefinition : Bool
    numericalStressReceiptIsKernelProof : Bool

open IITXOR369StressBoundary public

canonicalIITXOR369StressBoundary : IITXOR369StressBoundary
canonicalIITXOR369StressBoundary =
  iitXor369StressBoundary true true true true true false false false false

stressRankingDoesNotSelfPromote :
  systemPhiOrderingIsConsciousnessOrdering
    canonicalIITXOR369StressBoundary ≡ false
stressRankingDoesNotSelfPromote = refl

historicalVersionDoesNotSelfPromote :
  historicalIITQuantityEqualsIIT4BigPhi
    canonicalIITXOR369StressBoundary ≡ false
historicalVersionDoesNotSelfPromote = refl

matchedExperimentReceipt : Matched.MatchedSweepReceipt
matchedExperimentReceipt = Matched.currentMatchedSweepReceipt

algebraControlReceipt : Algebra.AlgebraControlReceipt
algebraControlReceipt = Algebra.currentAlgebraControlReceipt

structureBoundary : Structure.IIT4CauseEffectStructureBoundary
structureBoundary = Structure.canonicalIIT4CauseEffectStructureBoundary

kernelBoundary : Kernel.IIT4ExecutableKernelBoundary
kernelBoundary = Kernel.canonicalIIT4ExecutableKernelBoundary
