module DASHI.Moonshine.MonsterWeightTwoGriessConstituentCompilerEverything where

-- Focused rollup for the actual 196883-dimensional Griess constituent seam.
-- This exports the proof-relevant upstream linear-action hardening, the
-- representation-level constituent compiler, its validation, and the current
-- linear/isotypic status owner.  It deliberately does not manufacture the
-- missing actual Monster representation object or its inclusion from character
-- and dimension data.

import DASHI.Moonshine.Monster3BLinearActionProofRelevantHardeningExact
import DASHI.Moonshine.Monster3BLinearActionProofRelevantHardeningValidation
import DASHI.Moonshine.MonsterWeightTwoGriessConstituentCompilerExact
import DASHI.Moonshine.MonsterWeightTwoGriessConstituentCompilerValidation
import DASHI.Moonshine.Monster3BLinearIsotypicCurrentMaxCutExact
