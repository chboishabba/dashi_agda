module DASHI.Interop.PrimeLaneStage12ActionAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import Base369 using (tri-high; tri-low)
open import LogicTlurey using (overflow; resonance)

import DASHI.Algebra.StageQuotient as StageQuotient
import DASHI.Interop.PrimeSuccessorWitness as Successor
import DASHI.Foundations.P7UnitGroupC6Witness as P7C6
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Physics.Closure.P7Stage7C6HexRegression as P7Regression

------------------------------------------------------------------------
-- Prime-lane adapters into the global Stage12 fibre atlas.
--
-- Stage12FibreSurface is now the general stage/carry/fibre grammar.
-- Prime-local unit-action lanes plug into that atlas through adapter rows.
-- The p7 tranche is the first clean worked exemplar: it witnesses the
-- Stage-7 identity placement, the Stage-6 unit-order placement, and the
-- atlas-11 carry-depth seam without claiming that p7 defines the stage spine.

record PrimeLaneStage12ActionAuthorityBits : Set where
  field
    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true
    promotedStageSpine :
      Bool
    promotedStageSpineIsFalse :
      promotedStageSpine ≡ false
    promotedPrimeUniversal :
      Bool
    promotedPrimeUniversalIsFalse :
      promotedPrimeUniversal ≡ false
    promotedAnalyticPadicAuthority :
      Bool
    promotedAnalyticPadicAuthorityIsFalse :
      promotedAnalyticPadicAuthority ≡ false
    promotedClayAuthority :
      Bool
    promotedClayAuthorityIsFalse :
      promotedClayAuthority ≡ false

canonicalPrimeLaneStage12ActionAuthorityBits :
  PrimeLaneStage12ActionAuthorityBits
canonicalPrimeLaneStage12ActionAuthorityBits =
  record
    { candidateOnly = true
    ; candidateOnlyIsTrue = refl
    ; promotedStageSpine = false
    ; promotedStageSpineIsFalse = refl
    ; promotedPrimeUniversal = false
    ; promotedPrimeUniversalIsFalse = refl
    ; promotedAnalyticPadicAuthority = false
    ; promotedAnalyticPadicAuthorityIsFalse = refl
    ; promotedClayAuthority = false
    ; promotedClayAuthorityIsFalse = refl
    }

record PrimeLaneStage12ActionAdapter : Set where
  field
    primeLaneLabel :
      String
    unitGroupLabel :
      String
    stage12FibreSurface :
      StageQuotient.Stage12FibreSurface
    stage12FibreSurfaceIsCanonical :
      stage12FibreSurface ≡ StageQuotient.canonicalStage12FibreSurface
    successorWitness :
      Successor.PrimeSuccessorWitness
    successorWitnessIsCanonical :
      successorWitness ≡ Successor.canonicalP7PrimeSuccessorWitness
    stageWindowWitness :
      Successor.StageSuccessorWitness
    stageWindowWitnessIsCanonical :
      stageWindowWitness ≡ Successor.canonicalStage6SuccessorWitness
    stageIdentityPoint :
      Atlas.StageAtlasZeroToEleven
    stageIdentityPointIsAtlas7 :
      stageIdentityPoint ≡ Atlas.atlas-7
    stageIdentityResidue :
      StageQuotient.Stage12FibreSurface.residue stage12FibreSurface stageIdentityPoint
      ≡ overflow
    stageIdentityTone :
      StageQuotient.Stage12FibreSurface.quotient stage12FibreSurface stageIdentityPoint
      ≡ tri-low
    unitActionOrder :
      Nat
    unitActionOrderIs6 :
      unitActionOrder ≡ 6
    unitOrderStagePoint :
      Atlas.StageAtlasZeroToEleven
    unitOrderStagePointIsAtlas6 :
      unitOrderStagePoint ≡ Atlas.atlas-6
    unitOrderResidue :
      StageQuotient.Stage12FibreSurface.residue stage12FibreSurface unitOrderStagePoint
      ≡ resonance
    unitOrderTone :
      StageQuotient.Stage12FibreSurface.quotient stage12FibreSurface unitOrderStagePoint
      ≡ tri-high
    carryDepthSeamPoint :
      Atlas.StageAtlasZeroToEleven
    carryDepthSeamPointIsAtlas11 :
      carryDepthSeamPoint ≡ Atlas.atlas-11
    carryDepthSeam :
      StageQuotient.Stage12FibreSurface.carry-depth
        stage12FibreSurface
        carryDepthSeamPoint
      ≡
      Atlas.rev-2
    localRegression :
      P7Regression.P7Stage7C6HexRegression
    localRegressionStage7Witness :
      P7C6.p7IdentityStageIsStage7 ≡ refl
    localRegressionStage6Witness :
      P7C6.p7UnitStageIsStage6 ≡ refl
    localRegressionMobiusWitness :
      P7C6.p7GeneratorCubedIsMobius ≡ refl
    authorityBits :
      PrimeLaneStage12ActionAuthorityBits
    notes :
      List String

open PrimeLaneStage12ActionAuthorityBits public
open PrimeLaneStage12ActionAdapter public

canonicalP7PrimeLaneStage12ActionAdapter :
  PrimeLaneStage12ActionAdapter
canonicalP7PrimeLaneStage12ActionAdapter =
  record
    { primeLaneLabel =
        "p7"
    ; unitGroupLabel =
        "(Z/7Z)^x ~= C6"
    ; stage12FibreSurface =
        StageQuotient.canonicalStage12FibreSurface
    ; stage12FibreSurfaceIsCanonical =
        refl
    ; successorWitness =
        Successor.canonicalP7PrimeSuccessorWitness
    ; successorWitnessIsCanonical =
        refl
    ; stageWindowWitness =
        Successor.canonicalStage6SuccessorWitness
    ; stageWindowWitnessIsCanonical =
        refl
    ; stageIdentityPoint =
        Atlas.atlas-7
    ; stageIdentityPointIsAtlas7 =
        refl
    ; stageIdentityResidue =
        refl
    ; stageIdentityTone =
        refl
    ; unitActionOrder =
        6
    ; unitActionOrderIs6 =
        refl
    ; unitOrderStagePoint =
        Atlas.atlas-6
    ; unitOrderStagePointIsAtlas6 =
        refl
    ; unitOrderResidue =
        refl
    ; unitOrderTone =
        refl
    ; carryDepthSeamPoint =
        Atlas.atlas-11
    ; carryDepthSeamPointIsAtlas11 =
        refl
    ; carryDepthSeam =
        refl
    ; localRegression =
        P7Regression.canonicalP7Stage7C6HexRegression
    ; localRegressionStage7Witness =
        refl
    ; localRegressionStage6Witness =
        refl
    ; localRegressionMobiusWitness =
        refl
    ; authorityBits =
        canonicalPrimeLaneStage12ActionAuthorityBits
    ; notes =
        "Stage12FibreSurface is now the general stage/carry/fibre grammar; prime lanes are local unit-action adapters into it."
      ∷ "The prime-successor rule is explicit here: 6-action ecology +1 = 7-prime lane."
      ∷ "The p7 row is also the stage-6 successor witness inside the full 0..11 table, not a replacement for that table."
      ∷ "The p7 lane is the first canonical C6/HexTruth local witness: Stage-7 is its identity placement and Stage-6 is its unit-order placement."
      ∷ "atlas-11/rev-2 remains the more global carry-depth seam and is not reducible to the p7 lane."
      ∷ []
    }
