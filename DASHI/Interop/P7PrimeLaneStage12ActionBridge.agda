module DASHI.Interop.P7PrimeLaneStage12ActionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.StageQuotient as StageQuotient
import DASHI.Foundations.P7UnitGroupC6Witness as P7C6
import DASHI.Foundations.PrimeLaneUnitActionQuotient as Quotient
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Interop.PrimeLaneStage12ActionAdapter as Adapter
import DASHI.Interop.PrimeSuccessorWitness as Successor
import DASHI.Physics.Closure.P7Stage7C6HexRegression as Regression

record P7PrimeLaneStage12ActionBridgeAuthorityBits : Set where
  field
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    promotedStageSpine : Bool
    promotedStageSpineIsFalse : promotedStageSpine ≡ false
    promotedPrimeUniversal : Bool
    promotedPrimeUniversalIsFalse : promotedPrimeUniversal ≡ false
    promotedPhysicsAuthority : Bool
    promotedPhysicsAuthorityIsFalse : promotedPhysicsAuthority ≡ false

canonicalP7PrimeLaneStage12ActionBridgeAuthorityBits :
  P7PrimeLaneStage12ActionBridgeAuthorityBits
canonicalP7PrimeLaneStage12ActionBridgeAuthorityBits =
  record
    { candidateOnly = true
    ; candidateOnlyIsTrue = refl
    ; promotedStageSpine = false
    ; promotedStageSpineIsFalse = refl
    ; promotedPrimeUniversal = false
    ; promotedPrimeUniversalIsFalse = refl
    ; promotedPhysicsAuthority = false
    ; promotedPhysicsAuthorityIsFalse = refl
    }

record P7PrimeLaneStage12ActionBridge : Set where
  constructor mkP7PrimeLaneStage12ActionBridge
  field
    bridgeLabel : String
    stage12Adapter :
      Adapter.PrimeLaneStage12ActionAdapter
    stage12AdapterIsCanonical :
      stage12Adapter ≡ Adapter.canonicalP7PrimeLaneStage12ActionAdapter
    quotientSurfaceIsCanonical :
      Adapter.quotientSurface stage12Adapter
      ≡
      Quotient.p7C6PrimeLaneUnitActionQuotientSurface
    successorWitness :
      Successor.PrimeSuccessorWitness
    successorWitnessIsCanonical :
      successorWitness ≡ Successor.canonicalP7PrimeSuccessorWitness
    stageWindowWitness :
      Successor.StageSuccessorWitness
    stageWindowWitnessIsCanonical :
      stageWindowWitness ≡ Successor.canonicalStage6SuccessorWitness
    unitGroupWitness :
      P7C6.P7UnitGroupC6Witness
    unitGroupWitnessIsCanonical :
      unitGroupWitness ≡ P7C6.canonicalP7UnitGroupC6Witness
    p7Regression :
      Regression.P7Stage7C6HexRegression
    p7RegressionIsCanonical :
      p7Regression ≡ Regression.canonicalP7Stage7C6HexRegression
    adapterSuccessorWitness :
      Adapter.successorWitness stage12Adapter ≡ successorWitness
    adapterStageWindowWitness :
      Adapter.stageWindowWitness stage12Adapter ≡ stageWindowWitness
    regressionUnitGroupWitness :
      Regression.unitGroupWitness p7Regression ≡ unitGroupWitness
    regressionStage7Identity :
      Regression.stage7Identity p7Regression ≡ refl
    regressionStage6UnitOrder :
      Regression.stage6UnitOrder p7Regression ≡ refl
    adapterStageIdentityPointIsAtlas7 :
      Adapter.stageIdentityPoint stage12Adapter ≡ Atlas.atlas-7
    adapterUnitOrderStagePointIsAtlas6 :
      Adapter.unitOrderStagePoint stage12Adapter ≡ Atlas.atlas-6
    adapterCarryDepthSeamPointIsAtlas11 :
      Adapter.carryDepthSeamPoint stage12Adapter ≡ Atlas.atlas-11
    adapterCarryDepthSeam :
      StageQuotient.Stage12FibreSurface.carry-depth
        (Adapter.stage12FibreSurface stage12Adapter)
        (Adapter.carryDepthSeamPoint stage12Adapter)
      ≡
      Atlas.rev-2
    bridgeAuthorityBits :
      P7PrimeLaneStage12ActionBridgeAuthorityBits
    bridgeNotes :
      List String

open P7PrimeLaneStage12ActionBridge public
open P7PrimeLaneStage12ActionBridgeAuthorityBits public

canonicalP7PrimeLaneStage12ActionBridge :
  P7PrimeLaneStage12ActionBridge
canonicalP7PrimeLaneStage12ActionBridge =
  mkP7PrimeLaneStage12ActionBridge
    "p7-stage12-adapter-bridge"
    Adapter.canonicalP7PrimeLaneStage12ActionAdapter
    refl
    refl
    Successor.canonicalP7PrimeSuccessorWitness
    refl
    Successor.canonicalStage6SuccessorWitness
    refl
    P7C6.canonicalP7UnitGroupC6Witness
    refl
    Regression.canonicalP7Stage7C6HexRegression
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    canonicalP7PrimeLaneStage12ActionBridgeAuthorityBits
    ( "The Stage12 adapter is the shared public carrier for the p7 lane."
    ∷ "The p7 successor witness explains the +1 move from stage 6 into the p7 prime lane."
    ∷ "The p7 regression remains local, while the adapter keeps the lane under the global Stage12 spine."
    ∷ []
    )
