module DASHI.Interop.PrimeLaneStage12ActionCarryBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import Base369 using (tri-low)

import DASHI.Algebra.StageQuotient as StageQuotient
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Interop.PrimeLaneStage12ActionAdapter as Adapter

record PrimeLaneStage12ActionCarryBridgeAuthorityBits : Set where
  field
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    promotedStageSpine : Bool
    promotedStageSpineIsFalse : promotedStageSpine ≡ false
    promotedCarryDepthAuthority : Bool
    promotedCarryDepthAuthorityIsFalse : promotedCarryDepthAuthority ≡ false

canonicalPrimeLaneStage12ActionCarryBridgeAuthorityBits :
  PrimeLaneStage12ActionCarryBridgeAuthorityBits
canonicalPrimeLaneStage12ActionCarryBridgeAuthorityBits =
  record
    { candidateOnly = true
    ; candidateOnlyIsTrue = refl
    ; promotedStageSpine = false
    ; promotedStageSpineIsFalse = refl
    ; promotedCarryDepthAuthority = false
    ; promotedCarryDepthAuthorityIsFalse = refl
    }

record PrimeLaneStage12ActionCarryBridge : Set where
  field
    stage12FibreSurface :
      StageQuotient.Stage12FibreSurface
    stage12FibreSurfaceIsCanonical :
      stage12FibreSurface ≡ StageQuotient.canonicalStage12FibreSurface
    stageSeam :
      StageQuotient.Stage12FibreSurface.quotient
        stage12FibreSurface
        Atlas.atlas-11
      ≡
      tri-low
    p7Adapter :
      Adapter.PrimeLaneStage12ActionAdapter
    p7AdapterIsCanonical :
      p7Adapter ≡ Adapter.canonicalP7PrimeLaneStage12ActionAdapter
    p11Adapter :
      Adapter.PrimeLaneStage12ActionAdapter
    p11AdapterIsCanonical :
      p11Adapter ≡ Adapter.canonicalP11PrimeLaneStage12ActionAdapter
    p7CarryDepthSeamPointIsAtlas11 :
      Adapter.carryDepthSeamPoint p7Adapter ≡ Atlas.atlas-11
    p7CarryDepthSeam :
      StageQuotient.Stage12FibreSurface.carry-depth
        (Adapter.stage12FibreSurface p7Adapter)
        (Adapter.carryDepthSeamPoint p7Adapter)
      ≡
      Atlas.rev-2
    p11CarryDepthSeamPointIsAtlas11 :
      Adapter.carryDepthSeamPoint p11Adapter ≡ Atlas.atlas-11
    p11CarryDepthSeam :
      StageQuotient.Stage12FibreSurface.carry-depth
        (Adapter.stage12FibreSurface p11Adapter)
        (Adapter.carryDepthSeamPoint p11Adapter)
      ≡
      Atlas.rev-2
    notes :
      List String
    authorityBits :
      PrimeLaneStage12ActionCarryBridgeAuthorityBits

open PrimeLaneStage12ActionCarryBridge public

canonicalPrimeLaneStage12ActionCarryBridge :
  PrimeLaneStage12ActionCarryBridge
canonicalPrimeLaneStage12ActionCarryBridge =
  record
    { stage12FibreSurface = StageQuotient.canonicalStage12FibreSurface
    ; stage12FibreSurfaceIsCanonical = refl
    ; stageSeam = refl
    ; p7Adapter = Adapter.canonicalP7PrimeLaneStage12ActionAdapter
    ; p7AdapterIsCanonical = refl
    ; p11Adapter = Adapter.canonicalP11PrimeLaneStage12ActionAdapter
    ; p11AdapterIsCanonical = refl
    ; p7CarryDepthSeamPointIsAtlas11 = refl
    ; p7CarryDepthSeam = refl
    ; p11CarryDepthSeamPointIsAtlas11 = refl
    ; p11CarryDepthSeam = refl
    ; notes =
        "p7 and p11 now consume the same atlas-11/rev-2 carry-depth seam under Stage12FibreSurface."
      ∷ "The carry seam stays global; the prime lanes are local adapters into it."
      ∷ []
    ; authorityBits = canonicalPrimeLaneStage12ActionCarryBridgeAuthorityBits
    }
