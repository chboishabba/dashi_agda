module DASHI.Interop.PrimeLaneStage12ActionAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import Base369 using (tri-high; tri-low)
open import LogicTlurey using (overflow; resonance)

import DASHI.Algebra.StageQuotient as StageQuotient
import DASHI.Foundations.PrimeLaneUnitActionQuotient as Quotient
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Interop.PrimeSuccessorWitness as Successor
import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge as Phase

------------------------------------------------------------------------
-- Prime-lane adapters into the global Stage12 fibre atlas.
--
-- Stage12FibreSurface is the global stage/carry/fibre grammar.
-- Prime-local quotient-action lanes plug into that atlas through adapter rows.
-- The shared surface is now generic enough that p7, p11, and the full
-- 12->13 closure witness all consume the same adapter contract.

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
    quotientSurface :
      Quotient.PrimeLaneUnitActionQuotientSurface
    successorWitness :
      Successor.PrimeSuccessorWitness
    quotientPrimeMatchesSuccessorWitness :
      Quotient.primeIdentity quotientSurface
      ≡
      Successor.witnessPrime successorWitness
    stageWindowWitness :
      Successor.StageSuccessorWitness
    stageWindowWitnessMatchesSuccessorWitness :
      Successor.stage stageWindowWitness
      ≡
      Successor.stageWitnessed successorWitness
    stageWindowProjectedWitnessMatchesPrime :
      Successor.projectedWitnessPoint stageWindowWitness
      ≡
      Successor.primeLaneStagePoint successorWitness
    successorField0To111 :
      Successor.StageWindowSuccessorField
    successorField0To111IsCanonical :
      successorField0To111 ≡ Successor.canonicalStage0To111SuccessorField
    stageIdentityPoint :
      Atlas.StageAtlasZeroToEleven
    stageIdentityPointMatchesSuccessorWitness :
      stageIdentityPoint ≡ Successor.primeLaneStagePoint successorWitness
    stageIdentityPointMatchesPhaseBridge :
      stageIdentityPoint ≡
      Phase.primeIdentityStage (Quotient.phaseBridge quotientSurface)
    stageIdentityResidue :
      StageQuotient.Stage12FibreSurface.residue
        stage12FibreSurface
        stageIdentityPoint
      ≡
      Successor.primeLaneResidue successorWitness
    stageIdentityTone :
      StageQuotient.Stage12FibreSurface.quotient
        stage12FibreSurface
        stageIdentityPoint
      ≡
      Successor.primeLaneTone successorWitness
    unitActionOrder :
      Nat
    unitActionOrderMatchesSuccessorWitness :
      unitActionOrder ≡ Successor.witnessSpaceOrder successorWitness
    unitActionOrderMatchesPhaseBridge :
      unitActionOrder ≡ Phase.unitOrder (Quotient.phaseBridge quotientSurface)
    unitOrderStagePoint :
      Atlas.StageAtlasZeroToEleven
    unitOrderStagePointMatchesSuccessorWitness :
      unitOrderStagePoint ≡ Successor.witnessSpaceStagePoint successorWitness
    unitOrderStagePointMatchesPhaseBridge :
      unitOrderStagePoint ≡
      Phase.unitOrderStage (Quotient.phaseBridge quotientSurface)
    unitOrderResidue :
      StageQuotient.Stage12FibreSurface.residue
        stage12FibreSurface
        unitOrderStagePoint
      ≡
      Successor.witnessSpaceResidue successorWitness
    unitOrderTone :
      StageQuotient.Stage12FibreSurface.quotient
        stage12FibreSurface
        unitOrderStagePoint
      ≡
      Successor.witnessSpaceTone successorWitness
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
    ; quotientSurface =
        Quotient.p7C6PrimeLaneUnitActionQuotientSurface
    ; successorWitness =
        Successor.canonicalP7PrimeSuccessorWitness
    ; quotientPrimeMatchesSuccessorWitness =
        refl
    ; stageWindowWitness =
        Successor.canonicalStage6SuccessorWitness
    ; stageWindowWitnessMatchesSuccessorWitness =
        refl
    ; stageWindowProjectedWitnessMatchesPrime =
        refl
    ; successorField0To111 =
        Successor.canonicalStage0To111SuccessorField
    ; successorField0To111IsCanonical =
        refl
    ; stageIdentityPoint =
        Atlas.atlas-7
    ; stageIdentityPointMatchesSuccessorWitness =
        refl
    ; stageIdentityPointMatchesPhaseBridge =
        refl
    ; stageIdentityResidue =
        refl
    ; stageIdentityTone =
        refl
    ; unitActionOrder =
        6
    ; unitActionOrderMatchesSuccessorWitness =
        refl
    ; unitActionOrderMatchesPhaseBridge =
        refl
    ; unitOrderStagePoint =
        Atlas.atlas-6
    ; unitOrderStagePointMatchesSuccessorWitness =
        refl
    ; unitOrderStagePointMatchesPhaseBridge =
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
    ; authorityBits =
        canonicalPrimeLaneStage12ActionAuthorityBits
    ; notes =
        "Stage12FibreSurface is the global stage/carry/fibre grammar; p7 consumes it through the shared prime-lane adapter contract."
      ∷ "The prime-successor rule is explicit here: 6-action ecology +1 = 7-prime lane."
      ∷ "The p7 row remains the first canonical C6/HexTruth local witness under Stage12 rather than a replacement for the stage spine."
      ∷ "atlas-11/rev-2 remains the global carry-depth seam and is not reducible to the p7 lane."
      ∷ []
    }

canonicalP11PrimeLaneStage12ActionAdapter :
  PrimeLaneStage12ActionAdapter
canonicalP11PrimeLaneStage12ActionAdapter =
  record
    { primeLaneLabel =
        "p11"
    ; unitGroupLabel =
        "(Z/11Z)^x ~= C10"
    ; stage12FibreSurface =
        StageQuotient.canonicalStage12FibreSurface
    ; stage12FibreSurfaceIsCanonical =
        refl
    ; quotientSurface =
        Quotient.p11C10PrimeLaneUnitActionQuotientSurface
    ; successorWitness =
        Successor.canonicalP11PrimeSuccessorWitness
    ; quotientPrimeMatchesSuccessorWitness =
        refl
    ; stageWindowWitness =
        Successor.canonicalStage10SuccessorWitness
    ; stageWindowWitnessMatchesSuccessorWitness =
        refl
    ; stageWindowProjectedWitnessMatchesPrime =
        refl
    ; successorField0To111 =
        Successor.canonicalStage0To111SuccessorField
    ; successorField0To111IsCanonical =
        refl
    ; stageIdentityPoint =
        Atlas.atlas-11
    ; stageIdentityPointMatchesSuccessorWitness =
        refl
    ; stageIdentityPointMatchesPhaseBridge =
        refl
    ; stageIdentityResidue =
        refl
    ; stageIdentityTone =
        refl
    ; unitActionOrder =
        10
    ; unitActionOrderMatchesSuccessorWitness =
        refl
    ; unitActionOrderMatchesPhaseBridge =
        refl
    ; unitOrderStagePoint =
        Atlas.atlas-10
    ; unitOrderStagePointMatchesSuccessorWitness =
        refl
    ; unitOrderStagePointMatchesPhaseBridge =
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
    ; authorityBits =
        canonicalPrimeLaneStage12ActionAuthorityBits
    ; notes =
        "Stage12FibreSurface is the global stage/carry/fibre grammar; p11 now consumes the same adapter contract as p7."
      ∷ "The prime-successor rule is explicit here: 10-cycle witness-space +1 = 11-prime lane."
      ∷ "The p11 row records Stage-11 identity placement and Stage-10 unit-order placement without claiming that p11 defines the stage spine."
      ∷ "atlas-11/rev-2 remains the shared carry-depth seam, so p11 joins the same global Stage12 route instead of a parallel one."
      ∷ []
    }

canonicalP13PrimeLaneStage12ActionAdapter :
  PrimeLaneStage12ActionAdapter
canonicalP13PrimeLaneStage12ActionAdapter =
  record
    { primeLaneLabel =
        "p13"
    ; unitGroupLabel =
        "(Z/13Z)^x ~= C12"
    ; stage12FibreSurface =
        StageQuotient.canonicalStage12FibreSurface
    ; stage12FibreSurfaceIsCanonical =
        refl
    ; quotientSurface =
        Quotient.p13C12PrimeLaneUnitActionQuotientSurface
    ; successorWitness =
        Successor.canonicalP13PrimeSuccessorWitness
    ; quotientPrimeMatchesSuccessorWitness =
        refl
    ; stageWindowWitness =
        Successor.canonicalStage12SuccessorWitness
    ; stageWindowWitnessMatchesSuccessorWitness =
        refl
    ; stageWindowProjectedWitnessMatchesPrime =
        refl
    ; successorField0To111 =
        Successor.canonicalStage0To111SuccessorField
    ; successorField0To111IsCanonical =
        refl
    ; stageIdentityPoint =
        Atlas.atlas-1
    ; stageIdentityPointMatchesSuccessorWitness =
        refl
    ; stageIdentityPointMatchesPhaseBridge =
        refl
    ; stageIdentityResidue =
        refl
    ; stageIdentityTone =
        refl
    ; unitActionOrder =
        12
    ; unitActionOrderMatchesSuccessorWitness =
        refl
    ; unitActionOrderMatchesPhaseBridge =
        refl
    ; unitOrderStagePoint =
        Atlas.atlas-0
    ; unitOrderStagePointMatchesSuccessorWitness =
        refl
    ; unitOrderStagePointMatchesPhaseBridge =
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
    ; authorityBits =
        canonicalPrimeLaneStage12ActionAuthorityBits
    ; notes =
        "Stage12FibreSurface remains the global stage/carry/fibre grammar; p13 consumes it as the first full 12->13 closure witness row."
      ∷ "The prime-successor rule is explicit here: the Stage12 witness-space +1 = 13-prime lane."
      ∷ "The p13 row records the closure witness over the whole Stage12 carrier without claiming that p13 replaces the stage spine."
      ∷ "atlas-11/rev-2 remains the shared carry-depth seam, so the closure witness joins the same global Stage12 route as p7 and p11."
      ∷ []
    }

canonicalPrimeLaneStage12ActionAdapters :
  List PrimeLaneStage12ActionAdapter
canonicalPrimeLaneStage12ActionAdapters =
  canonicalP7PrimeLaneStage12ActionAdapter
  ∷ canonicalP11PrimeLaneStage12ActionAdapter
  ∷ canonicalP13PrimeLaneStage12ActionAdapter
  ∷ []
