module DASHI.Physics.Gravity.KKCircleQEDChiralityConsumerExact where

------------------------------------------------------------------------
-- KK physical-photon BIDI: QED electron vs electroweak chirality
--
-- Finite, consumer-specific non-descent fixture ONLY.
-- The smooth S1 zero-mode pairing statement itself follows from
-- separated 5D Dirac equations / periodic monodromy; this finite
-- theorem does NOT formalise the continuum Dirac operator or Atiyah-
-- Singer index. See check_kk_light_qed_dirac_same_action.py.
--
-- Reuse canonical SM chirality owner and canonical DASHI transport.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Laws.StandardModelLawBoundary as SM
import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair

data PhysicalQEDCharge : Set where
  electronMinusOne : PhysicalQEDCharge

data PhysicalQEDMassLabel : Set where
  electronMassInput : PhysicalQEDMassLabel

data DiracComponent : Set where
  electronLeftComponent electronRightComponent : DiracComponent

-- Both components are equally charged under the UNBROKEN QED U(1),
-- and are assigned the same Dirac mass; their weak representations
-- are separate source-side information.
qedObserve : DiracComponent →
  PhysicalQEDCharge × PhysicalQEDMassLabel
qedObserve electronLeftComponent =
  electronMinusOne , electronMassInput
qedObserve electronRightComponent =
  electronMinusOne , electronMassInput

chiralityQuestion : DiracComponent → SM.Chirality
chiralityQuestion electronLeftComponent = SM.leftHanded
chiralityQuestion electronRightComponent = SM.rightHanded

data ElectroweakRepresentation : Set where
  suTwoDoublet suTwoSinglet : ElectroweakRepresentation

weakRepresentationQuestion : DiracComponent → ElectroweakRepresentation
weakRepresentationQuestion electronLeftComponent = suTwoDoublet
weakRepresentationQuestion electronRightComponent = suTwoSinglet

leftNotRight : SM.leftHanded ≡ SM.rightHanded → ⊥
leftNotRight ()

doubletNotSinglet : suTwoDoublet ≡ suTwoSinglet → ⊥
doubletNotSinglet ()

qedDoesNotDetermineChirality :
  Transport.ClaimNonTransportWitness qedObserve chiralityQuestion
qedDoesNotDetermineChirality =
  Descent.consumerNonDescentWitness
    electronLeftComponent electronRightComponent refl leftNotRight

qedDoesNotDetermineWeakRepresentation :
  Transport.ClaimNonTransportWitness qedObserve weakRepresentationQuestion
qedDoesNotDetermineWeakRepresentation =
  Descent.consumerNonDescentWitness
    electronLeftComponent electronRightComponent refl doubletNotSinglet

noElectroweakChiralityPromotionFromQED :
  Transport.ClaimTransport qedObserve chiralityQuestion → ⊥
noElectroweakChiralityPromotionFromQED =
  Transport.claimNonTransportWitnessBlocksTransport
    qedDoesNotDetermineChirality

noElectroweakRepresentationPromotionFromQED :
  Transport.ClaimTransport qedObserve weakRepresentationQuestion → ⊥
noElectroweakRepresentationPromotionFromQED =
  Transport.claimNonTransportWitnessBlocksTransport
    qedDoesNotDetermineWeakRepresentation

-- A sufficient refinement must distinguish left/right; ordinary
-- QED electric charge and physical Dirac mass cannot do so.
refiningQEDToChiralityRequiresSeparateHandedness :
  (refine : DiracComponent → Bool) →
  Repair.RefinementRepairs qedObserve refine chiralityQuestion →
  refine electronLeftComponent ≡ refine electronRightComponent → ⊥
refiningQEDToChiralityRequiresSeparateHandedness refine sufficient same =
  Repair.refinementRepairSeparatesWitness
    qedDoesNotDetermineChirality sufficient same

-- Passing the limited physical QED consumer is not invalidated.
qedObservableStillValid :
  Transport.ClaimTransport qedObserve qedObserve
qedObservableStillValid = Transport.identityClaimTransport qedObserve

-- Structurally separating the missing information suffices for the
-- finite QED/weak-representation query, NOT for a physical SM model.
qedWithWeakRefinement : DiracComponent →
  (PhysicalQEDCharge × PhysicalQEDMassLabel) × ElectroweakRepresentation
qedWithWeakRefinement state =
  qedObserve state , weakRepresentationQuestion state

weakFactorFromRefinement :
  Transport.ClaimTransport qedWithWeakRefinement weakRepresentationQuestion
weakFactorFromRefinement =
  Transport.claimTransport proj₂ (λ state → refl)
