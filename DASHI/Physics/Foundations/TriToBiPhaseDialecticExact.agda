module DASHI.Physics.Foundations.TriToBiPhaseDialecticExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Physics.Foundations.TriToBiSingularJunctionExact as Junction
import DASHI.Physics.Foundations.TriToBiTransportExact as Transport

------------------------------------------------------------------------
-- Three-point circle-phase analogue.  It records common-rotation
-- equivariance and a destructive-interference locus without claiming that
-- three discrete phases are the full circle S1.

data Phase3 : Set where
  phaseZero : Phase3
  phaseOne : Phase3
  phaseTwo : Phase3

rotatePhase : Phase3 → Phase3
rotatePhase phaseZero = phaseOne
rotatePhase phaseOne = phaseTwo
rotatePhase phaseTwo = phaseZero

data PhaseResult : Set where
  resolvedPhase : Phase3 → PhaseResult
  cancellationPhase : PhaseResult

rotateResult : PhaseResult → PhaseResult
rotateResult (resolvedPhase phase) = resolvedPhase (rotatePhase phase)
rotateResult cancellationPhase = cancellationPhase

phaseResultant : Phase3 → Phase3 → Phase3 → PhaseResult
phaseResultant phaseZero phaseZero phaseZero = resolvedPhase phaseZero
phaseResultant phaseOne phaseOne phaseOne = resolvedPhase phaseOne
phaseResultant phaseTwo phaseTwo phaseTwo = resolvedPhase phaseTwo
phaseResultant _ _ _ = cancellationPhase

phaseResultantRotationEquivariant :
  (a b c : Phase3) →
  phaseResultant (rotatePhase a) (rotatePhase b) (rotatePhase c)
  ≡
  rotateResult (phaseResultant a b c)
phaseResultantRotationEquivariant phaseZero phaseZero phaseZero = refl
phaseResultantRotationEquivariant phaseZero phaseZero phaseOne = refl
phaseResultantRotationEquivariant phaseZero phaseZero phaseTwo = refl
phaseResultantRotationEquivariant phaseZero phaseOne phaseZero = refl
phaseResultantRotationEquivariant phaseZero phaseOne phaseOne = refl
phaseResultantRotationEquivariant phaseZero phaseOne phaseTwo = refl
phaseResultantRotationEquivariant phaseZero phaseTwo phaseZero = refl
phaseResultantRotationEquivariant phaseZero phaseTwo phaseOne = refl
phaseResultantRotationEquivariant phaseZero phaseTwo phaseTwo = refl
phaseResultantRotationEquivariant phaseOne phaseZero phaseZero = refl
phaseResultantRotationEquivariant phaseOne phaseZero phaseOne = refl
phaseResultantRotationEquivariant phaseOne phaseZero phaseTwo = refl
phaseResultantRotationEquivariant phaseOne phaseOne phaseZero = refl
phaseResultantRotationEquivariant phaseOne phaseOne phaseOne = refl
phaseResultantRotationEquivariant phaseOne phaseOne phaseTwo = refl
phaseResultantRotationEquivariant phaseOne phaseTwo phaseZero = refl
phaseResultantRotationEquivariant phaseOne phaseTwo phaseOne = refl
phaseResultantRotationEquivariant phaseOne phaseTwo phaseTwo = refl
phaseResultantRotationEquivariant phaseTwo phaseZero phaseZero = refl
phaseResultantRotationEquivariant phaseTwo phaseZero phaseOne = refl
phaseResultantRotationEquivariant phaseTwo phaseZero phaseTwo = refl
phaseResultantRotationEquivariant phaseTwo phaseOne phaseZero = refl
phaseResultantRotationEquivariant phaseTwo phaseOne phaseOne = refl
phaseResultantRotationEquivariant phaseTwo phaseOne phaseTwo = refl
phaseResultantRotationEquivariant phaseTwo phaseTwo phaseZero = refl
phaseResultantRotationEquivariant phaseTwo phaseTwo phaseOne = refl
phaseResultantRotationEquivariant phaseTwo phaseTwo phaseTwo = refl

coupledPhaseJunction :
  Phase3 → Phase3 → Phase3 → PhaseResult × PhaseResult
coupledPhaseJunction a b c =
  phaseResultant a b c , phaseResultant a b c

rotatePhaseOutput :
  PhaseResult × PhaseResult → PhaseResult × PhaseResult
rotatePhaseOutput (left , right) =
  rotateResult left , rotateResult right

coupledPhaseRotationEquivariant :
  (a b c : Phase3) →
  coupledPhaseJunction (rotatePhase a) (rotatePhase b) (rotatePhase c)
  ≡
  rotatePhaseOutput (coupledPhaseJunction a b c)
coupledPhaseRotationEquivariant a b c =
  cong
    (λ result → result , result)
    (phaseResultantRotationEquivariant a b c)

destructiveInterferenceWitness :
  phaseResultant phaseZero phaseOne phaseTwo ≡ cancellationPhase
destructiveInterferenceWitness = refl

phaseResultToTrit : PhaseResult → Triadic.KernelTrit
phaseResultToTrit cancellationPhase = Triadic.zeroTrit
phaseResultToTrit (resolvedPhase phaseZero) = Triadic.positiveTrit
phaseResultToTrit (resolvedPhase phaseOne) = Triadic.positiveTrit
phaseResultToTrit (resolvedPhase phaseTwo) = Triadic.positiveTrit

cancellationMapsToTernaryNeutral :
  phaseResultToTrit
    (phaseResultant phaseZero phaseOne phaseTwo)
  ≡
  Triadic.zeroTrit
cancellationMapsToTernaryNeutral = refl

------------------------------------------------------------------------
-- Dialectical labels remain interpretation metadata.  The exact invariant is
-- a finite joint balance with an explicit residual.

data DialecticalStage : Set where
  triadicInputStage : DialecticalStage
  coupledBiOutputStage : DialecticalStage

inputJointQuantity : Nat
inputJointQuantity = 3

outputJointQuantity : Nat
outputJointQuantity = 2

junctionDialecticalResidual : Nat
junctionDialecticalResidual = 1

jointInvariantWithResidual :
  inputJointQuantity
  ≡
  outputJointQuantity + junctionDialecticalResidual
jointInvariantWithResidual = refl

record TriToBiSingularJunctionObject : Set where
  field
    criticalPresentation : Junction.CriticalPresentation
    fullyCoupled : Junction.FullyCoupledWitness
    transportBalance : Transport.MassBalance
    interpretationInput : DialecticalStage
    interpretationOutput : DialecticalStage

canonicalTriToBiSingularJunctionObject :
  TriToBiSingularJunctionObject
canonicalTriToBiSingularJunctionObject =
  record
    { criticalPresentation = Junction.multiplicityThreeSingularity
    ; fullyCoupled = Junction.canonicalFullyCoupledWitness
    ; transportBalance = Transport.canonicalTemporalBalance
    ; interpretationInput = triadicInputStage
    ; interpretationOutput = coupledBiOutputStage
    }

record TriToBiPhaseDialecticBoundary : Set where
  constructor triToBiPhaseDialecticBoundary
  field
    finitePhaseCancellationIsFullComplexInterferenceTheory : Bool
    finitePhaseCancellationIsFullComplexInterferenceTheoryIsFalse :
      finitePhaseCancellationIsFullComplexInterferenceTheory ≡ false

    dialecticalLabelFollowsFromTopologyAlone : Bool
    dialecticalLabelFollowsFromTopologyAloneIsFalse :
      dialecticalLabelFollowsFromTopologyAlone ≡ false

    multiplicityThreeConstructorProvesStableSingularityType : Bool
    multiplicityThreeConstructorProvesStableSingularityTypeIsFalse :
      multiplicityThreeConstructorProvesStableSingularityType ≡ false

open TriToBiPhaseDialecticBoundary public

canonicalTriToBiPhaseDialecticBoundary :
  TriToBiPhaseDialecticBoundary
canonicalTriToBiPhaseDialecticBoundary =
  triToBiPhaseDialecticBoundary false refl false refl false refl
