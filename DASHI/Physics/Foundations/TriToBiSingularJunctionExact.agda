module DASHI.Physics.Foundations.TriToBiSingularJunctionExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- Finite exact carrier for a connected three-input/two-output event.
-- The topological numbers are declared as a finite shadow of the smooth
-- cobordism calculation.  No finite constructor is promoted to a smooth
-- manifold or singularity-theory classification.

data BoundaryPort : Set where
  incomingOne : BoundaryPort
  incomingTwo : BoundaryPort
  incomingThree : BoundaryPort
  outgoingOne : BoundaryPort
  outgoingTwo : BoundaryPort

boundaryPortCount : Nat
boundaryPortCount = 5

data Connectivity : Set where
  connectedJunction : Connectivity
  disconnectedPantsCylinder : Connectivity

data CriticalPresentation : Set where
  threeSimultaneousSaddles : CriticalPresentation
  multiplicityThreeSingularity : CriticalPresentation
  oneOrdinarySaddle : CriticalPresentation

ordinarySaddleCount : CriticalPresentation → Nat
ordinarySaddleCount threeSimultaneousSaddles = 3
ordinarySaddleCount multiplicityThreeSingularity = 3
ordinarySaddleCount oneOrdinarySaddle = 1

data EulerCharacteristic : Set where
  negativeThree : EulerCharacteristic
  negativeOne : EulerCharacteristic

presentationEulerCharacteristic : CriticalPresentation → EulerCharacteristic
presentationEulerCharacteristic threeSimultaneousSaddles = negativeThree
presentationEulerCharacteristic multiplicityThreeSingularity = negativeThree
presentationEulerCharacteristic oneOrdinarySaddle = negativeOne

presentationConnectivity : CriticalPresentation → Connectivity
presentationConnectivity threeSimultaneousSaddles = connectedJunction
presentationConnectivity multiplicityThreeSingularity = connectedJunction
presentationConnectivity oneOrdinarySaddle = disconnectedPantsCylinder

connectedGenusZeroNeedsThreeSaddles :
  ordinarySaddleCount threeSimultaneousSaddles ≡ 3
connectedGenusZeroNeedsThreeSaddles = refl

oneSaddleIsPantsPlusCylinder :
  presentationConnectivity oneOrdinarySaddle ≡ disconnectedPantsCylinder
oneSaddleIsPantsPlusCylinder = refl

oneSaddleDoesNotHaveConnectedEulerCharacteristic :
  presentationEulerCharacteristic oneOrdinarySaddle ≡ negativeThree → ⊥
oneSaddleDoesNotHaveConnectedEulerCharacteristic ()

------------------------------------------------------------------------
-- A genuinely coupled finite ternary kernel.  Both outputs are functions of
-- the same three-input consensus, and the second output is its involutive
-- conjugate.  Mixed triples are sent to the neutral state.

consensus3 :
  Triadic.KernelTrit →
  Triadic.KernelTrit →
  Triadic.KernelTrit →
  Triadic.KernelTrit
consensus3 Triadic.negativeTrit Triadic.negativeTrit Triadic.negativeTrit =
  Triadic.negativeTrit
consensus3 Triadic.zeroTrit Triadic.zeroTrit Triadic.zeroTrit =
  Triadic.zeroTrit
consensus3 Triadic.positiveTrit Triadic.positiveTrit Triadic.positiveTrit =
  Triadic.positiveTrit
consensus3 _ _ _ = Triadic.zeroTrit

triToBiKernel :
  Triadic.KernelTrit →
  Triadic.KernelTrit →
  Triadic.KernelTrit →
  Triadic.NineSheet
triToBiKernel x y z =
  consensus3 x y z ,
  Triadic.negateTrit (consensus3 x y z)

negateInputTriple :
  (Triadic.KernelTrit × Triadic.KernelTrit) × Triadic.KernelTrit →
  (Triadic.KernelTrit × Triadic.KernelTrit) × Triadic.KernelTrit
negateInputTriple ((x , y) , z) =
  (Triadic.negateTrit x , Triadic.negateTrit y) ,
  Triadic.negateTrit z

kernelOnTriple :
  (Triadic.KernelTrit × Triadic.KernelTrit) × Triadic.KernelTrit →
  Triadic.NineSheet
kernelOnTriple ((x , y) , z) = triToBiKernel x y z

consensusNegationEquivariant :
  (x y z : Triadic.KernelTrit) →
  consensus3
    (Triadic.negateTrit x)
    (Triadic.negateTrit y)
    (Triadic.negateTrit z)
  ≡
  Triadic.negateTrit (consensus3 x y z)
consensusNegationEquivariant Triadic.negativeTrit Triadic.negativeTrit Triadic.negativeTrit = refl
consensusNegationEquivariant Triadic.negativeTrit Triadic.negativeTrit Triadic.zeroTrit = refl
consensusNegationEquivariant Triadic.negativeTrit Triadic.negativeTrit Triadic.positiveTrit = refl
consensusNegationEquivariant Triadic.negativeTrit Triadic.zeroTrit Triadic.negativeTrit = refl
consensusNegationEquivariant Triadic.negativeTrit Triadic.zeroTrit Triadic.zeroTrit = refl
consensusNegationEquivariant Triadic.negativeTrit Triadic.zeroTrit Triadic.positiveTrit = refl
consensusNegationEquivariant Triadic.negativeTrit Triadic.positiveTrit Triadic.negativeTrit = refl
consensusNegationEquivariant Triadic.negativeTrit Triadic.positiveTrit Triadic.zeroTrit = refl
consensusNegationEquivariant Triadic.negativeTrit Triadic.positiveTrit Triadic.positiveTrit = refl
consensusNegationEquivariant Triadic.zeroTrit Triadic.negativeTrit Triadic.negativeTrit = refl
consensusNegationEquivariant Triadic.zeroTrit Triadic.negativeTrit Triadic.zeroTrit = refl
consensusNegationEquivariant Triadic.zeroTrit Triadic.negativeTrit Triadic.positiveTrit = refl
consensusNegationEquivariant Triadic.zeroTrit Triadic.zeroTrit Triadic.negativeTrit = refl
consensusNegationEquivariant Triadic.zeroTrit Triadic.zeroTrit Triadic.zeroTrit = refl
consensusNegationEquivariant Triadic.zeroTrit Triadic.zeroTrit Triadic.positiveTrit = refl
consensusNegationEquivariant Triadic.zeroTrit Triadic.positiveTrit Triadic.negativeTrit = refl
consensusNegationEquivariant Triadic.zeroTrit Triadic.positiveTrit Triadic.zeroTrit = refl
consensusNegationEquivariant Triadic.zeroTrit Triadic.positiveTrit Triadic.positiveTrit = refl
consensusNegationEquivariant Triadic.positiveTrit Triadic.negativeTrit Triadic.negativeTrit = refl
consensusNegationEquivariant Triadic.positiveTrit Triadic.negativeTrit Triadic.zeroTrit = refl
consensusNegationEquivariant Triadic.positiveTrit Triadic.negativeTrit Triadic.positiveTrit = refl
consensusNegationEquivariant Triadic.positiveTrit Triadic.zeroTrit Triadic.negativeTrit = refl
consensusNegationEquivariant Triadic.positiveTrit Triadic.zeroTrit Triadic.zeroTrit = refl
consensusNegationEquivariant Triadic.positiveTrit Triadic.zeroTrit Triadic.positiveTrit = refl
consensusNegationEquivariant Triadic.positiveTrit Triadic.positiveTrit Triadic.negativeTrit = refl
consensusNegationEquivariant Triadic.positiveTrit Triadic.positiveTrit Triadic.zeroTrit = refl
consensusNegationEquivariant Triadic.positiveTrit Triadic.positiveTrit Triadic.positiveTrit = refl

triToBiKernelEquivariant :
  (x y z : Triadic.KernelTrit) →
  triToBiKernel
    (Triadic.negateTrit x)
    (Triadic.negateTrit y)
    (Triadic.negateTrit z)
  ≡
  Triadic.negateNine (triToBiKernel x y z)
triToBiKernelEquivariant Triadic.negativeTrit Triadic.negativeTrit Triadic.negativeTrit = refl
triToBiKernelEquivariant Triadic.negativeTrit Triadic.negativeTrit Triadic.zeroTrit = refl
triToBiKernelEquivariant Triadic.negativeTrit Triadic.negativeTrit Triadic.positiveTrit = refl
triToBiKernelEquivariant Triadic.negativeTrit Triadic.zeroTrit Triadic.negativeTrit = refl
triToBiKernelEquivariant Triadic.negativeTrit Triadic.zeroTrit Triadic.zeroTrit = refl
triToBiKernelEquivariant Triadic.negativeTrit Triadic.zeroTrit Triadic.positiveTrit = refl
triToBiKernelEquivariant Triadic.negativeTrit Triadic.positiveTrit Triadic.negativeTrit = refl
triToBiKernelEquivariant Triadic.negativeTrit Triadic.positiveTrit Triadic.zeroTrit = refl
triToBiKernelEquivariant Triadic.negativeTrit Triadic.positiveTrit Triadic.positiveTrit = refl
triToBiKernelEquivariant Triadic.zeroTrit Triadic.negativeTrit Triadic.negativeTrit = refl
triToBiKernelEquivariant Triadic.zeroTrit Triadic.negativeTrit Triadic.zeroTrit = refl
triToBiKernelEquivariant Triadic.zeroTrit Triadic.negativeTrit Triadic.positiveTrit = refl
triToBiKernelEquivariant Triadic.zeroTrit Triadic.zeroTrit Triadic.negativeTrit = refl
triToBiKernelEquivariant Triadic.zeroTrit Triadic.zeroTrit Triadic.zeroTrit = refl
triToBiKernelEquivariant Triadic.zeroTrit Triadic.zeroTrit Triadic.positiveTrit = refl
triToBiKernelEquivariant Triadic.zeroTrit Triadic.positiveTrit Triadic.negativeTrit = refl
triToBiKernelEquivariant Triadic.zeroTrit Triadic.positiveTrit Triadic.zeroTrit = refl
triToBiKernelEquivariant Triadic.zeroTrit Triadic.positiveTrit Triadic.positiveTrit = refl
triToBiKernelEquivariant Triadic.positiveTrit Triadic.negativeTrit Triadic.negativeTrit = refl
triToBiKernelEquivariant Triadic.positiveTrit Triadic.negativeTrit Triadic.zeroTrit = refl
triToBiKernelEquivariant Triadic.positiveTrit Triadic.negativeTrit Triadic.positiveTrit = refl
triToBiKernelEquivariant Triadic.positiveTrit Triadic.zeroTrit Triadic.negativeTrit = refl
triToBiKernelEquivariant Triadic.positiveTrit Triadic.zeroTrit Triadic.zeroTrit = refl
triToBiKernelEquivariant Triadic.positiveTrit Triadic.zeroTrit Triadic.positiveTrit = refl
triToBiKernelEquivariant Triadic.positiveTrit Triadic.positiveTrit Triadic.negativeTrit = refl
triToBiKernelEquivariant Triadic.positiveTrit Triadic.positiveTrit Triadic.zeroTrit = refl
triToBiKernelEquivariant Triadic.positiveTrit Triadic.positiveTrit Triadic.positiveTrit = refl

------------------------------------------------------------------------
-- Concrete dependence witnesses.  Holding two inputs negative and changing
-- any one input changes both outputs.  This rules out the declared
-- pants-plus-cylinder factorisation criterion for the canonical kernel.

firstInputChangesFirstOutput :
  proj₁
    (triToBiKernel
      Triadic.negativeTrit
      Triadic.negativeTrit
      Triadic.negativeTrit)
  ≡
  proj₁
    (triToBiKernel
      Triadic.zeroTrit
      Triadic.negativeTrit
      Triadic.negativeTrit)
  →
  ⊥
firstInputChangesFirstOutput ()

firstInputChangesSecondOutput :
  proj₂
    (triToBiKernel
      Triadic.negativeTrit
      Triadic.negativeTrit
      Triadic.negativeTrit)
  ≡
  proj₂
    (triToBiKernel
      Triadic.zeroTrit
      Triadic.negativeTrit
      Triadic.negativeTrit)
  →
  ⊥
firstInputChangesSecondOutput ()

secondInputChangesFirstOutput :
  proj₁
    (triToBiKernel
      Triadic.negativeTrit
      Triadic.negativeTrit
      Triadic.negativeTrit)
  ≡
  proj₁
    (triToBiKernel
      Triadic.negativeTrit
      Triadic.zeroTrit
      Triadic.negativeTrit)
  →
  ⊥
secondInputChangesFirstOutput ()

secondInputChangesSecondOutput :
  proj₂
    (triToBiKernel
      Triadic.negativeTrit
      Triadic.negativeTrit
      Triadic.negativeTrit)
  ≡
  proj₂
    (triToBiKernel
      Triadic.negativeTrit
      Triadic.zeroTrit
      Triadic.negativeTrit)
  →
  ⊥
secondInputChangesSecondOutput ()

thirdInputChangesFirstOutput :
  proj₁
    (triToBiKernel
      Triadic.negativeTrit
      Triadic.negativeTrit
      Triadic.negativeTrit)
  ≡
  proj₁
    (triToBiKernel
      Triadic.negativeTrit
      Triadic.negativeTrit
      Triadic.zeroTrit)
  →
  ⊥
thirdInputChangesFirstOutput ()

thirdInputChangesSecondOutput :
  proj₂
    (triToBiKernel
      Triadic.negativeTrit
      Triadic.negativeTrit
      Triadic.negativeTrit)
  ≡
  proj₂
    (triToBiKernel
      Triadic.negativeTrit
      Triadic.negativeTrit
      Triadic.zeroTrit)
  →
  ⊥
thirdInputChangesSecondOutput ()

record FullyCoupledWitness : Set where
  field
    firstToFirst : ⊤
    firstToSecond : ⊤
    secondToFirst : ⊤
    secondToSecond : ⊤
    thirdToFirst : ⊤
    thirdToSecond : ⊤

canonicalFullyCoupledWitness : FullyCoupledWitness
canonicalFullyCoupledWitness =
  record
    { firstToFirst = tt
    ; firstToSecond = tt
    ; secondToFirst = tt
    ; secondToSecond = tt
    ; thirdToFirst = tt
    ; thirdToSecond = tt
    }

record TriToBiSingularJunctionBoundary : Set where
  constructor triToBiSingularJunctionBoundary
  field
    connectedThreeToTwoIsOneOrdinaryPairOfPants : Bool
    connectedThreeToTwoIsOneOrdinaryPairOfPantsIsFalse :
      connectedThreeToTwoIsOneOrdinaryPairOfPants ≡ false

    oneMacroscopicStageMeansOneNondegenerateSaddle : Bool
    oneMacroscopicStageMeansOneNondegenerateSaddleIsFalse :
      oneMacroscopicStageMeansOneNondegenerateSaddle ≡ false

    finiteCarrierIsSmoothCobordismClassification : Bool
    finiteCarrierIsSmoothCobordismClassificationIsFalse :
      finiteCarrierIsSmoothCobordismClassification ≡ false

open TriToBiSingularJunctionBoundary public

canonicalTriToBiSingularJunctionBoundary :
  TriToBiSingularJunctionBoundary
canonicalTriToBiSingularJunctionBoundary =
  triToBiSingularJunctionBoundary false refl false refl false refl
