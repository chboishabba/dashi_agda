module DASHI.Physics.Foundations.FiniteMultiscaleKernelCompatibilityExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Fine and coarse carriers with an explicit projection.

data FineState : Set where
  fineLeftLow : FineState
  fineLeftHigh : FineState
  fineRightLow : FineState
  fineRightHigh : FineState

data CoarseState : Set where
  coarseLeft : CoarseState
  coarseRight : CoarseState

coarseProjection : FineState → CoarseState
coarseProjection fineLeftLow = coarseLeft
coarseProjection fineLeftHigh = coarseLeft
coarseProjection fineRightLow = coarseRight
coarseProjection fineRightHigh = coarseRight

------------------------------------------------------------------------
-- Exact commuting kernel pair.  Fine dynamics changes hidden resolution while
-- preserving the coarse class; coarse dynamics is the identity.

fineKernelExact : FineState → FineState
fineKernelExact fineLeftLow = fineLeftHigh
fineKernelExact fineLeftHigh = fineLeftLow
fineKernelExact fineRightLow = fineRightHigh
fineKernelExact fineRightHigh = fineRightLow

coarseKernelExact : CoarseState → CoarseState
coarseKernelExact coarseLeft = coarseLeft
coarseKernelExact coarseRight = coarseRight

exactKernelCompatibility :
  (state : FineState) →
  coarseProjection (fineKernelExact state)
  ≡
  coarseKernelExact (coarseProjection state)
exactKernelCompatibility fineLeftLow = refl
exactKernelCompatibility fineLeftHigh = refl
exactKernelCompatibility fineRightLow = refl
exactKernelCompatibility fineRightHigh = refl

------------------------------------------------------------------------
-- An incompatible fine kernel crosses the coarse partition at one state.

fineKernelDefective : FineState → FineState
fineKernelDefective fineLeftLow = fineRightLow
fineKernelDefective fineLeftHigh = fineLeftLow
fineKernelDefective fineRightLow = fineRightHigh
fineKernelDefective fineRightHigh = fineRightLow

coarseMismatch : CoarseState → CoarseState → Nat
coarseMismatch coarseLeft coarseLeft = 0
coarseMismatch coarseLeft coarseRight = 1
coarseMismatch coarseRight coarseLeft = 1
coarseMismatch coarseRight coarseRight = 0

compatibilityDefect : FineState → Nat
compatibilityDefect state =
  coarseMismatch
    (coarseProjection (fineKernelDefective state))
    (coarseKernelExact (coarseProjection state))

canonicalDefectIsOne : compatibilityDefect fineLeftLow ≡ 1
canonicalDefectIsOne = refl

otherLeftFineStateHasZeroDefect : compatibilityDefect fineLeftHigh ≡ 0
otherLeftFineStateHasZeroDefect = refl

------------------------------------------------------------------------
-- Quotient-valued compatibility: a representative may change while its orbit
-- label is preserved.

data FineRepresentative : Set where
  leftRepresentativeA : FineRepresentative
  leftRepresentativeB : FineRepresentative
  rightRepresentativeA : FineRepresentative
  rightRepresentativeB : FineRepresentative

data OrbitLabel : Set where
  leftOrbit : OrbitLabel
  rightOrbit : OrbitLabel

orbitProjection : FineRepresentative → OrbitLabel
orbitProjection leftRepresentativeA = leftOrbit
orbitProjection leftRepresentativeB = leftOrbit
orbitProjection rightRepresentativeA = rightOrbit
orbitProjection rightRepresentativeB = rightOrbit

representativeKernel : FineRepresentative → FineRepresentative
representativeKernel leftRepresentativeA = leftRepresentativeB
representativeKernel leftRepresentativeB = leftRepresentativeA
representativeKernel rightRepresentativeA = rightRepresentativeB
representativeKernel rightRepresentativeB = rightRepresentativeA

orbitKernel : OrbitLabel → OrbitLabel
orbitKernel leftOrbit = leftOrbit
orbitKernel rightOrbit = rightOrbit

quotientValuedCompatibility :
  (representative : FineRepresentative) →
  orbitProjection (representativeKernel representative)
  ≡
  orbitKernel (orbitProjection representative)
quotientValuedCompatibility leftRepresentativeA = refl
quotientValuedCompatibility leftRepresentativeB = refl
quotientValuedCompatibility rightRepresentativeA = refl
quotientValuedCompatibility rightRepresentativeB = refl

------------------------------------------------------------------------
-- Kernel fibres are explicit preimages of one output.

data KernelOutput : Set where
  outputZero : KernelOutput
  outputOne : KernelOutput

finiteKernel : FineState → KernelOutput
finiteKernel fineLeftLow = outputZero
finiteKernel fineLeftHigh = outputZero
finiteKernel fineRightLow = outputOne
finiteKernel fineRightHigh = outputOne

sameKernelFibreWitness :
  finiteKernel fineLeftLow ≡ finiteKernel fineLeftHigh
sameKernelFibreWitness = refl

record FiniteMultiscaleKernelCompatibilityBoundary : Set where
  constructor finiteMultiscaleKernelCompatibilityBoundary
  field
    coarseGrainingAlwaysCommutesWithDynamics : Bool
    coarseGrainingAlwaysCommutesWithDynamicsIsFalse :
      coarseGrainingAlwaysCommutesWithDynamics ≡ false

    approximateCompatibilityIsExactEquality : Bool
    approximateCompatibilityIsExactEqualityIsFalse :
      approximateCompatibilityIsExactEquality ≡ false

    quotientCompatibilityPreservesRepresentatives : Bool
    quotientCompatibilityPreservesRepresentativesIsFalse :
      quotientCompatibilityPreservesRepresentatives ≡ false

    sameKernelOutputMeansSameMicroscopicState : Bool
    sameKernelOutputMeansSameMicroscopicStateIsFalse :
      sameKernelOutputMeansSameMicroscopicState ≡ false

open FiniteMultiscaleKernelCompatibilityBoundary public

canonicalFiniteMultiscaleKernelCompatibilityBoundary :
  FiniteMultiscaleKernelCompatibilityBoundary
canonicalFiniteMultiscaleKernelCompatibilityBoundary =
  finiteMultiscaleKernelCompatibilityBoundary
    false refl
    false refl
    false refl
    false refl
