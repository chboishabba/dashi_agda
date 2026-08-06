module DASHI.Biology.TernaryCyclicDialecticExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicCarryResidualExact as Carry
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- Supplied sections 756--800, integrated against the existing exact cyclic
-- and carry-aware ternary arithmetic.  Algebra, logic, phase, dialectical
-- labels, and differentiable/probabilistic relaxations are separate carriers.

TriResidue : Set
TriResidue = Carry.TriResidue

cyclicAdd3 : TriResidue → TriResidue → TriResidue
cyclicAdd3 = Carry.cyclicAdd3

zeroResidue : TriResidue
zeroResidue = Carry.residue0

inverseResidue : TriResidue → TriResidue
inverseResidue Carry.residue0 = Carry.residue0
inverseResidue Carry.residue1 = Carry.residue2
inverseResidue Carry.residue2 = Carry.residue1

cyclicIdentityLeft :
  (a : TriResidue) → cyclicAdd3 zeroResidue a ≡ a
cyclicIdentityLeft Carry.residue0 = refl
cyclicIdentityLeft Carry.residue1 = refl
cyclicIdentityLeft Carry.residue2 = refl

cyclicIdentityRight :
  (a : TriResidue) → cyclicAdd3 a zeroResidue ≡ a
cyclicIdentityRight Carry.residue0 = refl
cyclicIdentityRight Carry.residue1 = refl
cyclicIdentityRight Carry.residue2 = refl

cyclicInverseRight :
  (a : TriResidue) → cyclicAdd3 a (inverseResidue a) ≡ zeroResidue
cyclicInverseRight Carry.residue0 = refl
cyclicInverseRight Carry.residue1 = refl
cyclicInverseRight Carry.residue2 = refl

nonzeroSelfCancellationFails :
  cyclicAdd3 Carry.residue1 Carry.residue1 ≡ Carry.residue0 → ⊥
nonzeroSelfCancellationFails ()

------------------------------------------------------------------------
-- Fixed-length carryless addition is coordinatewise cyclic addition.  This is
-- the exact ternary counterpart of bitwise XOR, not genuine 3-adic addition.

record ResidueWord2 : Set where
  constructor residueWord2
  field
    lowDigit : TriResidue
    highDigit : TriResidue

open ResidueWord2 public

carrylessAddWord2 : ResidueWord2 → ResidueWord2 → ResidueWord2
carrylessAddWord2 x y =
  residueWord2
    (cyclicAdd3 (lowDigit x) (lowDigit y))
    (cyclicAdd3 (highDigit x) (highDigit y))

carrylessSample :
  carrylessAddWord2
    (residueWord2 Carry.residue1 Carry.residue2)
    (residueWord2 Carry.residue2 Carry.residue2)
  ≡
  residueWord2 Carry.residue0 Carry.residue1
carrylessSample = refl

carryAwareOverflowDiffersFromCarrylessDigit :
  Carry.addCarry3
    Triadic.positiveTrit
    Triadic.positiveTrit
    Triadic.zeroTrit
  ≡
  (Triadic.negativeTrit , Triadic.positiveTrit)
carryAwareOverflowDiffersFromCarrylessDigit = Carry.positiveOverflowLifts

------------------------------------------------------------------------
-- Balanced ternary is an encoding of the same cyclic group.  The semantic
-- meaning of a residue is not part of that encoding.

balancedToResidue : Triadic.KernelTrit → TriResidue
balancedToResidue Triadic.negativeTrit = Carry.residue2
balancedToResidue Triadic.zeroTrit = Carry.residue0
balancedToResidue Triadic.positiveTrit = Carry.residue1

residueToBalanced : TriResidue → Triadic.KernelTrit
residueToBalanced Carry.residue0 = Triadic.zeroTrit
residueToBalanced Carry.residue1 = Triadic.positiveTrit
residueToBalanced Carry.residue2 = Triadic.negativeTrit

balancedRoundTrip :
  (a : Triadic.KernelTrit) →
  residueToBalanced (balancedToResidue a) ≡ a
balancedRoundTrip Triadic.negativeTrit = refl
balancedRoundTrip Triadic.zeroTrit = refl
balancedRoundTrip Triadic.positiveTrit = refl

balancedCyclicAdd :
  Triadic.KernelTrit → Triadic.KernelTrit → Triadic.KernelTrit
balancedCyclicAdd a b =
  residueToBalanced
    (cyclicAdd3 (balancedToResidue a) (balancedToResidue b))

positivePlusPositiveIsNegative :
  balancedCyclicAdd Triadic.positiveTrit Triadic.positiveTrit
  ≡
  Triadic.negativeTrit
positivePlusPositiveIsNegative = refl

------------------------------------------------------------------------
-- Dialectical labels are an external annotation.  The nontrivial group
-- automorphism swaps residue one and residue two, so their philosophical names
-- are not algebraically canonical.

data DialecticalLabel : Set where
  agreementLabel : DialecticalLabel
  oppositionLabel : DialecticalLabel
  sublationLabel : DialecticalLabel

labelResidue : TriResidue → DialecticalLabel
labelResidue Carry.residue0 = agreementLabel
labelResidue Carry.residue1 = oppositionLabel
labelResidue Carry.residue2 = sublationLabel

doubleAutomorphism : TriResidue → TriResidue
doubleAutomorphism Carry.residue0 = Carry.residue0
doubleAutomorphism Carry.residue1 = Carry.residue2
doubleAutomorphism Carry.residue2 = Carry.residue1

doubleAutomorphismPreservesAddition :
  (a b : TriResidue) →
  doubleAutomorphism (cyclicAdd3 a b)
  ≡
  cyclicAdd3 (doubleAutomorphism a) (doubleAutomorphism b)
doubleAutomorphismPreservesAddition Carry.residue0 Carry.residue0 = refl
doubleAutomorphismPreservesAddition Carry.residue0 Carry.residue1 = refl
doubleAutomorphismPreservesAddition Carry.residue0 Carry.residue2 = refl
doubleAutomorphismPreservesAddition Carry.residue1 Carry.residue0 = refl
doubleAutomorphismPreservesAddition Carry.residue1 Carry.residue1 = refl
doubleAutomorphismPreservesAddition Carry.residue1 Carry.residue2 = refl
doubleAutomorphismPreservesAddition Carry.residue2 Carry.residue0 = refl
doubleAutomorphismPreservesAddition Carry.residue2 Carry.residue1 = refl
doubleAutomorphismPreservesAddition Carry.residue2 Carry.residue2 = refl

automorphismSwapsDialecticalNames :
  labelResidue (doubleAutomorphism Carry.residue1)
  ≡
  sublationLabel
automorphismSwapsDialecticalNames = refl

oppositionCombinedWithOpposition :
  labelResidue (cyclicAdd3 Carry.residue1 Carry.residue1)
  ≡
  sublationLabel
oppositionCombinedWithOpposition = refl

sublationCombinedWithSublation :
  labelResidue (cyclicAdd3 Carry.residue2 Carry.residue2)
  ≡
  oppositionLabel
sublationCombinedWithSublation = refl

------------------------------------------------------------------------
-- Four-valued evidence is separate from the three residues.  In particular,
-- the value carrying both positive and negative evidence is not residue two by
-- definitional equality.

data EvidenceBit : Set where
  evidenceAbsent : EvidenceBit
  evidencePresent : EvidenceBit

record EvidencePair : Set where
  constructor evidencePair
  field
    positiveEvidence : EvidenceBit
    negativeEvidence : EvidenceBit

open EvidencePair public

trueOnlyEvidence : EvidencePair
trueOnlyEvidence = evidencePair evidencePresent evidenceAbsent

falseOnlyEvidence : EvidencePair
falseOnlyEvidence = evidencePair evidenceAbsent evidencePresent

bothEvidence : EvidencePair
bothEvidence = evidencePair evidencePresent evidencePresent

neitherEvidence : EvidencePair
neitherEvidence = evidencePair evidenceAbsent evidenceAbsent

bothAndNeitherRemainDistinct : bothEvidence ≡ neitherEvidence → ⊥
bothAndNeitherRemainDistinct ()

------------------------------------------------------------------------
-- The corrected priority-disjoint TEX candidate is explicitly different from
-- balanced cyclic addition and fails both commutativity and associativity.

tex : Triadic.KernelTrit → Triadic.KernelTrit → Triadic.KernelTrit
tex Triadic.negativeTrit Triadic.negativeTrit = Triadic.zeroTrit
tex Triadic.negativeTrit Triadic.zeroTrit = Triadic.zeroTrit
tex Triadic.negativeTrit Triadic.positiveTrit = Triadic.positiveTrit
tex Triadic.zeroTrit Triadic.negativeTrit = Triadic.negativeTrit
tex Triadic.zeroTrit Triadic.zeroTrit = Triadic.zeroTrit
tex Triadic.zeroTrit Triadic.positiveTrit = Triadic.positiveTrit
tex Triadic.positiveTrit Triadic.negativeTrit = Triadic.negativeTrit
tex Triadic.positiveTrit Triadic.zeroTrit = Triadic.zeroTrit
tex Triadic.positiveTrit Triadic.positiveTrit = Triadic.zeroTrit

texIsNotCyclicAddition :
  tex Triadic.positiveTrit Triadic.positiveTrit
  ≡
  balancedCyclicAdd Triadic.positiveTrit Triadic.positiveTrit
  →
  ⊥
texIsNotCyclicAddition ()

texIsNotCommutative :
  tex Triadic.negativeTrit Triadic.zeroTrit
  ≡
  tex Triadic.zeroTrit Triadic.negativeTrit
  →
  ⊥
texIsNotCommutative ()

texIsNotAssociative :
  tex
    (tex Triadic.negativeTrit Triadic.negativeTrit)
    Triadic.negativeTrit
  ≡
  tex
    Triadic.negativeTrit
    (tex Triadic.negativeTrit Triadic.negativeTrit)
  →
  ⊥
texIsNotAssociative ()

------------------------------------------------------------------------
-- Triadic truth and consequence metadata.  Cyclic phase is not conjunction,
-- disjunction, implication, or a proof of paraconsistency.

data TriTruth : Set where
  falseTruth : TriTruth
  neutralTruth : TriTruth
  trueTruth : TriTruth

negateTruth : TriTruth → TriTruth
negateTruth falseTruth = trueTruth
negateTruth neutralTruth = neutralTruth
negateTruth trueTruth = falseTruth

data Designation : Set where
  undesignated : Designation
  designated : Designation

designation : TriTruth → Designation
designation falseTruth = undesignated
designation neutralTruth = undesignated
designation trueTruth = designated

data TruthOrder : TriTruth → TriTruth → Set where
  falseBelowNeutral : TruthOrder falseTruth neutralTruth
  neutralBelowTrue : TruthOrder neutralTruth trueTruth
  falseBelowTrue : TruthOrder falseTruth trueTruth
  truthReflexive : (value : TriTruth) → TruthOrder value value

data CyclicPhase : Set where
  phase0 : CyclicPhase
  phase1 : CyclicPhase
  phase2 : CyclicPhase

advancePhase : CyclicPhase → CyclicPhase
advancePhase phase0 = phase1
advancePhase phase1 = phase2
advancePhase phase2 = phase0

phaseReturnsAfterThree :
  (phase : CyclicPhase) →
  advancePhase (advancePhase (advancePhase phase)) ≡ phase
phaseReturnsAfterThree phase0 = refl
phaseReturnsAfterThree phase1 = refl
phaseReturnsAfterThree phase2 = refl

------------------------------------------------------------------------
-- Existing cyclic convolution is the exact soft/probabilistic extension on
-- nonnegative masses.  One-hot exactness is inherited; a normalised sample
-- verifies probability-mass preservation without pretending Nat masses are
-- already arbitrary real simplex coordinates.

Mass3 : Set
Mass3 = Carry.Mass3

massTotal : Mass3 → Nat
massTotal mass =
  Carry.mass0 mass + Carry.mass1 mass + Carry.mass2 mass

softInputP : Mass3
softInputP = Carry.mass3 1 1 0

softInputQ : Mass3
softInputQ = Carry.mass3 1 0 1

softConvolutionSample :
  Carry.cyclicConvolution softInputP softInputQ
  ≡
  Carry.mass3 2 1 1
softConvolutionSample = refl

softConvolutionMassProductSample :
  massTotal (Carry.cyclicConvolution softInputP softInputQ)
  ≡
  massTotal softInputP * massTotal softInputQ
softConvolutionMassProductSample = refl

oneHotSoftExactness :
  (a b : TriResidue) →
  Carry.cyclicConvolution (Carry.basisMass a) (Carry.basisMass b)
  ≡
  Carry.basisMass (cyclicAdd3 a b)
oneHotSoftExactness = Carry.basisConvolutionExact

------------------------------------------------------------------------
-- Finite Fourier/phase character.  Multiplication of cube-root labels is
-- represented by the same three-element table and therefore transports cyclic
-- addition exactly in this finite shadow.

data RootPhase3 : Set where
  rootOne : RootPhase3
  rootOmega : RootPhase3
  rootOmegaSquared : RootPhase3

multiplyRoot : RootPhase3 → RootPhase3 → RootPhase3
multiplyRoot rootOne phase = phase
multiplyRoot rootOmega rootOne = rootOmega
multiplyRoot rootOmega rootOmega = rootOmegaSquared
multiplyRoot rootOmega rootOmegaSquared = rootOne
multiplyRoot rootOmegaSquared rootOne = rootOmegaSquared
multiplyRoot rootOmegaSquared rootOmega = rootOne
multiplyRoot rootOmegaSquared rootOmegaSquared = rootOmega

character : TriResidue → RootPhase3
character Carry.residue0 = rootOne
character Carry.residue1 = rootOmega
character Carry.residue2 = rootOmegaSquared

characterIsHomomorphism :
  (a b : TriResidue) →
  character (cyclicAdd3 a b)
  ≡
  multiplyRoot (character a) (character b)
characterIsHomomorphism Carry.residue0 Carry.residue0 = refl
characterIsHomomorphism Carry.residue0 Carry.residue1 = refl
characterIsHomomorphism Carry.residue0 Carry.residue2 = refl
characterIsHomomorphism Carry.residue1 Carry.residue0 = refl
characterIsHomomorphism Carry.residue1 Carry.residue1 = refl
characterIsHomomorphism Carry.residue1 Carry.residue2 = refl
characterIsHomomorphism Carry.residue2 Carry.residue0 = refl
characterIsHomomorphism Carry.residue2 Carry.residue1 = refl
characterIsHomomorphism Carry.residue2 Carry.residue2 = refl

------------------------------------------------------------------------
-- Geometry and solver architecture remain typed.  The same word carrier can
-- carry Hamming, prefix, or finite 3-adic observations, but none is forced by
-- the alphabet alone.

data WordGeometry : Set where
  hammingGeometry : WordGeometry
  prefixUltrametricGeometry : WordGeometry
  finiteThreeAdicGeometry : WordGeometry

data SolverLayer : Set where
  hardCyclicLayer : SolverLayer
  softConvolutionLayer : SolverLayer
  carryAwareLayer : SolverLayer
  recursiveDepthLayer : SolverLayer

data DifferentialNotion : Set where
  finiteDifference : DifferentialNotion
  realRelaxationJacobian : DifferentialNotion
  threeAdicDerivative : DifferentialNotion

record CarryTransitionAnnotation : Set where
  constructor carryTransitionAnnotation
  field
    localDigit : Triadic.KernelTrit
    outgoingCarry : Triadic.KernelTrit
    semanticLabel : DialecticalLabel

open CarryTransitionAnnotation public

positiveOverflowAnnotation : CarryTransitionAnnotation
positiveOverflowAnnotation =
  carryTransitionAnnotation
    Triadic.negativeTrit
    Triadic.positiveTrit
    sublationLabel

annotationRetainsResidual :
  outgoingCarry positiveOverflowAnnotation ≡ Triadic.positiveTrit
annotationRetainsResidual = refl

record TernaryCyclicDialecticBoundary : Set where
  constructor ternaryCyclicDialecticBoundary
  field
    ternaryCyclicAdditionIsBooleanXORWithAllLaws : Bool
    ternaryCyclicAdditionIsBooleanXORWithAllLawsIsFalse :
      ternaryCyclicAdditionIsBooleanXORWithAllLaws ≡ false

    residueTwoIntrinsicallyMeansBothTrue : Bool
    residueTwoIntrinsicallyMeansBothTrueIsFalse :
      residueTwoIntrinsicallyMeansBothTrue ≡ false

    texIsEquivalentToCyclicAddition : Bool
    texIsEquivalentToCyclicAdditionIsFalse :
      texIsEquivalentToCyclicAddition ≡ false

    modularAdditionIsIntrinsicallyNonlinear : Bool
    modularAdditionIsIntrinsicallyNonlinearIsFalse :
      modularAdditionIsIntrinsicallyNonlinear ≡ false

    carrylessAdditionIsThreeAdicAddition : Bool
    carrylessAdditionIsThreeAdicAdditionIsFalse :
      carrylessAdditionIsThreeAdicAddition ≡ false

    realModuloTanhIsCertifiedSoftCyclicAddition : Bool
    realModuloTanhIsCertifiedSoftCyclicAdditionIsFalse :
      realModuloTanhIsCertifiedSoftCyclicAddition ≡ false

    cyclicAdditionAloneProvesParaconsistency : Bool
    cyclicAdditionAloneProvesParaconsistencyIsFalse :
      cyclicAdditionAloneProvesParaconsistency ≡ false

open TernaryCyclicDialecticBoundary public

canonicalTernaryCyclicDialecticBoundary :
  TernaryCyclicDialecticBoundary
canonicalTernaryCyclicDialecticBoundary =
  ternaryCyclicDialecticBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
