module DASHI.Biology.TernarySoftCarryLogicExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TernaryCyclicDialecticExact as Cyclic
import DASHI.Biology.TriadicCarryResidualExact as Carry
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- Finite exact completion of sections 774--793 and 797--799: consequence
-- specifications, soft carry distributions, depth recursion, and finite-prefix
-- continuity.  No chosen three-valued logic is identified with cyclic addition.

data Formula2 : Set where
  propositionP : Formula2
  propositionQ : Formula2

record Valuation2 : Set where
  constructor valuation2
  field
    valueP : Cyclic.TriTruth
    valueQ : Cyclic.TriTruth

open Valuation2 public

data DesignationScheme : Set where
  trueOnlyScheme : DesignationScheme
  neutralOrTrueScheme : DesignationScheme

isDesignated : DesignationScheme → Cyclic.TriTruth → Bool
isDesignated trueOnlyScheme Cyclic.falseTruth = false
isDesignated trueOnlyScheme Cyclic.neutralTruth = false
isDesignated trueOnlyScheme Cyclic.trueTruth = true
isDesignated neutralOrTrueScheme Cyclic.falseTruth = false
isDesignated neutralOrTrueScheme Cyclic.neutralTruth = true
isDesignated neutralOrTrueScheme Cyclic.trueTruth = true

formulaValue : Valuation2 → Formula2 → Cyclic.TriTruth
formulaValue valuation propositionP = valueP valuation
formulaValue valuation propositionQ = valueQ valuation

onePremiseConsequence :
  DesignationScheme → Valuation2 → Formula2 → Formula2 → Bool
onePremiseConsequence scheme valuation premise conclusion
  with isDesignated scheme (formulaValue valuation premise)
... | false = true
... | true = isDesignated scheme (formulaValue valuation conclusion)

schemeSensitiveValuation : Valuation2
schemeSensitiveValuation =
  valuation2 Cyclic.neutralTruth Cyclic.falseTruth

trueOnlyConsequenceIsVacuous :
  onePremiseConsequence
    trueOnlyScheme
    schemeSensitiveValuation
    propositionP
    propositionQ
  ≡
  true
trueOnlyConsequenceIsVacuous = refl

neutralDesignatedConsequenceFails :
  onePremiseConsequence
    neutralOrTrueScheme
    schemeSensitiveValuation
    propositionP
    propositionQ
  ≡
  false
neutralDesignatedConsequenceFails = refl

------------------------------------------------------------------------
-- A logic specification owns operations and designation separately from the
-- cyclic group law.

record TriLogicSpecification : Set where
  constructor triLogicSpecification
  field
    negation : Cyclic.TriTruth → Cyclic.TriTruth
    conjunction : Cyclic.TriTruth → Cyclic.TriTruth → Cyclic.TriTruth
    disjunction : Cyclic.TriTruth → Cyclic.TriTruth → Cyclic.TriTruth
    implication : Cyclic.TriTruth → Cyclic.TriTruth → Cyclic.TriTruth
    designationScheme : DesignationScheme

open TriLogicSpecification public

minimumTruth : Cyclic.TriTruth → Cyclic.TriTruth → Cyclic.TriTruth
minimumTruth Cyclic.falseTruth _ = Cyclic.falseTruth
minimumTruth Cyclic.neutralTruth Cyclic.falseTruth = Cyclic.falseTruth
minimumTruth Cyclic.neutralTruth _ = Cyclic.neutralTruth
minimumTruth Cyclic.trueTruth value = value

maximumTruth : Cyclic.TriTruth → Cyclic.TriTruth → Cyclic.TriTruth
maximumTruth Cyclic.trueTruth _ = Cyclic.trueTruth
maximumTruth Cyclic.neutralTruth Cyclic.trueTruth = Cyclic.trueTruth
maximumTruth Cyclic.neutralTruth _ = Cyclic.neutralTruth
maximumTruth Cyclic.falseTruth value = value

orderedImplication : Cyclic.TriTruth → Cyclic.TriTruth → Cyclic.TriTruth
orderedImplication Cyclic.falseTruth _ = Cyclic.trueTruth
orderedImplication Cyclic.neutralTruth Cyclic.falseTruth = Cyclic.neutralTruth
orderedImplication Cyclic.neutralTruth Cyclic.neutralTruth = Cyclic.trueTruth
orderedImplication Cyclic.neutralTruth Cyclic.trueTruth = Cyclic.trueTruth
orderedImplication Cyclic.trueTruth value = value

canonicalOrderedLogic : TriLogicSpecification
canonicalOrderedLogic =
  triLogicSpecification
    Cyclic.negateTruth
    minimumTruth
    maximumTruth
    orderedImplication
    trueOnlyScheme

cyclicAdditionIsNotDeclaredConjunction :
  conjunction canonicalOrderedLogic
    Cyclic.trueTruth
    Cyclic.trueTruth
  ≡
  Cyclic.trueTruth
cyclicAdditionIsNotDeclaredConjunction = refl

------------------------------------------------------------------------
-- Nine output bins for digit/carry pairs.  This is the finite transition
-- tensor codomain for a probabilistic carry-aware layer.

record CarryPairMass9 : Set where
  constructor carryPairMass9
  field
    nnMass : Nat
    nzMass : Nat
    npMass : Nat
    znMass : Nat
    zzMass : Nat
    zpMass : Nat
    pnMass : Nat
    pzMass : Nat
    ppMass : Nat

open CarryPairMass9 public

carryPairMassTotal : CarryPairMass9 → Nat
carryPairMassTotal mass =
  nnMass mass + nzMass mass + npMass mass
  + znMass mass + zzMass mass + zpMass mass
  + pnMass mass + pzMass mass + ppMass mass

basisCarryPair :
  Triadic.KernelTrit × Triadic.KernelTrit → CarryPairMass9
basisCarryPair (Triadic.negativeTrit , Triadic.negativeTrit) =
  carryPairMass9 1 0 0 0 0 0 0 0 0
basisCarryPair (Triadic.negativeTrit , Triadic.zeroTrit) =
  carryPairMass9 0 1 0 0 0 0 0 0 0
basisCarryPair (Triadic.negativeTrit , Triadic.positiveTrit) =
  carryPairMass9 0 0 1 0 0 0 0 0 0
basisCarryPair (Triadic.zeroTrit , Triadic.negativeTrit) =
  carryPairMass9 0 0 0 1 0 0 0 0 0
basisCarryPair (Triadic.zeroTrit , Triadic.zeroTrit) =
  carryPairMass9 0 0 0 0 1 0 0 0 0
basisCarryPair (Triadic.zeroTrit , Triadic.positiveTrit) =
  carryPairMass9 0 0 0 0 0 1 0 0 0
basisCarryPair (Triadic.positiveTrit , Triadic.negativeTrit) =
  carryPairMass9 0 0 0 0 0 0 1 0 0
basisCarryPair (Triadic.positiveTrit , Triadic.zeroTrit) =
  carryPairMass9 0 0 0 0 0 0 0 1 0
basisCarryPair (Triadic.positiveTrit , Triadic.positiveTrit) =
  carryPairMass9 0 0 0 0 0 0 0 0 1

basisCarryPairHasUnitMass :
  (output : Triadic.KernelTrit × Triadic.KernelTrit) →
  carryPairMassTotal (basisCarryPair output) ≡ 1
basisCarryPairHasUnitMass (Triadic.negativeTrit , Triadic.negativeTrit) = refl
basisCarryPairHasUnitMass (Triadic.negativeTrit , Triadic.zeroTrit) = refl
basisCarryPairHasUnitMass (Triadic.negativeTrit , Triadic.positiveTrit) = refl
basisCarryPairHasUnitMass (Triadic.zeroTrit , Triadic.negativeTrit) = refl
basisCarryPairHasUnitMass (Triadic.zeroTrit , Triadic.zeroTrit) = refl
basisCarryPairHasUnitMass (Triadic.zeroTrit , Triadic.positiveTrit) = refl
basisCarryPairHasUnitMass (Triadic.positiveTrit , Triadic.negativeTrit) = refl
basisCarryPairHasUnitMass (Triadic.positiveTrit , Triadic.zeroTrit) = refl
basisCarryPairHasUnitMass (Triadic.positiveTrit , Triadic.positiveTrit) = refl

hardCarryAsSoftOneHot :
  Triadic.KernelTrit →
  Triadic.KernelTrit →
  Triadic.KernelTrit →
  CarryPairMass9
hardCarryAsSoftOneHot x y carry =
  basisCarryPair (Carry.addCarry3 x y carry)

positiveOverflowSoftOutput :
  hardCarryAsSoftOneHot
    Triadic.positiveTrit
    Triadic.positiveTrit
    Triadic.zeroTrit
  ≡
  carryPairMass9 0 0 1 0 0 0 0 0 0
positiveOverflowSoftOutput = refl

hardCarrySoftOutputHasUnitMass :
  (x y carry : Triadic.KernelTrit) →
  carryPairMassTotal (hardCarryAsSoftOneHot x y carry) ≡ 1
hardCarrySoftOutputHasUnitMass x y carry =
  basisCarryPairHasUnitMass (Carry.addCarry3 x y carry)

scaleCarryMass : Nat → CarryPairMass9 → CarryPairMass9
scaleCarryMass scalar mass =
  carryPairMass9
    (scalar * nnMass mass)
    (scalar * nzMass mass)
    (scalar * npMass mass)
    (scalar * znMass mass)
    (scalar * zzMass mass)
    (scalar * zpMass mass)
    (scalar * pnMass mass)
    (scalar * pzMass mass)
    (scalar * ppMass mass)

addCarryMass : CarryPairMass9 → CarryPairMass9 → CarryPairMass9
addCarryMass left right =
  carryPairMass9
    (nnMass left + nnMass right)
    (nzMass left + nzMass right)
    (npMass left + npMass right)
    (znMass left + znMass right)
    (zzMass left + zzMass right)
    (zpMass left + zpMass right)
    (pnMass left + pnMass right)
    (pzMass left + pzMass right)
    (ppMass left + ppMass right)

canonicalUncertainCarryOutput : CarryPairMass9
canonicalUncertainCarryOutput =
  addCarryMass
    (scaleCarryMass 2
      (hardCarryAsSoftOneHot
        Triadic.positiveTrit
        Triadic.positiveTrit
        Triadic.zeroTrit))
    (scaleCarryMass 1
      (hardCarryAsSoftOneHot
        Triadic.negativeTrit
        Triadic.positiveTrit
        Triadic.zeroTrit))

canonicalUncertainCarryMassIsThree :
  carryPairMassTotal canonicalUncertainCarryOutput ≡ 3
canonicalUncertainCarryMassIsThree = refl

------------------------------------------------------------------------
-- Depth recursion exposes the carry distribution as recurrent hidden state.

data DigitDepth : Set where
  depth0 : DigitDepth
  depth1 : DigitDepth
  depth2 : DigitDepth

record SoftDepthState : Set where
  constructor softDepthState
  field
    currentDepth : DigitDepth
    currentCarryMass : Carry.Mass3

open SoftDepthState public

initialSoftDepthState : SoftDepthState
initialSoftDepthState =
  softDepthState depth0 (Carry.basisMass Carry.residue0)

advanceSoftDepth : SoftDepthState → SoftDepthState
advanceSoftDepth (softDepthState depth0 carryMass) =
  softDepthState depth1 carryMass
advanceSoftDepth (softDepthState depth1 carryMass) =
  softDepthState depth2 carryMass
advanceSoftDepth (softDepthState depth2 carryMass) =
  softDepthState depth2 carryMass

softDepthReachesTwo :
  currentDepth
    (advanceSoftDepth (advanceSoftDepth initialSoftDepthState))
  ≡
  depth2
softDepthReachesTwo = refl

------------------------------------------------------------------------
-- Finite-prefix continuity: matching low digits and incoming carries produce
-- matching resolved low digits.  This is the exact finite shadow of native
-- 3-adic continuity, not a real-coordinate continuity statement.

carrylessLowCompatibility :
  (x x' y y' : Cyclic.ResidueWord2) →
  Cyclic.lowDigit x ≡ Cyclic.lowDigit x' →
  Cyclic.lowDigit y ≡ Cyclic.lowDigit y' →
  Cyclic.lowDigit (Cyclic.carrylessAddWord2 x y)
  ≡
  Cyclic.lowDigit (Cyclic.carrylessAddWord2 x' y')
carrylessLowCompatibility x x' y y' refl refl = refl

carryOutputCompatibility :
  (x x' y y' carry carry' : Triadic.KernelTrit) →
  x ≡ x' →
  y ≡ y' →
  carry ≡ carry' →
  Carry.addCarry3 x y carry
  ≡
  Carry.addCarry3 x' y' carry'
carryOutputCompatibility x x' y y' carry carry' refl refl refl = refl

------------------------------------------------------------------------
-- Temperature and phase relaxations remain declared approximation families.

data TemperatureRegime : Set where
  highTemperatureSoft : TemperatureRegime
  finiteTemperatureSoft : TemperatureRegime
  zeroTemperatureHardLimit : TemperatureRegime

data RelaxationFamily : Set where
  cyclicSimplexConvolution : RelaxationFamily
  cubeRootPhaseMultiplication : RelaxationFamily
  sineCosineEmbedding : RelaxationFamily
  malformedRealModuloTanh : RelaxationFamily

relaxationCertified : RelaxationFamily → Bool
relaxationCertified cyclicSimplexConvolution = true
relaxationCertified cubeRootPhaseMultiplication = true
relaxationCertified sineCosineEmbedding = true
relaxationCertified malformedRealModuloTanh = false

malformedRelaxationRejected :
  relaxationCertified malformedRealModuloTanh ≡ false
malformedRelaxationRejected = refl

record TernarySoftCarryLogicBoundary : Set where
  constructor ternarySoftCarryLogicBoundary
  field
    designationChoiceIsDeterminedByResidueGroup : Bool
    designationChoiceIsDeterminedByResidueGroupIsFalse :
      designationChoiceIsDeterminedByResidueGroup ≡ false

    cyclicAdditionDefinesLogicalConsequence : Bool
    cyclicAdditionDefinesLogicalConsequenceIsFalse :
      cyclicAdditionDefinesLogicalConsequence ≡ false

    softCarryCanDiscardOutgoingCarryState : Bool
    softCarryCanDiscardOutgoingCarryStateIsFalse :
      softCarryCanDiscardOutgoingCarryState ≡ false

    realEmbeddingDiscontinuityIsNativeThreeAdicDiscontinuity : Bool
    realEmbeddingDiscontinuityIsNativeThreeAdicDiscontinuityIsFalse :
      realEmbeddingDiscontinuityIsNativeThreeAdicDiscontinuity ≡ false

open TernarySoftCarryLogicBoundary public

canonicalTernarySoftCarryLogicBoundary : TernarySoftCarryLogicBoundary
canonicalTernarySoftCarryLogicBoundary =
  ternarySoftCarryLogicBoundary false refl false refl false refl false refl
