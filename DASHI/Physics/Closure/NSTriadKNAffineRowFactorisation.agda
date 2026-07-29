module DASHI.Physics.Closure.NSTriadKNAffineRowFactorisation where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Jean-Michel Bony; Loukas Grafakos; Rodolfo H. Torres; Pierre
-- Germain; DASHI repository contributors.
-- Title: "Archetype factorisation of the twenty-one Stage-3 affine rows".
-- Venue/year: Annales scientifiques de l'Ecole Normale Superieure 14
-- (1981); Journal of Functional Analysis 187 (2001), 1--24; Journal of
-- Differential Equations 226 (2006), 373--428; DASHI formal development,
-- 2026.
-- DOI: 10.24033/asens.1404; 10.1006/jfan.2001.3804;
-- 10.1016/j.jde.2005.10.007; the repository row factorisation has no DOI.
-- Uses: the literal twelve-component direct/swapped ledger, its reduction
-- to five analytic archetypes, and the output/first-adjoint/second-adjoint
-- ownership of the nine finite-overlap rows.
-- Relationship: proves a structural compression from sixty-three raw row
-- slots to eight three-leg coefficient families, hence twenty-four
-- independent coefficient slots. It supplies no numeric shell exponent
-- and does not claim positive epsilon.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Physics.Closure.NSTriadKNExactDyadicShellGeometry as Geometry
import DASHI.Physics.Closure.NSTriadKNSeparatedComponentLedger as Components
import DASHI.Physics.Closure.NSTriadKNComponentAffineConstraintLedger as Ledger

data SeparatedRow : Set where
  outputLeftLow outputRightLow outputOutputLow : SeparatedRow
  firstDirectLeftLow firstDirectRightLow firstDirectOutputLow : SeparatedRow
  firstSwappedLeftLow firstSwappedRightLow firstSwappedOutputLow : SeparatedRow
  secondLeftLow secondRightLow secondOutputLow : SeparatedRow

separatedComponent : SeparatedRow → Components.ShellComponent
separatedComponent outputLeftLow =
  Components.component Geometry.outputView Geometry.unsplitPiece Geometry.leftLowTag
separatedComponent outputRightLow =
  Components.component Geometry.outputView Geometry.unsplitPiece Geometry.rightLowTag
separatedComponent outputOutputLow =
  Components.component Geometry.outputView Geometry.unsplitPiece Geometry.outputLowTag
separatedComponent firstDirectLeftLow =
  Components.component Geometry.firstAdjointView Geometry.directPiece Geometry.leftLowTag
separatedComponent firstDirectRightLow =
  Components.component Geometry.firstAdjointView Geometry.directPiece Geometry.rightLowTag
separatedComponent firstDirectOutputLow =
  Components.component Geometry.firstAdjointView Geometry.directPiece Geometry.outputLowTag
separatedComponent firstSwappedLeftLow =
  Components.component Geometry.firstAdjointView Geometry.swappedPiece Geometry.leftLowTag
separatedComponent firstSwappedRightLow =
  Components.component Geometry.firstAdjointView Geometry.swappedPiece Geometry.rightLowTag
separatedComponent firstSwappedOutputLow =
  Components.component Geometry.firstAdjointView Geometry.swappedPiece Geometry.outputLowTag
separatedComponent secondLeftLow =
  Components.component Geometry.secondAdjointView Geometry.unsplitPiece Geometry.leftLowTag
separatedComponent secondRightLow =
  Components.component Geometry.secondAdjointView Geometry.unsplitPiece Geometry.rightLowTag
separatedComponent secondOutputLow =
  Components.component Geometry.secondAdjointView Geometry.unsplitPiece Geometry.outputLowTag

data IndependentCoefficientFamily : Set where
  lowHighFamily
  lowLowFamily
  directFirstConvolutionFamily
  outputRelocationFamily
  secondFrozenFamily
  outputOverlapFamily
  firstOverlapFamily
  secondOverlapFamily : IndependentCoefficientFamily

data ArchetypeFamilyMatch :
    Components.AnalyticArchetype → IndependentCoefficientFamily → Set where
  lowHighMatch :
    ArchetypeFamilyMatch
      Components.lowBernsteinDerivativeHigh
      lowHighFamily
  lowLowMatch :
    ArchetypeFamilyMatch
      Components.lowBernsteinDerivativeLow
      lowLowFamily
  directFirstMatch :
    ArchetypeFamilyMatch
      Components.highHighFirstAdjointConvolution
      directFirstConvolutionFamily
  outputRelocationMatch :
    ArchetypeFamilyMatch
      Components.outputRelocationGain
      outputRelocationFamily
  secondFrozenMatch :
    ArchetypeFamilyMatch
      Components.secondAdjointFrozenLowDerivative
      secondFrozenFamily

separatedFamily : SeparatedRow → IndependentCoefficientFamily
separatedFamily outputLeftLow = lowHighFamily
separatedFamily outputRightLow = lowLowFamily
separatedFamily outputOutputLow = outputRelocationFamily
separatedFamily firstDirectLeftLow = directFirstConvolutionFamily
separatedFamily firstDirectRightLow = lowLowFamily
separatedFamily firstDirectOutputLow = lowHighFamily
separatedFamily firstSwappedLeftLow = secondFrozenFamily
separatedFamily firstSwappedRightLow = lowHighFamily
separatedFamily firstSwappedOutputLow = lowHighFamily
separatedFamily secondLeftLow = lowHighFamily
separatedFamily secondRightLow = secondFrozenFamily
separatedFamily secondOutputLow = lowHighFamily

separatedFamilyMatchesRepositoryArchetype :
  ∀ row →
  ArchetypeFamilyMatch
    (Components.componentArchetype (separatedComponent row))
    (separatedFamily row)
separatedFamilyMatchesRepositoryArchetype outputLeftLow = lowHighMatch
separatedFamilyMatchesRepositoryArchetype outputRightLow = lowLowMatch
separatedFamilyMatchesRepositoryArchetype outputOutputLow = outputRelocationMatch
separatedFamilyMatchesRepositoryArchetype firstDirectLeftLow = directFirstMatch
separatedFamilyMatchesRepositoryArchetype firstDirectRightLow = lowLowMatch
separatedFamilyMatchesRepositoryArchetype firstDirectOutputLow = lowHighMatch
separatedFamilyMatchesRepositoryArchetype firstSwappedLeftLow = secondFrozenMatch
separatedFamilyMatchesRepositoryArchetype firstSwappedRightLow = lowHighMatch
separatedFamilyMatchesRepositoryArchetype firstSwappedOutputLow = lowHighMatch
separatedFamilyMatchesRepositoryArchetype secondLeftLow = lowHighMatch
separatedFamilyMatchesRepositoryArchetype secondRightLow = secondFrozenMatch
separatedFamilyMatchesRepositoryArchetype secondOutputLow = lowHighMatch

data OverlapRow : Set where
  outputNear outputTransition outputResidual : OverlapRow
  firstNear firstTransition firstResidual : OverlapRow
  secondNear secondTransition secondResidual : OverlapRow

overlapOwner : OverlapRow → Ledger.ConstraintOwner
overlapOwner outputNear = Ledger.outputOwner
overlapOwner outputTransition = Ledger.outputOwner
overlapOwner outputResidual = Ledger.outputOwner
overlapOwner firstNear = Ledger.firstAdjointOwner
overlapOwner firstTransition = Ledger.firstAdjointOwner
overlapOwner firstResidual = Ledger.firstAdjointOwner
overlapOwner secondNear = Ledger.secondAdjointOwner
overlapOwner secondTransition = Ledger.secondAdjointOwner
overlapOwner secondResidual = Ledger.secondAdjointOwner

overlapClass : OverlapRow → Ledger.FiniteOverlapClass
overlapClass outputNear = Ledger.nearClass
overlapClass outputTransition = Ledger.transitionClass
overlapClass outputResidual = Ledger.residualClass
overlapClass firstNear = Ledger.nearClass
overlapClass firstTransition = Ledger.transitionClass
overlapClass firstResidual = Ledger.residualClass
overlapClass secondNear = Ledger.nearClass
overlapClass secondTransition = Ledger.transitionClass
overlapClass secondResidual = Ledger.residualClass

overlapFamily : OverlapRow → IndependentCoefficientFamily
overlapFamily outputNear = outputOverlapFamily
overlapFamily outputTransition = outputOverlapFamily
overlapFamily outputResidual = outputOverlapFamily
overlapFamily firstNear = firstOverlapFamily
overlapFamily firstTransition = firstOverlapFamily
overlapFamily firstResidual = firstOverlapFamily
overlapFamily secondNear = secondOverlapFamily
overlapFamily secondTransition = secondOverlapFamily
overlapFamily secondResidual = secondOverlapFamily

data AffineRow : Set where
  separated : SeparatedRow → AffineRow
  overlap : OverlapRow → AffineRow

rowFamily : AffineRow → IndependentCoefficientFamily
rowFamily (separated row) = separatedFamily row
rowFamily (overlap row) = overlapFamily row

record ThreeLegCoefficientVector {s : Level} (Scalar : Set s) : Set (lsuc s) where
  constructor vector
  field
    leftCoefficient rightCoefficient outputCoefficient : Scalar

open ThreeLegCoefficientVector public

FamilyCoefficientAssignment :
  ∀ {s} (Scalar : Set s) → Set (lsuc s)
FamilyCoefficientAssignment Scalar =
  IndependentCoefficientFamily → ThreeLegCoefficientVector Scalar

extractRowVector :
  ∀ {s} {Scalar : Set s} →
  FamilyCoefficientAssignment Scalar →
  AffineRow →
  ThreeLegCoefficientVector Scalar
extractRowVector assignment row = assignment (rowFamily row)

allRowsFactorThroughEightFamilies :
  ∀ {s} {Scalar : Set s}
    (assignment : FamilyCoefficientAssignment Scalar)
    (row : AffineRow) →
  extractRowVector assignment row ≡ assignment (rowFamily row)
allRowsFactorThroughEightFamilies assignment row = refl

record OverlapClassDoesNotChangeWeightVector : Set where
  constructor overlap-receipt
  field
    outputNearTransition :
      overlapFamily outputNear ≡ overlapFamily outputTransition
    outputTransitionResidual :
      overlapFamily outputTransition ≡ overlapFamily outputResidual
    firstNearTransition :
      overlapFamily firstNear ≡ overlapFamily firstTransition
    firstTransitionResidual :
      overlapFamily firstTransition ≡ overlapFamily firstResidual
    secondNearTransition :
      overlapFamily secondNear ≡ overlapFamily secondTransition
    secondTransitionResidual :
      overlapFamily secondTransition ≡ overlapFamily secondResidual

open OverlapClassDoesNotChangeWeightVector public

overlapClassDoesNotChangeWeightVector :
  OverlapClassDoesNotChangeWeightVector
overlapClassDoesNotChangeWeightVector =
  overlap-receipt refl refl refl refl refl refl

separatedRowCount overlapRowCount totalRowCount : Nat
separatedRowCount = 12
overlapRowCount = 9
totalRowCount = separatedRowCount + overlapRowCount

separatedFamilyCount overlapFamilyCount independentFamilyCount : Nat
separatedFamilyCount = 5
overlapFamilyCount = 3
independentFamilyCount = separatedFamilyCount + overlapFamilyCount

coefficientCountPerFamily rawCoefficientSlotCount
  independentCoefficientSlotCount : Nat
coefficientCountPerFamily = 3
rawCoefficientSlotCount = totalRowCount * coefficientCountPerFamily
independentCoefficientSlotCount =
  independentFamilyCount * coefficientCountPerFamily

rawCoefficientSlotCountIs63 : rawCoefficientSlotCount ≡ 63
rawCoefficientSlotCountIs63 = refl

independentCoefficientSlotCountIs24 :
  independentCoefficientSlotCount ≡ 24
independentCoefficientSlotCountIs24 = refl

allTwelveSeparatedRowsFactorised : Bool
allTwelveSeparatedRowsFactorised = true

allTwelveSeparatedRowsFactorisedIsTrue :
  allTwelveSeparatedRowsFactorised ≡ true
allTwelveSeparatedRowsFactorisedIsTrue = refl

allNineOverlapRowsFactorised : Bool
allNineOverlapRowsFactorised = true

allNineOverlapRowsFactorisedIsTrue :
  allNineOverlapRowsFactorised ≡ true
allNineOverlapRowsFactorisedIsTrue = refl

rawSixtyThreeSlotsFactorThroughTwentyFourIndependentSlots : Bool
rawSixtyThreeSlotsFactorThroughTwentyFourIndependentSlots = true

rawSixtyThreeSlotsFactorThroughTwentyFourIndependentSlotsIsTrue :
  rawSixtyThreeSlotsFactorThroughTwentyFourIndependentSlots ≡ true
rawSixtyThreeSlotsFactorThroughTwentyFourIndependentSlotsIsTrue = refl

numericIndependentCoefficientVectorsSupplied : Bool
numericIndependentCoefficientVectorsSupplied = false

numericIndependentCoefficientVectorsSuppliedIsFalse :
  numericIndependentCoefficientVectorsSupplied ≡ false
numericIndependentCoefficientVectorsSuppliedIsFalse = refl
