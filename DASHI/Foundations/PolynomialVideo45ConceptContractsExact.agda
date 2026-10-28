module DASHI.Foundations.PolynomialVideo45ConceptContractsExact where

------------------------------------------------------------------------
-- COMPLETE VIDEO CONCEPT INVENTORY: 45 distinct topics.
-- Owners / evidence are SOURCE-TYPED: this is NOT 45 completed theorems.
-- Every topic maps to a proof receiver and an explicit promotion status.
-- Mathematical background: Abel, Galois, Riemann, Viete, Hamilton;
-- source video: 2swap teaching transcript supplied by user.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

data VideoConcept : Set where
  polynomialCoefficients
    domainColouring
    numberSystemExtensions
    plusMinusImaginary
    complexAlgebraicClosure
    rootMultiplicityCount
    localZeroWinding
    coefficientLength
    binaryCoefficientAlphabet
    fractalResemblance
    linearEquation
    rootCoefficientOrder
    globalRootChoice
    branchCutSelection
    conjugateRoots
    branchCutRelocation
    riemannSurface
    unorderedRootSelection
    squareRootLoopSwap
    cubicNeedsCubeRoot
    cubeRootC3
    c3MissesSwap
    adjacentRootSwaps
    nontrivialS3Commutator
    cyclicRadicalIsAbelian
    nestedSkewedRadicals
    cardanoFormula
    quarticNestedCommutator
    radicalTowerDerivedLimit
    radicalTowerIteration
    s2DerivedTrivial
    s3DerivedSeries
    s4DerivedSeries
    overlappingFiveRootCycles
    doubleCommutatorRecovery
    unboundedNestedCommutator
    finiteRadicalTowerObstruction
    a5Perfectness
    genericQuinticAbelRuffini
    higherDegreeObstruction
    finiteRootCloud
    interactiveRootTracking
    ternaryCoefficientAlphabet
    visualizerDemo
    numerologyDistinction : VideoConcept

data Scope : Set where
  finiteOwner typedFiniteModel globalProofInput : Scope

conceptScope : VideoConcept → Scope
conceptScope polynomialCoefficients = finiteOwner
conceptScope domainColouring = globalProofInput
conceptScope numberSystemExtensions = globalProofInput
conceptScope plusMinusImaginary = finiteOwner
conceptScope complexAlgebraicClosure = globalProofInput
conceptScope rootMultiplicityCount = globalProofInput
conceptScope localZeroWinding = globalProofInput
conceptScope coefficientLength = finiteOwner
conceptScope binaryCoefficientAlphabet = finiteOwner
conceptScope fractalResemblance = typedFiniteModel
conceptScope linearEquation = globalProofInput
conceptScope rootCoefficientOrder = finiteOwner
conceptScope globalRootChoice = typedFiniteModel
conceptScope branchCutSelection = finiteOwner
conceptScope conjugateRoots = finiteOwner
conceptScope branchCutRelocation = globalProofInput
conceptScope riemannSurface = globalProofInput
conceptScope unorderedRootSelection = typedFiniteModel
conceptScope squareRootLoopSwap = finiteOwner
conceptScope cubicNeedsCubeRoot = typedFiniteModel
conceptScope cubeRootC3 = finiteOwner
conceptScope c3MissesSwap = finiteOwner
conceptScope adjacentRootSwaps = finiteOwner
conceptScope nontrivialS3Commutator = finiteOwner
conceptScope cyclicRadicalIsAbelian = finiteOwner
conceptScope nestedSkewedRadicals = typedFiniteModel
conceptScope cardanoFormula = globalProofInput
conceptScope quarticNestedCommutator = typedFiniteModel
conceptScope radicalTowerDerivedLimit = typedFiniteModel
conceptScope radicalTowerIteration = typedFiniteModel
conceptScope s2DerivedTrivial = finiteOwner
conceptScope s3DerivedSeries = finiteOwner
conceptScope s4DerivedSeries = typedFiniteModel
conceptScope overlappingFiveRootCycles = finiteOwner
conceptScope doubleCommutatorRecovery = finiteOwner
conceptScope unboundedNestedCommutator = typedFiniteModel
conceptScope finiteRadicalTowerObstruction = typedFiniteModel
conceptScope a5Perfectness = globalProofInput
conceptScope genericQuinticAbelRuffini = globalProofInput
conceptScope higherDegreeObstruction = globalProofInput
conceptScope finiteRootCloud = typedFiniteModel
conceptScope interactiveRootTracking = typedFiniteModel
conceptScope ternaryCoefficientAlphabet = typedFiniteModel
conceptScope visualizerDemo = finiteOwner
conceptScope numerologyDistinction = finiteOwner

videoConcept01 : VideoConcept
videoConcept01 = polynomialCoefficients

videoConcept02 : VideoConcept
videoConcept02 = domainColouring

videoConcept03 : VideoConcept
videoConcept03 = numberSystemExtensions

videoConcept04 : VideoConcept
videoConcept04 = plusMinusImaginary

videoConcept05 : VideoConcept
videoConcept05 = complexAlgebraicClosure

videoConcept06 : VideoConcept
videoConcept06 = rootMultiplicityCount

videoConcept07 : VideoConcept
videoConcept07 = localZeroWinding

videoConcept08 : VideoConcept
videoConcept08 = coefficientLength

videoConcept09 : VideoConcept
videoConcept09 = binaryCoefficientAlphabet

videoConcept10 : VideoConcept
videoConcept10 = fractalResemblance

videoConcept11 : VideoConcept
videoConcept11 = linearEquation

videoConcept12 : VideoConcept
videoConcept12 = rootCoefficientOrder

videoConcept13 : VideoConcept
videoConcept13 = globalRootChoice

videoConcept14 : VideoConcept
videoConcept14 = branchCutSelection

videoConcept15 : VideoConcept
videoConcept15 = conjugateRoots

videoConcept16 : VideoConcept
videoConcept16 = branchCutRelocation

videoConcept17 : VideoConcept
videoConcept17 = riemannSurface

videoConcept18 : VideoConcept
videoConcept18 = unorderedRootSelection

videoConcept19 : VideoConcept
videoConcept19 = squareRootLoopSwap

videoConcept20 : VideoConcept
videoConcept20 = cubicNeedsCubeRoot

videoConcept21 : VideoConcept
videoConcept21 = cubeRootC3

videoConcept22 : VideoConcept
videoConcept22 = c3MissesSwap

videoConcept23 : VideoConcept
videoConcept23 = adjacentRootSwaps

videoConcept24 : VideoConcept
videoConcept24 = nontrivialS3Commutator

videoConcept25 : VideoConcept
videoConcept25 = cyclicRadicalIsAbelian

videoConcept26 : VideoConcept
videoConcept26 = nestedSkewedRadicals

videoConcept27 : VideoConcept
videoConcept27 = cardanoFormula

videoConcept28 : VideoConcept
videoConcept28 = quarticNestedCommutator

videoConcept29 : VideoConcept
videoConcept29 = radicalTowerDerivedLimit

videoConcept30 : VideoConcept
videoConcept30 = radicalTowerIteration

videoConcept31 : VideoConcept
videoConcept31 = s2DerivedTrivial

videoConcept32 : VideoConcept
videoConcept32 = s3DerivedSeries

videoConcept33 : VideoConcept
videoConcept33 = s4DerivedSeries

videoConcept34 : VideoConcept
videoConcept34 = overlappingFiveRootCycles

videoConcept35 : VideoConcept
videoConcept35 = doubleCommutatorRecovery

videoConcept36 : VideoConcept
videoConcept36 = unboundedNestedCommutator

videoConcept37 : VideoConcept
videoConcept37 = finiteRadicalTowerObstruction

videoConcept38 : VideoConcept
videoConcept38 = a5Perfectness

videoConcept39 : VideoConcept
videoConcept39 = genericQuinticAbelRuffini

videoConcept40 : VideoConcept
videoConcept40 = higherDegreeObstruction

videoConcept41 : VideoConcept
videoConcept41 = finiteRootCloud

videoConcept42 : VideoConcept
videoConcept42 = interactiveRootTracking

videoConcept43 : VideoConcept
videoConcept43 = ternaryCoefficientAlphabet

videoConcept44 : VideoConcept
videoConcept44 = visualizerDemo

videoConcept45 : VideoConcept
videoConcept45 = numerologyDistinction

-- Neither a "finiteOwner" nor an "interface" means the complex analytic
-- theorem was kernel checked in this PR. No test receipt is manufactured.
kernelVerifiedInThisPR : VideoConcept → Bool
kernelVerifiedInThisPR _ = false

kernelVerificationNotAssertedHere :
  (concept : VideoConcept) →
  kernelVerifiedInThisPR concept ≡ false
kernelVerificationNotAssertedHere concept = refl
