module DASHI.Physics.YangMills.BalabanPeriodicFourierHodgeRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Fourier as Fourier
import DASHI.Physics.YangMills.BalabanPeriodicDifferenceSymbols as Difference
import DASHI.Physics.YangMills.BalabanPeriodicBlockSymbolGap as Gap
import DASHI.Physics.YangMills.BalabanPeriodicFiniteFourierHodgeCertificate as Certificate

------------------------------------------------------------------------
-- One-site regression. This exercises every new definition/adapter without
-- claiming the physical local-block estimate.
------------------------------------------------------------------------

data One : Set where
  one : One

data Holds : Set where
  holds : Holds

oneNat : Nat
oneNat = suc zero

index0 : Carrier.CyclicIndex oneNat
index0 = Carrier.zeroᵢ

site0 : Carrier.periodicTorus4Definition oneNat
site0 = Carrier.pair
  (Carrier.pair index0 index0)
  (Carrier.pair index0 index0)

axis0 : Carrier.Axis4
axis0 = Carrier.zeroᵢ

siteEnumerationRegression :
  Carrier._∈_ site0
    (Carrier.FiniteEnumeration.elements
      (Carrier.periodicTorus4Finite oneNat))
siteEnumerationRegression =
  Carrier.FiniteEnumeration.complete
    (Carrier.periodicTorus4Finite oneNat) site0

siteDecidableEqualityRegression : Carrier.Dec (site0 ≡ site0)
siteDecidableEqualityRegression =
  Carrier.periodicTorus4DecidableEquality oneNat site0 site0

oneBinary : One → One → One
oneBinary left right = one

oneUnary : One → One
oneUnary value = one

scalarOperations : Fourier.FourierScalarOperations One One
scalarOperations = record
  { zeroScalar = one
  ; oneScalar = one
  ; addScalar = oneBinary
  ; multiplyScalar = oneBinary
  ; negateScalar = oneUnary
  ; conjugateScalar = oneUnary
  ; normalizationScalar = one
  ; cardinalityScalar = one
  ; zeroBound = one
  ; addBound = oneBinary
  ; scaleBound = oneBinary
  }

fourierAuthority :
  Fourier.PeriodicTorus4FourierAuthority oneNat One One
fourierAuthority = record
  { operations = scalarOperations
  ; momentumAdd = λ k l → site0
  ; momentumNegate = λ k → site0
  ; momentumCharacter = λ k x → one
  ; sourceMomentumCharacterMultiplication = λ k l x → refl
  ; sourceMomentumCharacterConjugation = λ k x → refl
  ; scalarSiteNormSq = λ field → one
  ; scalarMomentumNormSq = λ field → one
  }

siteFieldValueOne :
  ∀ (field : Fourier.SiteField oneNat One) site → one ≡ field site
siteFieldValueOne field site with field site
... | one = refl

momentumFieldValueOne :
  ∀ (field : Fourier.MomentumField oneNat One) momentum →
  one ≡ field momentum
momentumFieldValueOne field momentum with field momentum
... | one = refl

fourierTheorems : Fourier.PeriodicTorus4FourierTheorems fourierAuthority
fourierTheorems = record
  { sourceCharacterOrthogonality = λ k l → refl
  ; sourceCharacterCompleteness = λ x y → refl
  ; sourceFiniteFourierInversionLeft = siteFieldValueOne
  ; sourceFiniteFourierInversionRight = momentumFieldValueOne
  ; sourceScalarFourierParseval = λ field → refl
  }

siteField : Fourier.SiteField oneNat One
siteField site = one

bondField : Fourier.AxisSiteField oneNat One
bondField axis site = one

bondInversionRegression :
  Fourier.bondInverseFourierTransform fourierAuthority
    (Fourier.bondFourierTransform fourierAuthority bondField)
    axis0 site0
  ≡ bondField axis0 site0
bondInversionRegression =
  Fourier.bondFourierInversion fourierTheorems bondField axis0 site0

bondParsevalRegression :
  Fourier.bondSiteNormSq fourierAuthority bondField ≡
  Fourier.bondMomentumNormSq fourierAuthority
    (Fourier.bondFourierTransform fourierAuthority bondField)
bondParsevalRegression =
  Fourier.fourierParsevalForBondFields fourierTheorems bondField

differencePrimitives :
  Difference.PeriodicDifferencePrimitives oneNat One One
differencePrimitives = record
  { fourierAuthority = fourierAuthority
  ; forwardDifferencePrimitive = λ axis field site → one
  ; backwardDifferencePrimitive = λ axis field site → one
  ; forwardDifferenceSymbolPrimitive = λ axis momentum → one
  ; backwardDifferenceSymbolPrimitive = λ axis momentum → one
  ; blockConstraintOperatorPrimitive = λ field axis site → one
  ; blockConstraintFourierOperatorPrimitive =
      λ field axis momentum → one
  }

differenceTheorems :
  Difference.PeriodicDifferenceFourierTheorems differencePrimitives
differenceTheorems = record
  { forwardDifferenceFourierSymbol =
      λ axis field momentum → refl
  ; backwardDifferenceFourierSymbol =
      λ axis field momentum → refl
  ; latticeGradientFourierSymbol =
      λ field axis momentum → refl
  ; latticeDivergenceFourierSymbol =
      λ field momentum → refl
  ; latticeCurlFourierSymbol =
      λ field pairIndex momentum → refl
  ; latticeCodifferentialFourierSymbol =
      λ field axis momentum → refl
  ; gaugeFixingOperatorFourierSymbol =
      λ field axis momentum → refl
  ; blockConstraintOperatorFourierSymbol =
      λ field axis momentum → refl
  ; referenceHessianFourierSymbol =
      λ field axis momentum → refl
  ; finiteFourierDiagonalizesScalarLaplacian =
      λ field momentum → refl
  ; finiteFourierDiagonalizesBondLaplacian =
      λ field axis momentum → refl
  ; finiteFourierDiagonalizesGaugeFixingTerm =
      λ field axis momentum → refl
  ; finiteFourierDiagonalizesBlockConstraintTerm =
      λ field axis momentum → refl
  ; finiteFourierDiagonalizesReferenceLaplacian =
      λ field axis momentum → refl
  }

orderedBound : Gap.OrderedAdditiveBound One
orderedBound = record
  { zero = one
  ; add = oneBinary
  ; scale = oneBinary
  ; LessEqual = λ left right → Holds
  ; Positive = λ value → Holds
  ; Nonnegative = λ value → Holds
  ; lessEqualTransitive = λ left≤middle middle≤right → holds
  ; addNonnegative = λ leftPositive rightPositive → holds
  }

symbolData : Gap.PeriodicReferenceSymbolData One One One One
symbolData = record
  { ordered = orderedBound
  ; fourier = λ state → one
  ; referenceEnergy = λ index state → one
  ; normSq = λ state → one
  ; frequencyNormSq = λ frequency → one
  ; differenceSymbolEnergy = λ index frequency → one
  ; gaugeSymbolEnergy = λ index frequency → one
  ; blockSymbolEnergy = λ index frequency → one
  ; symbolEnergy = λ index frequency → one
  ; referenceSymbolSumOfSquares = λ index frequency → refl
  ; differenceSymbolNonnegative = λ index frequency → holds
  ; gaugeSymbolNonnegative = λ index frequency → holds
  ; blockSymbolNonnegative = λ index frequency → holds
  ; finiteFourierDiagonalizesReferenceLaplacian =
      λ index state → refl
  ; fourierParsevalForBondFields = λ state → refl
  }

emptyEliminate : ∀ {A : Set} → Carrier.Empty → A
emptyEliminate ()

kernelData : Gap.PeriodicReferenceKernelData symbolData
kernelData = record
  { ZeroMomentum = λ frequency → Carrier.Empty
  ; DifferenceSymbolZero = λ index frequency → Carrier.Empty
  ; SymbolKernel = λ index frequency → Carrier.Empty
  ; ConstantMode = λ frequency → Carrier.Empty
  ; zeroMomentumImpliesDifferenceSymbolZero =
      λ index frequency impossible → emptyEliminate impossible
  ; differenceSymbolZeroImpliesZeroMomentum =
      λ index frequency impossible → emptyEliminate impossible
  ; referenceSymbolZeroImpliesConstantMode =
      λ index frequency impossible → emptyEliminate impossible
  ; constantModeImpliesReferenceSymbolZero =
      λ index frequency impossible → emptyEliminate impossible
  ; ForwardDifferenceSymbolNormSq = λ index frequency → Holds
  ; forwardDifferenceSymbolNormSq = λ index frequency → holds
  }

constraints : Gap.PeriodicConstraintRemovalData kernelData
constraints = record
  { GaugeOrthogonal = λ index state → Holds
  ; BlockAverageZero = λ index state → Holds
  ; ResidualGaugeOrthogonal = λ index state → Holds
  ; BoundaryCompatible = λ index state → Holds
  ; GaugeFixedTangent = λ index state → Holds
  ; tangentGaugeOrthogonal = λ index state tangent → holds
  ; tangentBlockAverageZero = λ index state tangent → holds
  ; tangentResidualGaugeOrthogonal = λ index state tangent → holds
  ; tangentBoundaryCompatible = λ index state tangent → holds
  ; GaugeOrthogonalityFourierIdentity = λ index state → Holds
  ; BlockAverageZeroFourierIdentity = λ index state → Holds
  ; ResidualGaugeOrthogonalityFourierIdentity = λ index state → Holds
  ; BoundaryCompatibilityFourierIdentity = λ index state → Holds
  ; gaugeOrthogonalityFourierIdentity =
      λ index state constraint → holds
  ; blockAverageZeroFourierIdentity =
      λ index state constraint → holds
  ; residualGaugeOrthogonalityFourierIdentity =
      λ index state constraint → holds
  ; boundaryCompatibilityFourierIdentity =
      λ index state constraint → holds
  ; ExactMode = λ index frequency → Carrier.Empty
  ; ResidualKernel = λ index frequency → Carrier.Empty
  ; BoundaryKernel = λ index frequency → Carrier.Empty
  ; gaugeConstraintRemovesExactModes =
      λ index state constraint impossible → impossible
  ; blockConstraintRemovesConstantModes =
      λ index state constraint impossible → impossible
  ; residualGaugeConstraintRemovesResidualKernel =
      λ index state constraint impossible → impossible
  ; boundaryConstraintRemovesBoundaryKernel =
      λ index state constraint impossible → impossible
  ; symbolKernelClassification =
      λ index frequency impossible → emptyEliminate impossible
  }

gapData : Gap.PeriodicBlockGapData constraints
gapData = record
  { cBulk = one
  ; cBulkPositive = holds
  ; Volume = One
  ; LatticeSpacing = One
  ; RGScale = One
  ; Background = One
  ; cBulkAt = λ volume spacing scaleValue background → one
  ; cBulkAtEqualsSelected =
      λ volume spacing scaleValue background → refl
  ; LowMomentum = λ index frequency → Holds
  ; HighMomentum = λ index frequency → Holds
  ; blockZeroModeFrequencyDecomposition =
      λ index frequency → Gap.left holds
  ; nonzeroMomentumDifferenceSymbolLowerBound =
      λ index frequency high → holds
  ; lowMomentumControlledByBlockConstraint =
      λ index frequency low removed → holds
  ; highMomentumControlledByDifferenceSymbol =
      λ index frequency high → holds
  ; GaugeLongitudinalModeControlled = λ index frequency → Holds
  ; TransverseModeControlledByCurl = λ index frequency → Holds
  ; gaugeLongitudinalModeControlled = λ index frequency → holds
  ; transverseModeControlledByCurl = λ index frequency → holds
  }

periodicHodgeRegression : Holds
periodicHodgeRegression =
  Certificate.periodicBulkGaugeFixedHodgePoincare
    symbolData kernelData constraints gapData one one holds
