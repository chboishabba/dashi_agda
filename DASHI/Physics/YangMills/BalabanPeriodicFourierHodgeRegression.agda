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
  { Fourier.zeroScalar = one
  ; Fourier.oneScalar = one
  ; Fourier.addScalar = oneBinary
  ; Fourier.multiplyScalar = oneBinary
  ; Fourier.negateScalar = oneUnary
  ; Fourier.conjugateScalar = oneUnary
  ; Fourier.normalizationScalar = one
  ; Fourier.cardinalityScalar = one
  ; Fourier.zeroBound = one
  ; Fourier.addBound = oneBinary
  ; Fourier.scaleBound = oneBinary
  }

fourierAuthority :
  Fourier.PeriodicTorus4FourierAuthority oneNat One One
fourierAuthority = record
  { Fourier.operations = scalarOperations
  ; Fourier.momentumAdd = λ k l → site0
  ; Fourier.momentumNegate = λ k → site0
  ; Fourier.momentumCharacter = λ k x → one
  ; Fourier.sourceMomentumCharacterMultiplication = λ k l x → refl
  ; Fourier.sourceMomentumCharacterConjugation = λ k x → refl
  ; Fourier.scalarSiteNormSq = λ field → one
  ; Fourier.scalarMomentumNormSq = λ field → one
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
  { Fourier.sourceCharacterOrthogonality = λ k l → refl
  ; Fourier.sourceCharacterCompleteness = λ x y → refl
  ; Fourier.sourceFiniteFourierInversionLeft = siteFieldValueOne
  ; Fourier.sourceFiniteFourierInversionRight = momentumFieldValueOne
  ; Fourier.sourceScalarFourierParseval = λ field → refl
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
  { Difference.fourierAuthority = fourierAuthority
  ; Difference.forwardDifferencePrimitive = λ axis field site → one
  ; Difference.backwardDifferencePrimitive = λ axis field site → one
  ; Difference.forwardDifferenceSymbolPrimitive = λ axis momentum → one
  ; Difference.backwardDifferenceSymbolPrimitive = λ axis momentum → one
  ; Difference.blockConstraintOperatorPrimitive = λ field axis site → one
  ; Difference.blockConstraintFourierOperatorPrimitive =
      λ field axis momentum → one
  }

differenceTheorems :
  Difference.PeriodicDifferenceFourierTheorems differencePrimitives
differenceTheorems = record
  { Difference.forwardDifferenceFourierSymbol =
      λ axis field momentum → refl
  ; Difference.backwardDifferenceFourierSymbol =
      λ axis field momentum → refl
  ; Difference.latticeGradientFourierSymbol =
      λ field axis momentum → refl
  ; Difference.latticeDivergenceFourierSymbol =
      λ field momentum → refl
  ; Difference.latticeCurlFourierSymbol =
      λ field pairIndex momentum → refl
  ; Difference.latticeCodifferentialFourierSymbol =
      λ field axis momentum → refl
  ; Difference.gaugeFixingOperatorFourierSymbol =
      λ field axis momentum → refl
  ; Difference.blockConstraintOperatorFourierSymbol =
      λ field axis momentum → refl
  ; Difference.referenceHessianFourierSymbol =
      λ field axis momentum → refl
  ; Difference.finiteFourierDiagonalizesScalarLaplacian =
      λ field momentum → refl
  ; Difference.finiteFourierDiagonalizesBondLaplacian =
      λ field axis momentum → refl
  ; Difference.finiteFourierDiagonalizesGaugeFixingTerm =
      λ field axis momentum → refl
  ; Difference.finiteFourierDiagonalizesBlockConstraintTerm =
      λ field axis momentum → refl
  ; Difference.finiteFourierDiagonalizesReferenceLaplacian =
      λ field axis momentum → refl
  }

orderedBound : Gap.OrderedAdditiveBound One
orderedBound = record
  { Gap.zero = one
  ; Gap.add = oneBinary
  ; Gap.scale = oneBinary
  ; Gap.LessEqual = λ left right → Holds
  ; Gap.Positive = λ value → Holds
  ; Gap.Nonnegative = λ value → Holds
  ; Gap.lessEqualTransitive = λ left≤middle middle≤right → holds
  ; Gap.addNonnegative = λ leftPositive rightPositive → holds
  }

symbolData : Gap.PeriodicReferenceSymbolData One One One One
symbolData = record
  { Gap.ordered = orderedBound
  ; Gap.fourier = λ state → one
  ; Gap.referenceEnergy = λ index state → one
  ; Gap.normSq = λ state → one
  ; Gap.frequencyNormSq = λ frequency → one
  ; Gap.differenceSymbolEnergy = λ index frequency → one
  ; Gap.gaugeSymbolEnergy = λ index frequency → one
  ; Gap.blockSymbolEnergy = λ index frequency → one
  ; Gap.symbolEnergy = λ index frequency → one
  ; Gap.referenceSymbolSumOfSquares = λ index frequency → refl
  ; Gap.differenceSymbolNonnegative = λ index frequency → holds
  ; Gap.gaugeSymbolNonnegative = λ index frequency → holds
  ; Gap.blockSymbolNonnegative = λ index frequency → holds
  ; Gap.finiteFourierDiagonalizesReferenceLaplacian =
      λ index state → refl
  ; Gap.fourierParsevalForBondFields = λ state → refl
  }

emptyEliminate : ∀ {A : Set} → Carrier.Empty → A
emptyEliminate ()

kernelData : Gap.PeriodicReferenceKernelData symbolData
kernelData = record
  { Gap.ZeroMomentum = λ frequency → Carrier.Empty
  ; Gap.DifferenceSymbolZero = λ index frequency → Carrier.Empty
  ; Gap.SymbolKernel = λ index frequency → Carrier.Empty
  ; Gap.ConstantMode = λ frequency → Carrier.Empty
  ; Gap.zeroMomentumImpliesDifferenceSymbolZero =
      λ index frequency impossible → emptyEliminate impossible
  ; Gap.differenceSymbolZeroImpliesZeroMomentum =
      λ index frequency impossible → emptyEliminate impossible
  ; Gap.referenceSymbolZeroImpliesConstantMode =
      λ index frequency impossible → emptyEliminate impossible
  ; Gap.constantModeImpliesReferenceSymbolZero =
      λ index frequency impossible → emptyEliminate impossible
  ; Gap.ForwardDifferenceSymbolNormSq = λ index frequency → Holds
  ; Gap.forwardDifferenceSymbolNormSq = λ index frequency → holds
  }

constraints : Gap.PeriodicConstraintRemovalData kernelData
constraints = record
  { Gap.GaugeOrthogonal = λ index state → Holds
  ; Gap.BlockAverageZero = λ index state → Holds
  ; Gap.ResidualGaugeOrthogonal = λ index state → Holds
  ; Gap.BoundaryCompatible = λ index state → Holds
  ; Gap.GaugeFixedTangent = λ index state → Holds
  ; Gap.tangentGaugeOrthogonal = λ index state tangent → holds
  ; Gap.tangentBlockAverageZero = λ index state tangent → holds
  ; Gap.tangentResidualGaugeOrthogonal = λ index state tangent → holds
  ; Gap.tangentBoundaryCompatible = λ index state tangent → holds
  ; Gap.GaugeOrthogonalityFourierIdentity = λ index state → Holds
  ; Gap.BlockAverageZeroFourierIdentity = λ index state → Holds
  ; Gap.ResidualGaugeOrthogonalityFourierIdentity = λ index state → Holds
  ; Gap.BoundaryCompatibilityFourierIdentity = λ index state → Holds
  ; Gap.gaugeOrthogonalityFourierIdentity =
      λ index state constraint → holds
  ; Gap.blockAverageZeroFourierIdentity =
      λ index state constraint → holds
  ; Gap.residualGaugeOrthogonalityFourierIdentity =
      λ index state constraint → holds
  ; Gap.boundaryCompatibilityFourierIdentity =
      λ index state constraint → holds
  ; Gap.ExactMode = λ index frequency → Carrier.Empty
  ; Gap.ResidualKernel = λ index frequency → Carrier.Empty
  ; Gap.BoundaryKernel = λ index frequency → Carrier.Empty
  ; Gap.gaugeConstraintRemovesExactModes =
      λ index state constraint impossible → impossible
  ; Gap.blockConstraintRemovesConstantModes =
      λ index state constraint impossible → impossible
  ; Gap.residualGaugeConstraintRemovesResidualKernel =
      λ index state constraint impossible → impossible
  ; Gap.boundaryConstraintRemovesBoundaryKernel =
      λ index state constraint impossible → impossible
  ; Gap.symbolKernelClassification =
      λ index frequency impossible → emptyEliminate impossible
  }

gapData : Gap.PeriodicBlockGapData constraints
gapData = record
  { Gap.cBulk = one
  ; Gap.cBulkPositive = holds
  ; Gap.Volume = One
  ; Gap.LatticeSpacing = One
  ; Gap.RGScale = One
  ; Gap.Background = One
  ; Gap.cBulkAt = λ volume spacing scaleValue background → one
  ; Gap.cBulkAtEqualsSelected =
      λ volume spacing scaleValue background → refl
  ; Gap.LowMomentum = λ index frequency → Holds
  ; Gap.HighMomentum = λ index frequency → Holds
  ; Gap.blockZeroModeFrequencyDecomposition =
      λ index frequency → Gap.left holds
  ; Gap.nonzeroMomentumDifferenceSymbolLowerBound =
      λ index frequency high → holds
  ; Gap.lowMomentumControlledByBlockConstraint =
      λ index frequency low removed → holds
  ; Gap.highMomentumControlledByDifferenceSymbol =
      λ index frequency high → holds
  ; Gap.GaugeLongitudinalModeControlled = λ index frequency → Holds
  ; Gap.TransverseModeControlledByCurl = λ index frequency → Holds
  ; Gap.gaugeLongitudinalModeControlled = λ index frequency → holds
  ; Gap.transverseModeControlledByCurl = λ index frequency → holds
  }

periodicHodgeRegression : Holds
periodicHodgeRegression =
  Certificate.periodicBulkGaugeFixedHodgePoincare
    symbolData kernelData constraints gapData one one holds
