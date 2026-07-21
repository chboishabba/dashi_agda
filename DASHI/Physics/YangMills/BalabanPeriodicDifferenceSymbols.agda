module DASHI.Physics.YangMills.BalabanPeriodicDifferenceSymbols where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Fourier

------------------------------------------------------------------------
-- Literal difference operators and their Fourier-domain formulas.
--
-- Forward/backward differences and the block operator are the primitive
-- lattice data. Gradient, divergence, curl, codifferential, gauge fixing,
-- scalar/bond Laplacians and the reference Hessian are defined here from
-- those primitives. The standard Fourier intertwining theorem is required
-- against exactly these definitions.
------------------------------------------------------------------------

Plaquette4 : Set
Plaquette4 = Product Axis4 Axis4

PlaquetteSiteField : Nat → Set → Set
PlaquetteSiteField L Scalar = Plaquette4 → SiteField L Scalar

PlaquetteMomentumField : Nat → Set → Set
PlaquetteMomentumField L Scalar = Plaquette4 → MomentumField L Scalar

record PeriodicDifferencePrimitives
    (L : Nat) (Scalar Bound : Set) : Set₁ where
  field
    fourierAuthority : PeriodicTorus4FourierAuthority L Scalar Bound

    forwardDifferencePrimitive backwardDifferencePrimitive :
      Axis4 → SiteField L Scalar → SiteField L Scalar

    forwardDifferenceSymbolPrimitive backwardDifferenceSymbolPrimitive :
      Axis4 → dualPeriodicTorus4Definition L → Scalar

    blockConstraintOperatorPrimitive :
      AxisSiteField L Scalar → AxisSiteField L Scalar

    blockConstraintFourierOperatorPrimitive :
      AxisMomentumField L Scalar → AxisMomentumField L Scalar

open PeriodicDifferencePrimitives public

sumAxesScalar :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  (Axis4 → Scalar) → Scalar
sumAxesScalar primitives term =
  sumScalarList (operations (fourierAuthority primitives)) term
    (elements (cyclicIndexFinite four))

forwardDifference :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  Axis4 → SiteField L Scalar → SiteField L Scalar
forwardDifference = forwardDifferencePrimitive

backwardDifference :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  Axis4 → SiteField L Scalar → SiteField L Scalar
backwardDifference = backwardDifferencePrimitive

forwardDifferenceSymbol :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  Axis4 → dualPeriodicTorus4Definition L → Scalar
forwardDifferenceSymbol = forwardDifferenceSymbolPrimitive

backwardDifferenceSymbol :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  Axis4 → dualPeriodicTorus4Definition L → Scalar
backwardDifferenceSymbol = backwardDifferenceSymbolPrimitive

latticeGradient :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  SiteField L Scalar → AxisSiteField L Scalar
latticeGradient primitives field axis =
  forwardDifference primitives axis field

latticeDivergence :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → SiteField L Scalar
latticeDivergence primitives field site =
  sumAxesScalar primitives
    (λ axis → backwardDifference primitives axis (field axis) site)

latticeCurl :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → PlaquetteSiteField L Scalar
latticeCurl primitives field (pair mu nu) site =
  addScalar (operations (fourierAuthority primitives))
    (forwardDifference primitives mu (field nu) site)
    (negateScalar (operations (fourierAuthority primitives))
      (forwardDifference primitives nu (field mu) site))

latticeCodifferential :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  PlaquetteSiteField L Scalar → AxisSiteField L Scalar
latticeCodifferential primitives field axis site =
  sumAxesScalar primitives
    (λ nu → backwardDifference primitives nu (field (pair nu axis)) site)

gaugeFixingOperator :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → AxisSiteField L Scalar
gaugeFixingOperator primitives field =
  latticeGradient primitives (latticeDivergence primitives field)

curlCodifferentialOperator :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → AxisSiteField L Scalar
curlCodifferentialOperator primitives field =
  latticeCodifferential primitives (latticeCurl primitives field)

scalarLaplacian :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  SiteField L Scalar → SiteField L Scalar
scalarLaplacian primitives field site =
  sumAxesScalar primitives
    (λ axis →
      backwardDifference primitives axis
        (forwardDifference primitives axis field) site)

bondLaplacian :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → AxisSiteField L Scalar
bondLaplacian primitives field axis =
  scalarLaplacian primitives (field axis)

latticeHodgeOperator :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → AxisSiteField L Scalar
latticeHodgeOperator primitives field axis site =
  addScalar (operations (fourierAuthority primitives))
    (curlCodifferentialOperator primitives field axis site)
    (gaugeFixingOperator primitives field axis site)

blockConstraintOperator :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → AxisSiteField L Scalar
blockConstraintOperator = blockConstraintOperatorPrimitive

referenceHessian :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → AxisSiteField L Scalar
referenceHessian primitives field axis site =
  addScalar (operations (fourierAuthority primitives))
    (latticeHodgeOperator primitives field axis site)
    (blockConstraintOperator primitives field axis site)

------------------------------------------------------------------------
-- Fourier-domain formulas.
------------------------------------------------------------------------

forwardDifferenceSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  Axis4 → MomentumField L Scalar → MomentumField L Scalar
forwardDifferenceSymbolAction primitives axis field momentum =
  multiplyScalar (operations (fourierAuthority primitives))
    (forwardDifferenceSymbol primitives axis momentum)
    (field momentum)

backwardDifferenceSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  Axis4 → MomentumField L Scalar → MomentumField L Scalar
backwardDifferenceSymbolAction primitives axis field momentum =
  multiplyScalar (operations (fourierAuthority primitives))
    (backwardDifferenceSymbol primitives axis momentum)
    (field momentum)

latticeGradientSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  MomentumField L Scalar → AxisMomentumField L Scalar
latticeGradientSymbolAction primitives field axis =
  forwardDifferenceSymbolAction primitives axis field

latticeDivergenceSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → MomentumField L Scalar
latticeDivergenceSymbolAction primitives field momentum =
  sumAxesScalar primitives
    (λ axis →
      multiplyScalar (operations (fourierAuthority primitives))
        (backwardDifferenceSymbol primitives axis momentum)
        (field axis momentum))

latticeCurlSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → PlaquetteMomentumField L Scalar
latticeCurlSymbolAction primitives field (pair mu nu) momentum =
  addScalar (operations (fourierAuthority primitives))
    (multiplyScalar (operations (fourierAuthority primitives))
      (forwardDifferenceSymbol primitives mu momentum)
      (field nu momentum))
    (negateScalar (operations (fourierAuthority primitives))
      (multiplyScalar (operations (fourierAuthority primitives))
        (forwardDifferenceSymbol primitives nu momentum)
        (field mu momentum)))

latticeCodifferentialSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  PlaquetteMomentumField L Scalar → AxisMomentumField L Scalar
latticeCodifferentialSymbolAction primitives field axis momentum =
  sumAxesScalar primitives
    (λ nu →
      multiplyScalar (operations (fourierAuthority primitives))
        (backwardDifferenceSymbol primitives nu momentum)
        (field (pair nu axis) momentum))

gaugeFixingSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → AxisMomentumField L Scalar
gaugeFixingSymbolAction primitives field =
  latticeGradientSymbolAction primitives
    (latticeDivergenceSymbolAction primitives field)

curlCodifferentialSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → AxisMomentumField L Scalar
curlCodifferentialSymbolAction primitives field =
  latticeCodifferentialSymbolAction primitives
    (latticeCurlSymbolAction primitives field)

scalarLaplacianSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  MomentumField L Scalar → MomentumField L Scalar
scalarLaplacianSymbolAction primitives field momentum =
  sumAxesScalar primitives
    (λ axis →
      multiplyScalar (operations (fourierAuthority primitives))
        (backwardDifferenceSymbol primitives axis momentum)
        (multiplyScalar (operations (fourierAuthority primitives))
          (forwardDifferenceSymbol primitives axis momentum)
          (field momentum)))

bondLaplacianSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → AxisMomentumField L Scalar
bondLaplacianSymbolAction primitives field axis =
  scalarLaplacianSymbolAction primitives (field axis)

latticeHodgeSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → AxisMomentumField L Scalar
latticeHodgeSymbolAction primitives field axis momentum =
  addScalar (operations (fourierAuthority primitives))
    (curlCodifferentialSymbolAction primitives field axis momentum)
    (gaugeFixingSymbolAction primitives field axis momentum)

blockConstraintSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → AxisMomentumField L Scalar
blockConstraintSymbolAction = blockConstraintFourierOperatorPrimitive

referenceSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → AxisMomentumField L Scalar
referenceSymbolAction primitives field axis momentum =
  addScalar (operations (fourierAuthority primitives))
    (latticeHodgeSymbolAction primitives field axis momentum)
    (blockConstraintSymbolAction primitives field axis momentum)

referenceSymbolFormula :
  ∀ {L Scalar Bound}
    (primitives : PeriodicDifferencePrimitives L Scalar Bound) →
  ∀ field axis momentum →
  referenceSymbolAction primitives field axis momentum ≡
  addScalar (operations (fourierAuthority primitives))
    (latticeHodgeSymbolAction primitives field axis momentum)
    (blockConstraintSymbolAction primitives field axis momentum)
referenceSymbolFormula primitives field axis momentum = refl

------------------------------------------------------------------------
-- Exact standard Fourier intertwining theorem for these definitions.
------------------------------------------------------------------------

record PeriodicDifferenceFourierTheorems
    {L : Nat} {Scalar Bound : Set}
    (primitives : PeriodicDifferencePrimitives L Scalar Bound) : Set₁ where
  field
    forwardDifferenceFourierSymbol : ∀ axis field momentum →
      finiteFourierTransformDefinition (fourierAuthority primitives)
        (forwardDifference primitives axis field) momentum
      ≡ forwardDifferenceSymbolAction primitives axis
          (finiteFourierTransformDefinition
            (fourierAuthority primitives) field) momentum

    backwardDifferenceFourierSymbol : ∀ axis field momentum →
      finiteFourierTransformDefinition (fourierAuthority primitives)
        (backwardDifference primitives axis field) momentum
      ≡ backwardDifferenceSymbolAction primitives axis
          (finiteFourierTransformDefinition
            (fourierAuthority primitives) field) momentum

    latticeGradientFourierSymbol : ∀ field axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (latticeGradient primitives field) axis momentum
      ≡ latticeGradientSymbolAction primitives
          (finiteFourierTransformDefinition
            (fourierAuthority primitives) field) axis momentum

    latticeDivergenceFourierSymbol : ∀ field momentum →
      finiteFourierTransformDefinition (fourierAuthority primitives)
        (latticeDivergence primitives field) momentum
      ≡ latticeDivergenceSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) field) momentum

    latticeCurlFourierSymbol : ∀ field pairIndex momentum →
      finiteFourierTransformDefinition (fourierAuthority primitives)
        (latticeCurl primitives field pairIndex) momentum
      ≡ latticeCurlSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) field)
          pairIndex momentum

    latticeCodifferentialFourierSymbol : ∀ field axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (latticeCodifferential primitives field) axis momentum
      ≡ latticeCodifferentialSymbolAction primitives
          (λ pairIndex →
            finiteFourierTransformDefinition (fourierAuthority primitives)
              (field pairIndex))
          axis momentum

    gaugeFixingOperatorFourierSymbol : ∀ field axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (gaugeFixingOperator primitives field) axis momentum
      ≡ gaugeFixingSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) field)
          axis momentum

    blockConstraintOperatorFourierSymbol : ∀ field axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (blockConstraintOperator primitives field) axis momentum
      ≡ blockConstraintSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) field)
          axis momentum

    referenceHessianFourierSymbol : ∀ field axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (referenceHessian primitives field) axis momentum
      ≡ referenceSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) field)
          axis momentum

    finiteFourierDiagonalizesScalarLaplacian : ∀ field momentum →
      finiteFourierTransformDefinition (fourierAuthority primitives)
        (scalarLaplacian primitives field) momentum
      ≡ scalarLaplacianSymbolAction primitives
          (finiteFourierTransformDefinition
            (fourierAuthority primitives) field) momentum

    finiteFourierDiagonalizesBondLaplacian : ∀ field axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (bondLaplacian primitives field) axis momentum
      ≡ bondLaplacianSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) field)
          axis momentum

    finiteFourierDiagonalizesGaugeFixingTerm : ∀ field axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (gaugeFixingOperator primitives field) axis momentum
      ≡ gaugeFixingSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) field)
          axis momentum

    finiteFourierDiagonalizesBlockConstraintTerm : ∀ field axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (blockConstraintOperator primitives field) axis momentum
      ≡ blockConstraintSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) field)
          axis momentum

    finiteFourierDiagonalizesReferenceLaplacian : ∀ field axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (referenceHessian primitives field) axis momentum
      ≡ referenceSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) field)
          axis momentum

open PeriodicDifferenceFourierTheorems public

periodicDifferenceDefinitionsLevel : ProofLevel
periodicDifferenceDefinitionsLevel = machineChecked

periodicDifferenceFourierTheoremsLevel : ProofLevel
periodicDifferenceFourierTheoremsLevel = standardImported

referenceSymbolFormulaLevel : ProofLevel
referenceSymbolFormulaLevel = machineChecked
