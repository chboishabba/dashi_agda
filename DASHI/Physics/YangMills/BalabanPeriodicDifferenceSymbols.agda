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
latticeGradient primitives fld axis =
  forwardDifference primitives axis fld

latticeDivergence :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → SiteField L Scalar
latticeDivergence primitives fld site =
  sumAxesScalar primitives
    (λ axis → backwardDifference primitives axis (fld axis) site)

latticeCurl :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → PlaquetteSiteField L Scalar
latticeCurl primitives fld (pair mu nu) site =
  addScalar (operations (fourierAuthority primitives))
    (forwardDifference primitives mu (fld nu) site)
    (negateScalar (operations (fourierAuthority primitives))
      (forwardDifference primitives nu (fld mu) site))

latticeCodifferential :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  PlaquetteSiteField L Scalar → AxisSiteField L Scalar
latticeCodifferential primitives fld axis site =
  sumAxesScalar primitives
    (λ nu → backwardDifference primitives nu (fld (pair nu axis)) site)

gaugeFixingOperator :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → AxisSiteField L Scalar
gaugeFixingOperator primitives fld =
  latticeGradient primitives (latticeDivergence primitives fld)

curlCodifferentialOperator :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → AxisSiteField L Scalar
curlCodifferentialOperator primitives fld =
  latticeCodifferential primitives (latticeCurl primitives fld)

scalarLaplacian :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  SiteField L Scalar → SiteField L Scalar
scalarLaplacian primitives fld site =
  sumAxesScalar primitives
    (λ axis →
      backwardDifference primitives axis
        (forwardDifference primitives axis fld) site)

bondLaplacian :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → AxisSiteField L Scalar
bondLaplacian primitives fld axis =
  scalarLaplacian primitives (fld axis)

latticeHodgeOperator :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → AxisSiteField L Scalar
latticeHodgeOperator primitives fld axis site =
  addScalar (operations (fourierAuthority primitives))
    (curlCodifferentialOperator primitives fld axis site)
    (gaugeFixingOperator primitives fld axis site)

blockConstraintOperator :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → AxisSiteField L Scalar
blockConstraintOperator = blockConstraintOperatorPrimitive

referenceHessian :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisSiteField L Scalar → AxisSiteField L Scalar
referenceHessian primitives fld axis site =
  addScalar (operations (fourierAuthority primitives))
    (latticeHodgeOperator primitives fld axis site)
    (blockConstraintOperator primitives fld axis site)

------------------------------------------------------------------------
-- Fourier-domain formulas.
------------------------------------------------------------------------

forwardDifferenceSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  Axis4 → MomentumField L Scalar → MomentumField L Scalar
forwardDifferenceSymbolAction primitives axis fld momentum =
  multiplyScalar (operations (fourierAuthority primitives))
    (forwardDifferenceSymbol primitives axis momentum)
    (fld momentum)

backwardDifferenceSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  Axis4 → MomentumField L Scalar → MomentumField L Scalar
backwardDifferenceSymbolAction primitives axis fld momentum =
  multiplyScalar (operations (fourierAuthority primitives))
    (backwardDifferenceSymbol primitives axis momentum)
    (fld momentum)

latticeGradientSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  MomentumField L Scalar → AxisMomentumField L Scalar
latticeGradientSymbolAction primitives fld axis =
  forwardDifferenceSymbolAction primitives axis fld

latticeDivergenceSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → MomentumField L Scalar
latticeDivergenceSymbolAction primitives fld momentum =
  sumAxesScalar primitives
    (λ axis →
      multiplyScalar (operations (fourierAuthority primitives))
        (backwardDifferenceSymbol primitives axis momentum)
        (fld axis momentum))

latticeCurlSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → PlaquetteMomentumField L Scalar
latticeCurlSymbolAction primitives fld (pair mu nu) momentum =
  addScalar (operations (fourierAuthority primitives))
    (multiplyScalar (operations (fourierAuthority primitives))
      (forwardDifferenceSymbol primitives mu momentum)
      (fld nu momentum))
    (negateScalar (operations (fourierAuthority primitives))
      (multiplyScalar (operations (fourierAuthority primitives))
        (forwardDifferenceSymbol primitives nu momentum)
        (fld mu momentum)))

latticeCodifferentialSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  PlaquetteMomentumField L Scalar → AxisMomentumField L Scalar
latticeCodifferentialSymbolAction primitives fld axis momentum =
  sumAxesScalar primitives
    (λ nu →
      multiplyScalar (operations (fourierAuthority primitives))
        (backwardDifferenceSymbol primitives nu momentum)
        (fld (pair nu axis) momentum))

gaugeFixingSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → AxisMomentumField L Scalar
gaugeFixingSymbolAction primitives fld =
  latticeGradientSymbolAction primitives
    (latticeDivergenceSymbolAction primitives fld)

curlCodifferentialSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → AxisMomentumField L Scalar
curlCodifferentialSymbolAction primitives fld =
  latticeCodifferentialSymbolAction primitives
    (latticeCurlSymbolAction primitives fld)

scalarLaplacianSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  MomentumField L Scalar → MomentumField L Scalar
scalarLaplacianSymbolAction primitives fld momentum =
  sumAxesScalar primitives
    (λ axis →
      multiplyScalar (operations (fourierAuthority primitives))
        (backwardDifferenceSymbol primitives axis momentum)
        (multiplyScalar (operations (fourierAuthority primitives))
          (forwardDifferenceSymbol primitives axis momentum)
          (fld momentum)))

bondLaplacianSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → AxisMomentumField L Scalar
bondLaplacianSymbolAction primitives fld axis =
  scalarLaplacianSymbolAction primitives (fld axis)

latticeHodgeSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → AxisMomentumField L Scalar
latticeHodgeSymbolAction primitives fld axis momentum =
  addScalar (operations (fourierAuthority primitives))
    (curlCodifferentialSymbolAction primitives fld axis momentum)
    (gaugeFixingSymbolAction primitives fld axis momentum)

blockConstraintSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → AxisMomentumField L Scalar
blockConstraintSymbolAction = blockConstraintFourierOperatorPrimitive

referenceSymbolAction :
  ∀ {L Scalar Bound} →
  PeriodicDifferencePrimitives L Scalar Bound →
  AxisMomentumField L Scalar → AxisMomentumField L Scalar
referenceSymbolAction primitives fld axis momentum =
  addScalar (operations (fourierAuthority primitives))
    (latticeHodgeSymbolAction primitives fld axis momentum)
    (blockConstraintSymbolAction primitives fld axis momentum)

referenceSymbolFormula :
  ∀ {L Scalar Bound}
    (primitives : PeriodicDifferencePrimitives L Scalar Bound) →
  ∀ fld axis momentum →
  referenceSymbolAction primitives fld axis momentum ≡
  addScalar (operations (fourierAuthority primitives))
    (latticeHodgeSymbolAction primitives fld axis momentum)
    (blockConstraintSymbolAction primitives fld axis momentum)
referenceSymbolFormula primitives fld axis momentum = refl

------------------------------------------------------------------------
-- Exact standard Fourier intertwining theorem for these definitions.
------------------------------------------------------------------------

record PeriodicDifferenceFourierTheorems
    {L : Nat} {Scalar Bound : Set}
    (primitives : PeriodicDifferencePrimitives L Scalar Bound) : Set₁ where
  field
    forwardDifferenceFourierSymbol : ∀ axis fld momentum →
      finiteFourierTransformDefinition (fourierAuthority primitives)
        (forwardDifference primitives axis fld) momentum
      ≡ forwardDifferenceSymbolAction primitives axis
          (finiteFourierTransformDefinition
            (fourierAuthority primitives) fld) momentum

    backwardDifferenceFourierSymbol : ∀ axis fld momentum →
      finiteFourierTransformDefinition (fourierAuthority primitives)
        (backwardDifference primitives axis fld) momentum
      ≡ backwardDifferenceSymbolAction primitives axis
          (finiteFourierTransformDefinition
            (fourierAuthority primitives) fld) momentum

    latticeGradientFourierSymbol : ∀ fld axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (latticeGradient primitives fld) axis momentum
      ≡ latticeGradientSymbolAction primitives
          (finiteFourierTransformDefinition
            (fourierAuthority primitives) fld) axis momentum

    latticeDivergenceFourierSymbol : ∀ fld momentum →
      finiteFourierTransformDefinition (fourierAuthority primitives)
        (latticeDivergence primitives fld) momentum
      ≡ latticeDivergenceSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) fld) momentum

    latticeCurlFourierSymbol : ∀ fld pairIndex momentum →
      finiteFourierTransformDefinition (fourierAuthority primitives)
        (latticeCurl primitives fld pairIndex) momentum
      ≡ latticeCurlSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) fld)
          pairIndex momentum

    latticeCodifferentialFourierSymbol : ∀ fld axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (latticeCodifferential primitives fld) axis momentum
      ≡ latticeCodifferentialSymbolAction primitives
          (λ pairIndex →
            finiteFourierTransformDefinition (fourierAuthority primitives)
              (fld pairIndex))
          axis momentum

    gaugeFixingOperatorFourierSymbol : ∀ fld axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (gaugeFixingOperator primitives fld) axis momentum
      ≡ gaugeFixingSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) fld)
          axis momentum

    blockConstraintOperatorFourierSymbol : ∀ fld axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (blockConstraintOperator primitives fld) axis momentum
      ≡ blockConstraintSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) fld)
          axis momentum

    referenceHessianFourierSymbol : ∀ fld axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (referenceHessian primitives fld) axis momentum
      ≡ referenceSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) fld)
          axis momentum

    finiteFourierDiagonalizesScalarLaplacian : ∀ fld momentum →
      finiteFourierTransformDefinition (fourierAuthority primitives)
        (scalarLaplacian primitives fld) momentum
      ≡ scalarLaplacianSymbolAction primitives
          (finiteFourierTransformDefinition
            (fourierAuthority primitives) fld) momentum

    finiteFourierDiagonalizesBondLaplacian : ∀ fld axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (bondLaplacian primitives fld) axis momentum
      ≡ bondLaplacianSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) fld)
          axis momentum

    finiteFourierDiagonalizesGaugeFixingTerm : ∀ fld axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (gaugeFixingOperator primitives fld) axis momentum
      ≡ gaugeFixingSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) fld)
          axis momentum

    finiteFourierDiagonalizesBlockConstraintTerm : ∀ fld axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (blockConstraintOperator primitives fld) axis momentum
      ≡ blockConstraintSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) fld)
          axis momentum

    finiteFourierDiagonalizesReferenceLaplacian : ∀ fld axis momentum →
      bondFourierTransform (fourierAuthority primitives)
        (referenceHessian primitives fld) axis momentum
      ≡ referenceSymbolAction primitives
          (bondFourierTransform (fourierAuthority primitives) fld)
          axis momentum

open PeriodicDifferenceFourierTheorems public

periodicDifferenceDefinitionsLevel : ProofLevel
periodicDifferenceDefinitionsLevel = machineChecked

periodicDifferenceFourierTheoremsLevel : ProofLevel
periodicDifferenceFourierTheoremsLevel = standardImported

referenceSymbolFormulaLevel : ProofLevel
referenceSymbolFormulaLevel = machineChecked
