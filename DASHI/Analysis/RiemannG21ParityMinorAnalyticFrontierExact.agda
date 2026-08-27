module DASHI.Analysis.RiemannG21ParityMinorAnalyticFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG21ActualZetaHeightSeparationBoundary as Height
import DASHI.Analysis.RiemannG21ScaledHyperbolicMonotonicityBridgeExact as Scaled
import DASHI.Analysis.RiemannG21TwoPointCovarianceShadowExact as Cov
import DASHI.Analysis.RiemannG21TwoHeightMomentRatioTargetExact as Moment
import DASHI.Analysis.RiemannG21SymmetricSampleBlockReductionExact as Block
import DASHI.Analysis.RiemannG21OffLinePoleQuotientTransversalityExact as Trans

data ParityFrontierArrow : Set where
  actualZetaStrictHeightSeparation : ParityFrontierArrow
  scaledXTanhXMonotonicity : ParityFrontierArrow
  scaledXCothXMonotonicity : ParityFrontierArrow
  coshRelativeOuterUpweight : ParityFrontierArrow
  sinhRelativeOuterUpweight : ParityFrontierArrow
  finiteCovarianceDecomposition : ParityFrontierArrow
  continuumMomentRatioSeparation : ParityFrontierArrow
  taylorRemainderToFiniteRadiusMinors : ParityFrontierArrow
  symmetricParityBlockReduction : ParityFrontierArrow
  parityMinorsToPoleQuotientTransversality : ParityFrontierArrow

data FrontierStatus : Set where
  sourceAudited : FrontierStatus
  structurallyDerived : FrontierStatus
  analyticOpen : FrontierStatus

record ParityFrontierEntry : Set where
  constructor parityFrontierEntry
  field
    arrow : ParityFrontierArrow
    status : FrontierStatus
    reading : String

open ParityFrontierEntry public

strictHeightEntry : ParityFrontierEntry
strictHeightEntry = parityFrontierEntry
  actualZetaStrictHeightSeparation sourceAudited
  "The actual-zeta companion definition uses 0 < Re rho < 1, so an off-line height |alpha| satisfies 0 < |alpha| < 1/2. The older abstract ZeroConfig retains only closed-strip bounds."

xTanhEntry : ParityFrontierEntry
xTanhEntry = parityFrontierEntry
  scaledXTanhXMonotonicity analyticOpen
  "Prove x -> x tanh x strictly increasing on x > 0. The standard derivative is tanh x + x sech^2 x > 0. This single scalar theorem supplies the cosh log-derivative ordering after x = height * radius."

xCothEntry : ParityFrontierEntry
xCothEntry = parityFrontierEntry
  scaledXCothXMonotonicity analyticOpen
  "Prove x -> x coth x strictly increasing on x > 0. The derivative reduces to (sinh x cosh x - x)/sinh^2 x > 0. This supplies the odd/sinh log-derivative ordering."

coshWeightEntry : ParityFrontierEntry
coshWeightEntry = parityFrontierEntry
  coshRelativeOuterUpweight analyticOpen
  "Use strict increase of x tanh x to show that raising height from |alpha| to 1/2 relatively upweights larger positive radius for the even cosh weight."

sinhWeightEntry : ParityFrontierEntry
sinhWeightEntry = parityFrontierEntry
  sinhRelativeOuterUpweight analyticOpen
  "Use strict increase of x coth x to prove the analogous relative outer upweighting for the positive odd-sector sinh weight."

finiteCovarianceEntry : ParityFrontierEntry
finiteCovarianceEntry = parityFrontierEntry
  finiteCovarianceDecomposition structurallyDerived
  "The two-support cross-multiplied mean difference is exactly delta-q times the relative-weight determinant; the owning theorem is proved by rational ring normalization in RiemannG21TwoPointCovarianceShadowExact."

momentRatioEntry : ParityFrontierEntry
momentRatioEntry = parityFrontierEntry
  continuumMomentRatioSeparation analyticOpen
  "Lift relative weight monotonicity from finite covariance to the source taper integrals, obtaining nonzero even and odd moment cross-products between heights |alpha| and 1/2."

remainderEntry : ParityFrontierEntry
remainderEntry = parityFrontierEntry
  taylorRemainderToFiniteRadiusMinors analyticOpen
  "Control the small-radius expansion remainder strongly enough that moment-ratio separation yields nonzero parity minors at two explicit symmetric sample radii."

blockEntry : ParityFrontierEntry
blockEntry = parityFrontierEntry
  symmetricParityBlockReduction structurallyDerived
  "The four-sample conjugate-height exterior problem has been reduced to independent even and odd 2x2 minor admission conditions; one sector alone is insufficient."

transversalityEntry : ParityFrontierEntry
transversalityEntry = parityFrontierEntry
  parityMinorsToPoleQuotientTransversality analyticOpen
  "After the literal nuisance-space transport is fixed, combine both actual nonzero parity minors into the full off-line rank-two response modulo the nuisance span."

canonicalParityFrontier : List ParityFrontierEntry
canonicalParityFrontier =
  strictHeightEntry ∷ xTanhEntry ∷ xCothEntry
  ∷ coshWeightEntry ∷ sinhWeightEntry
  ∷ finiteCovarianceEntry ∷ momentRatioEntry ∷ remainderEntry
  ∷ blockEntry ∷ transversalityEntry ∷ []

strictHeightBoundary : Height.ActualZetaHeightBoundary
strictHeightBoundary = Height.canonicalActualZetaHeightBoundary

scaledHyperbolicBoundary : Scaled.ScaledHyperbolicMonotonicityBoundary
scaledHyperbolicBoundary = Scaled.canonicalScaledHyperbolicMonotonicityBoundary

momentCriterionWitness : Moment.CrossProductSeparation
momentCriterionWitness = Moment.canonicalMomentCrossProductSeparation

parityBlockWitness : Block.SymmetricSampleTwoHeightAdmission
parityBlockWitness = Block.canonicalSymmetricSampleAdmission

transversalityCriterionWitness : Trans.OffLinePoleQuotientTransversality
transversalityCriterionWitness = Trans.canonicalToyTransversality

record ParityAnalyticFrontierBoundary : Set where
  constructor parityAnalyticFrontierBoundary
  field
    strictActualZetaHeightSeparationAvailable : Bool
    strictActualZetaHeightSeparationAvailableIsTrue :
      strictActualZetaHeightSeparationAvailable ≡ true
    scaledLogDerivativeReductionDerived : Bool
    scaledLogDerivativeReductionDerivedIsTrue :
      scaledLogDerivativeReductionDerived ≡ true
    finiteCovarianceAlgebraDerived : Bool
    finiteCovarianceAlgebraDerivedIsTrue : finiteCovarianceAlgebraDerived ≡ true
    parityBlockReductionDerived : Bool
    parityBlockReductionDerivedIsTrue : parityBlockReductionDerived ≡ true
    actualXTanhXMonotonicityDerived : Bool
    actualXTanhXMonotonicityDerivedIsFalse : actualXTanhXMonotonicityDerived ≡ false
    actualXCothXMonotonicityDerived : Bool
    actualXCothXMonotonicityDerivedIsFalse : actualXCothXMonotonicityDerived ≡ false
    actualCoshWeightMonotonicityDerived : Bool
    actualCoshWeightMonotonicityDerivedIsFalse : actualCoshWeightMonotonicityDerived ≡ false
    actualSinhWeightMonotonicityDerived : Bool
    actualSinhWeightMonotonicityDerivedIsFalse : actualSinhWeightMonotonicityDerived ≡ false
    actualMomentRatioSeparationDerived : Bool
    actualMomentRatioSeparationDerivedIsFalse : actualMomentRatioSeparationDerived ≡ false
    finiteRadiusParityMinorsDerived : Bool
    finiteRadiusParityMinorsDerivedIsFalse : finiteRadiusParityMinorsDerived ≡ false

canonicalParityAnalyticFrontierBoundary : ParityAnalyticFrontierBoundary
canonicalParityAnalyticFrontierBoundary =
  parityAnalyticFrontierBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
