module DASHI.Analysis.RiemannG21ParityMinorAnalyticFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG21ActualZetaHeightSeparationBoundary as Height
import DASHI.Analysis.RiemannG21TwoPointCovarianceShadowExact as Cov
import DASHI.Analysis.RiemannG21TwoHeightMomentRatioTargetExact as Moment
import DASHI.Analysis.RiemannG21SymmetricSampleBlockReductionExact as Block
import DASHI.Analysis.RiemannG21OffLinePoleQuotientTransversalityExact as Trans

------------------------------------------------------------------------
-- Exact ownership map for the zero-side analytic frontier.
------------------------------------------------------------------------

data ParityFrontierArrow : Set where
  actualZetaStrictHeightSeparation : ParityFrontierArrow
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
  "The actual-zeta companion definition uses 0 < Re rho < 1, so off-line height |alpha| is strictly below pole height 1/2. The older abstract ZeroConfig retains only closed-strip bounds."

coshWeightEntry : ParityFrontierEntry
coshWeightEntry = parityFrontierEntry
  coshRelativeOuterUpweight analyticOpen
  "Prove that raising height from |alpha| to 1/2 relatively upweights larger positive radius for the even cosh weight. This is the monotone-likelihood-ratio input for the even moment ratio."

sinhWeightEntry : ParityFrontierEntry
sinhWeightEntry = parityFrontierEntry
  sinhRelativeOuterUpweight analyticOpen
  "Prove the analogous relative outer upweighting for the positive odd-sector sinh weight. It is a separate theorem from the even/cosh statement."

finiteCovarianceEntry : ParityFrontierEntry
finiteCovarianceEntry = parityFrontierEntry
  finiteCovarianceDecomposition structurallyDerived
  "The two-support cross-multiplied mean difference is exactly delta-q times the relative-weight determinant; this is proved by rational ring normalization."

momentRatioEntry : ParityFrontierEntry
momentRatioEntry = parityFrontierEntry
  continuumMomentRatioSeparation analyticOpen
  "Lift relative weight monotonicity from finite covariance to the source taper integrals, obtaining nonzero cross-products M2(alpha)M0(1/2)-M0(alpha)M2(1/2) and N3(alpha)N1(1/2)-N1(alpha)N3(1/2)."

remainderEntry : ParityFrontierEntry
remainderEntry = parityFrontierEntry
  taylorRemainderToFiniteRadiusMinors analyticOpen
  "Control the r-expansion remainder strongly enough that moment-ratio separation yields nonzero parity minors at two explicit finite symmetric sample radii."

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
  strictHeightEntry
  ∷ coshWeightEntry
  ∷ sinhWeightEntry
  ∷ finiteCovarianceEntry
  ∷ momentRatioEntry
  ∷ remainderEntry
  ∷ blockEntry
  ∷ transversalityEntry
  ∷ []

------------------------------------------------------------------------
-- Concrete structural returns from the constituent owners.
------------------------------------------------------------------------

strictHeightBoundary : Height.ActualZetaHeightBoundary
strictHeightBoundary = Height.canonicalActualZetaHeightBoundary

finiteMomentCrossProductIdentity = Cov.twoPointMomentCrossProductDecomposition

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

    finiteCovarianceAlgebraDerived : Bool
    finiteCovarianceAlgebraDerivedIsTrue : finiteCovarianceAlgebraDerived ≡ true

    parityBlockReductionDerived : Bool
    parityBlockReductionDerivedIsTrue : parityBlockReductionDerived ≡ true

    actualCoshWeightMonotonicityDerived : Bool
    actualCoshWeightMonotonicityDerivedIsFalse :
      actualCoshWeightMonotonicityDerived ≡ false

    actualSinhWeightMonotonicityDerived : Bool
    actualSinhWeightMonotonicityDerivedIsFalse :
      actualSinhWeightMonotonicityDerived ≡ false

    actualMomentRatioSeparationDerived : Bool
    actualMomentRatioSeparationDerivedIsFalse :
      actualMomentRatioSeparationDerived ≡ false

    finiteRadiusParityMinorsDerived : Bool
    finiteRadiusParityMinorsDerivedIsFalse :
      finiteRadiusParityMinorsDerived ≡ false

canonicalParityAnalyticFrontierBoundary : ParityAnalyticFrontierBoundary
canonicalParityAnalyticFrontierBoundary =
  parityAnalyticFrontierBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
