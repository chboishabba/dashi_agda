module DASHI.Analysis.RiemannG21ParityMinorAnalyticFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG21ActualZetaHeightSeparationBoundary as Height
import DASHI.Analysis.RiemannG21ScaledHyperbolicMonotonicityBridgeExact as Scaled
import DASHI.Analysis.RiemannG21MathlibHyperbolicReceiptBoundary as MathlibReceipt
import DASHI.Analysis.RiemannG21EvenHyperbolicAlgebraicRouteExact as Even
import DASHI.Analysis.StrictKernelMomentRatioExact as TP2
import DASHI.Analysis.RiemannG21OddSinhTP2Exact as OddTP2
import DASHI.Analysis.RiemannG21TwoPointCovarianceShadowExact as Cov
import DASHI.Analysis.RiemannG21TwoHeightMomentRatioTargetExact as Moment
import DASHI.Analysis.RiemannG21DeterminantMarginTransferExact as Margin
import DASHI.Analysis.RiemannG21SymmetricSampleBlockReductionExact as Block
import DASHI.Analysis.RiemannG21OffLinePoleQuotientTransversalityExact as Trans

data ParityFrontierArrow : Set where
  actualZetaStrictHeightSeparation : ParityFrontierArrow
  mathlibAtomicHyperbolicTheoremsLocated : ParityFrontierArrow
  scaledXTanhXMonotonicity : ParityFrontierArrow
  scaledXCothXMonotonicity : ParityFrontierArrow
  evenProductToSumRoute : ParityFrontierArrow
  strictSinhTP2 : ParityFrontierArrow
  strictKernelMomentComposition : ParityFrontierArrow
  oddMomentDeterminantStrictSign : ParityFrontierArrow
  directDeterminantMarginTransfer : ParityFrontierArrow
  finiteCovarianceDecomposition : ParityFrontierArrow
  continuumEvenMomentRatioSeparation : ParityFrontierArrow
  finiteRadiusParityMinors : ParityFrontierArrow
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
  "The actual-zeta companion definition uses 0 < Re rho < 1, so an off-line height |alpha| satisfies 0 < |alpha| < 1/2."

mathlibReceiptEntry : ParityFrontierEntry
mathlibReceiptEntry = parityFrontierEntry
  mathlibAtomicHyperbolicTheoremsLocated sourceAudited
  "Mathlib owns Real.self_lt_sinh_iff, Real.sinh_pos_iff, Real.cosh_pos, Real.tanh_eq_sinh_div_cosh and Real.sinh_two_mul. These are external machine-checked facts, not Agda theorems until transported or independently reproved."

xTanhEntry : ParityFrontierEntry
xTanhEntry = parityFrontierEntry
  scaledXTanhXMonotonicity analyticOpen
  "Optional even-sector calculus route: prove x -> x tanh x strictly increasing on x > 0. The even sector now also has a direct product-to-sum route, so this is no longer on the critical path."

xCothEntry : ParityFrontierEntry
xCothEntry = parityFrontierEntry
  scaledXCothXMonotonicity analyticOpen
  "Odd-sector calculus route: prove x -> x coth x strictly increasing on x > 0. Its derivative sign reduces to sinh(2x)>2x, with the atomic Lean facts already source-audited."

evenRouteEntry : ParityFrontierEntry
evenRouteEntry = parityFrontierEntry
  evenProductToSumRoute structurallyDerived
  "The even/cosh TP2 minor has a derivative-free product-to-sum reduction using (p-a)(v-u)>0 and (pv-au)^2-(pu-av)^2=(p^2-a^2)(v^2-u^2)>0. Ordered-real cosh monotonicity is still an analytic instantiation."

sinhTP2Entry : ParityFrontierEntry
sinhTP2Entry = parityFrontierEntry
  strictSinhTP2 analyticOpen
  "Prove the strict positive-quadrant TP2 inequality sinh(pv)sinh(au) > sinh(pu)sinh(av) for 0<a<p and 0<u<v. This is the atomic odd kernel theorem."

kernelCompositionEntry : ParityFrontierEntry
kernelCompositionEntry = parityFrontierEntry
  strictKernelMomentComposition structurallyDerived
  "StrictKernelMomentRatioExact now owns the generic TP2 -> strict moment-cross-product theorem shape, signed determinant orientation, and an exact finite two-support regression. The continuum integral theorem remains a producer obligation."

oddMomentEntry : ParityFrontierEntry
oddMomentEntry = parityFrontierEntry
  oddMomentDeterminantStrictSign analyticOpen
  "Use strict sinh TP2 plus positive nondegenerate taper support in the symmetrized double-integral identity to prove N1(a)N3(p) > N3(a)N1(p), equivalently the previous G21 odd determinant orientation is strictly negative."

marginEntry : ParityFrontierEntry
marginEntry = parityFrontierEntry
  directDeterminantMarginTransfer structurallyDerived
  "The Taylor stage is now formulated against one continuum determinant margin: prove |D_R-Delta_odd| < Delta_odd rather than four independent entrywise estimates. The interface is constructed; the actual remainder theorem remains open."

finiteCovarianceEntry : ParityFrontierEntry
finiteCovarianceEntry = parityFrontierEntry
  finiteCovarianceDecomposition structurallyDerived
  "The earlier two-support covariance identity remains an exact finite shadow and regression of the same TP2 composition mechanism, but is no longer a separate conceptual gate."

evenMomentEntry : ParityFrontierEntry
evenMomentEntry = parityFrontierEntry
  continuumEvenMomentRatioSeparation analyticOpen
  "Instantiate the even/cosh strict-kernel route with the positive taper measure to obtain its signed moment determinant. This can share the generic TP2 moment-composition owner."

finiteRadiusEntry : ParityFrontierEntry
finiteRadiusEntry = parityFrontierEntry
  finiteRadiusParityMinors analyticOpen
  "Use direct determinant-margin error control to preserve the strict continuum signs at two explicit symmetric sample radii."

blockEntry : ParityFrontierEntry
blockEntry = parityFrontierEntry
  symmetricParityBlockReduction structurallyDerived
  "The four-sample conjugate-height exterior problem reduces to independent even and odd 2x2 minor admission conditions; one sector alone remains insufficient."

transversalityEntry : ParityFrontierEntry
transversalityEntry = parityFrontierEntry
  parityMinorsToPoleQuotientTransversality analyticOpen
  "After the literal nuisance-space transport is fixed, combine both actual signed parity minors into full off-line rank-two response modulo the nuisance span."

canonicalParityFrontier : List ParityFrontierEntry
canonicalParityFrontier =
  strictHeightEntry ∷ mathlibReceiptEntry
  ∷ xTanhEntry ∷ xCothEntry ∷ evenRouteEntry
  ∷ sinhTP2Entry ∷ kernelCompositionEntry ∷ oddMomentEntry
  ∷ marginEntry ∷ finiteCovarianceEntry ∷ evenMomentEntry
  ∷ finiteRadiusEntry ∷ blockEntry ∷ transversalityEntry ∷ []

strictHeightBoundary : Height.ActualZetaHeightBoundary
strictHeightBoundary = Height.canonicalActualZetaHeightBoundary

scaledHyperbolicBoundary : Scaled.ScaledHyperbolicMonotonicityBoundary
scaledHyperbolicBoundary = Scaled.canonicalScaledHyperbolicMonotonicityBoundary

mathlibHyperbolicReceiptBoundary : MathlibReceipt.MathlibHyperbolicReceiptBoundary
mathlibHyperbolicReceiptBoundary = MathlibReceipt.canonicalMathlibHyperbolicReceiptBoundary

evenAlgebraicBoundary : Even.EvenHyperbolicAlgebraicBoundary
evenAlgebraicBoundary = Even.canonicalEvenHyperbolicAlgebraicBoundary

genericTP2Boundary : TP2.StrictKernelMomentRatioBoundary
genericTP2Boundary = TP2.canonicalStrictKernelMomentRatioBoundary

oddTP2Boundary : OddTP2.OddSinhTP2Boundary
oddTP2Boundary = OddTP2.canonicalOddSinhTP2Boundary

marginTransferBoundary : Margin.DeterminantMarginBoundary
marginTransferBoundary = Margin.canonicalDeterminantMarginBoundary

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
    strictActualZetaHeightSeparationAvailableIsTrue : strictActualZetaHeightSeparationAvailable ≡ true
    mathlibAtomicHyperbolicTheoremsLocated : Bool
    mathlibAtomicHyperbolicTheoremsLocatedIsTrue : mathlibAtomicHyperbolicTheoremsLocated ≡ true
    scaledLogDerivativeReductionDerived : Bool
    scaledLogDerivativeReductionDerivedIsTrue : scaledLogDerivativeReductionDerived ≡ true
    evenProductToSumReductionDerived : Bool
    evenProductToSumReductionDerivedIsTrue : evenProductToSumReductionDerived ≡ true
    genericStrictTP2MomentOwnerConstructed : Bool
    genericStrictTP2MomentOwnerConstructedIsTrue : genericStrictTP2MomentOwnerConstructed ≡ true
    directDeterminantMarginInterfaceConstructed : Bool
    directDeterminantMarginInterfaceConstructedIsTrue : directDeterminantMarginInterfaceConstructed ≡ true
    finiteCovarianceAlgebraDerived : Bool
    finiteCovarianceAlgebraDerivedIsTrue : finiteCovarianceAlgebraDerived ≡ true
    parityBlockReductionDerived : Bool
    parityBlockReductionDerivedIsTrue : parityBlockReductionDerived ≡ true
    actualSinhTP2Derived : Bool
    actualSinhTP2DerivedIsFalse : actualSinhTP2Derived ≡ false
    actualOddMomentStrictSignDerived : Bool
    actualOddMomentStrictSignDerivedIsFalse : actualOddMomentStrictSignDerived ≡ false
    actualEvenMomentStrictSignDerived : Bool
    actualEvenMomentStrictSignDerivedIsFalse : actualEvenMomentStrictSignDerived ≡ false
    finiteRadiusParityMinorsDerived : Bool
    finiteRadiusParityMinorsDerivedIsFalse : finiteRadiusParityMinorsDerived ≡ false

canonicalParityAnalyticFrontierBoundary : ParityAnalyticFrontierBoundary
canonicalParityAnalyticFrontierBoundary =
  parityAnalyticFrontierBoundary
    true refl true refl true refl true refl true refl true refl true refl true refl
    false refl false refl false refl false refl
