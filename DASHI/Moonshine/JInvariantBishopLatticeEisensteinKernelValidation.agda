module DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as P

reciprocalCancellationRegression :
  ∀ z (nz : Reciprocal.BishopComplexNonzero z) →
  Complex._≈C_
    (Algebra._*C_ z (Reciprocal.reciprocalC z nz))
    Algebra.oneC
reciprocalCancellationRegression =
  Reciprocal.multiplyReciprocal

literalSummandRegression :
  ∀ {Parameter tauOf}
    (geometry : P.BishopLatticeDenominatorGeometry Parameter tauOf)
    (weight : Nat)
    (index : P.NonzeroLatticePoint)
    (parameter : Parameter) →
  P.latticeEisensteinSummand geometry weight index parameter
  ≡
  Algebra.powC
    (P.latticeReciprocal geometry parameter index)
    weight
literalSummandRegression geometry weight index parameter = refl

integerEmbeddingPaidRegression :
  P.concreteIntegerEmbeddingConstructed
    P.canonicalBishopLiteralLatticeKernelBoundary
  ≡ true
integerEmbeddingPaidRegression = refl

literalKernelPaidRegression :
  P.literalInversePowerSummandConstructed
    P.canonicalBishopLiteralLatticeKernelBoundary
  ≡ true
literalKernelPaidRegression = refl

denominatorGeometryStillOpenRegression :
  P.upperHalfPlaneDenominatorNonzeroProvedHere
    P.canonicalBishopLiteralLatticeKernelBoundary
  ≡ false
denominatorGeometryStillOpenRegression = refl

absoluteSummabilityStillOpenRegression :
  P.z2AbsoluteSummabilityProvedHere
    P.canonicalBishopLiteralLatticeKernelBoundary
  ≡ false
absoluteSummabilityStillOpenRegression = refl
