module DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceCoreExact where

-- Sources: K. Wilson, Phys. Rev. D 10 (1974) 2445-2459,
-- DOI 10.1103/PhysRevD.10.2445; T. Balaban, CMP 99 (1985) 75-102,
-- DOI 10.1007/BF01466594.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN

record SUNMatrixRealTrace
    {Matrix Complex Scalar : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) : Set₁ where
  field
    normalizedRealTrace : Matrix → Scalar
    traceCyclic : ∀ A B →
      normalizedRealTrace
        (SUN.multiplyM (SUN.operations theory) A B)
      ≡
      normalizedRealTrace
        (SUN.multiplyM (SUN.operations theory) B A)

open SUNMatrixRealTrace public

matrixWilsonValue :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex} →
  SUNMatrixRealTrace theory → SUN.SUNMatrixElement theory → Scalar
matrixWilsonValue traceData U =
  normalizedRealTrace traceData (SUN.matrix U)
