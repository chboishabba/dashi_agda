module DASHI.Analysis.MarxFastCauchyDerivativeCompletion where

open import Agda.Primitive using (Set₁)

open import DASHI.Analysis.MarxFastCauchyCompletionCutset
open import DASHI.Analysis.MarxOrdinaryDerivativeBridge

------------------------------------------------------------------------
-- Final analytic cutset for the selected fast-Cauchy quotient real.
--
-- The finite Marx algebra and the analytic derivative are indexed by the same
-- selected quotient carrier.  This prevents a factorisation theorem on one
-- real implementation from being combined with a limit/uniqueness theorem on
-- another.

record FastCauchyMarxDerivativeCompletion : Set₁ where
  field
    completion : FastCauchyMarxCompletionData

    remainderStructure :
      RemainderDerivativeStructure
        (selectedFastCauchyMarxAlgebra completion)

    expansionLaws :
      MarxRemainderExpansionLaws
        (selectedFastCauchyMarxAlgebra completion)

    derivativeUniqueness :
      OrdinaryDerivativeUniqueness remainderStructure

open FastCauchyMarxDerivativeCompletion public

selectedFastCauchyDerivativeSeam :
  FastCauchyMarxDerivativeCompletion →
  ConstructiveRealDerivativeSeam
selectedFastCauchyDerivativeSeam D =
  record
    { algebra = selectedFastCauchyMarxAlgebra (completion D)
    ; remainderStructure = remainderStructure D
    ; expansionLaws = expansionLaws D
    ; uniqueness = derivativeUniqueness D
    }

selectedFastCauchyCompatibilityAuthority :
  (D : FastCauchyMarxDerivativeCompletion) →
  MarxOrdinaryCompatibilityAuthority (remainderStructure D)
selectedFastCauchyCompatibilityAuthority D =
  record
    { expansionLaws = expansionLaws D
    ; derivativeUniqueness = derivativeUniqueness D
    }

-- Once this record is inhabited, every Marx factorisation whose preliminary
-- function is continuous at the diagonal obtains an ordinary little-o
-- derivative on the same nondegenerate fast-Cauchy real, and derivative
-- uniqueness identifies the two coefficients.
