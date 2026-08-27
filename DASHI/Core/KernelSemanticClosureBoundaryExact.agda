module DASHI.Core.KernelSemanticClosureBoundaryExact where

------------------------------------------------------------------------
-- KERNEL CLOSURE != SEMANTIC CLOSURE
--
-- SOURCE CALIBRATION
-- Theodor W. Adorno, Negative Dialectics, Suhrkamp 1966; English trans.
-- E. B. Ashton, Continuum, 1973. ISBN 9780826401328. No DOI asserted.
--
-- Adorno motivates attention to non-identity and resistance to totalising
-- conceptual closure. DASHI does not claim to formalise the non-identical.
-- It records only the methodological boundary that successful regression/
-- kernel closure is not exhaustive semantic capture.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record CapstoneStatus : Set where
  constructor capstone-status
  field
    regressionClosed : Bool
    semanticallyExhaustive : Bool

open CapstoneStatus public

criticalCapstoneStatus : CapstoneStatus
criticalCapstoneStatus = capstone-status true false

criticalCapstoneRegressionClosed : regressionClosed criticalCapstoneStatus ≡ true
criticalCapstoneRegressionClosed = refl

criticalCapstoneNotSemanticallyExhaustive :
  semanticallyExhaustive criticalCapstoneStatus ≡ false
criticalCapstoneNotSemanticallyExhaustive = refl

record KernelSemanticClosureBoundary : Set where
  constructor kernel-semantic-closure-boundary
  field
    kernelClosureImpliesSemanticClosure : Bool
    kernelClosureImpliesSemanticClosureIsFalse :
      kernelClosureImpliesSemanticClosure ≡ false
    capstoneMeansExhaustiveCapture : Bool
    capstoneMeansExhaustiveCaptureIsFalse : capstoneMeansExhaustiveCapture ≡ false
    formalResidualProvesMetaphysicalNonIdentity : Bool
    formalResidualProvesMetaphysicalNonIdentityIsFalse :
      formalResidualProvesMetaphysicalNonIdentity ≡ false

canonicalKernelSemanticClosureBoundary : KernelSemanticClosureBoundary
canonicalKernelSemanticClosureBoundary =
  kernel-semantic-closure-boundary false refl false refl false refl
