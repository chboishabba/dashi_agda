module DASHI.Physics.Closure.HEPDataT45BinIntegrationDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- HEP-R48: t45 bin-width integration diagnostic.
--
-- HEP-R47 left a well-characterised high-mass shape residual:
-- t45 chi2/dof = 16.1225593070 with mean pred/data = 0.9587136559.
-- HEP-R48 tests the governance-clean hypothesis that wide phi* bins were
-- being biased by midpoint evaluation.  The implementation switches the
-- prediction ratio to fixed five-point Gauss-Legendre bin integration.
--
-- Result: this is not the dominant residual.  t45 improves only slightly
-- to chi2/dof = 15.8545837677; t43 remains below the comparison threshold
-- but worsens to chi2/dof = 2.1565191176.  Therefore this surface is a
-- non-promoting precision diagnostic and the remaining blocker is a genuine
-- above-Z shape-kernel gap.

data QuadratureMethod : Set where
  gaussLegendre5Point : QuadratureMethod

record WideBin : Set where
  field
    low : Float
    high : Float
    width : Float

record HEPDataT45BinIntegrationDiagnostic : Set where
  field
    integrationMethod : QuadratureMethod
    implementationSurface : String

    wideBinOne : WideBin
    wideBinTwo : WideBin

    t43Chi2Before : Float
    t45Chi2Before : Float
    t45MeanPredDataBefore : Float

    t43Chi2After : Float
    t45Chi2After : Float
    t45MeanPredDataAfter : Float

    t43StillPassesDiagnosticThreshold : Bool
    t45StillFailsDiagnosticThreshold : Bool
    wideBinHypothesisDominant : Bool

    remainingGap : String

    -- Explicit governance boundary.
    statusNonPromoting : ⊤
    noPromotion : ⊤

canonicalHEPDataT45BinIntegrationDiagnostic :
  HEPDataT45BinIntegrationDiagnostic
canonicalHEPDataT45BinIntegrationDiagnostic =
  record
    { integrationMethod = gaussLegendre5Point
    ; implementationSurface =
        "DASHI.Physics.Prediction.sigma_dashi:_bin_integrated_prediction_ratio"
    ; wideBinOne =
        record { low = 0.524 ; high = 1.153 ; width = 0.629 }
    ; wideBinTwo =
        record { low = 1.153 ; high = 3.277 ; width = 2.124 }
    ; t43Chi2Before = 1.7408778006
    ; t45Chi2Before = 16.1225593070
    ; t45MeanPredDataBefore = 0.9587136559
    ; t43Chi2After = 2.1565191176
    ; t45Chi2After = 15.8545837677
    ; t45MeanPredDataAfter = 0.9581222335
    ; t43StillPassesDiagnosticThreshold = true
    ; t45StillFailsDiagnosticThreshold = true
    ; wideBinHypothesisDominant = false
    ; remainingGap =
        "above-Z high-mass phi-star shape kernel; not resolved by bin-width integration"
    ; statusNonPromoting = tt
    ; noPromotion = tt
    }

canonicalHEPDataT45BinIntegrationNoPromotion :
  HEPDataT45BinIntegrationDiagnostic.noPromotion
    canonicalHEPDataT45BinIntegrationDiagnostic
    ≡ tt
canonicalHEPDataT45BinIntegrationNoPromotion = refl
