module DASHI.Physics.Closure.PDFCarrierLogRatioDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- W5 PDF-carrier nearest-path diagnostic.
--
-- This is a numeric, non-promoting diagnostic for the high-mass t45
-- neutral-current/PDF carrier gap.  It records the required correction from
-- the current local mass-kernel diagnostic and compares it with the nearest
-- repo-native pressure-shaped proxy.  The proxy is intentionally not treated
-- as a derivation: it has no PDF table, no parton luminosity carrier, and no
-- GR/QFT promotion authority.

data PDFCarrierRouteStatus : Set where
  numericallySuggestiveButUnderived :
    PDFCarrierRouteStatus
  externallyPDFGated :
    PDFCarrierRouteStatus

record PDFCarrierLogRatioDiagnostic : Set where
  field
    observedT45Mean :
      Float

    neutralCurrentT45Mean :
      Float

    requiredT45Correction :
      Float

    requiredLogCorrection :
      Float

    trackedPrimeLaneCount :
      Nat

    pressureUnitsTested :
      Nat

    primeWeightedLogProxy :
      Float

    proxyCorrectionFactor :
      Float

    absoluteCorrectionGap :
      Float

    relativeCorrectionGap :
      Float

    absoluteLogGap :
      Float

    proxyNumericallyClose :
      Bool

    internalDerivationAvailable :
      Bool

    routeStatus :
      PDFCarrierRouteStatus

    diagnosticNotes :
      List String

    -- Explicit governance boundary.
    noPDFCarrierConstructed :
      ⊤

    noClosurePromotion :
      ⊤

canonicalPDFCarrierLogRatioDiagnostic :
  PDFCarrierLogRatioDiagnostic
canonicalPDFCarrierLogRatioDiagnostic =
  record
    { observedT45Mean =
        0.026288
    ; neutralCurrentT45Mean =
        0.0298575065
    ; requiredT45Correction =
        0.8804486068
    ; requiredLogCorrection =
        -0.1273237210
    ; trackedPrimeLaneCount =
        15
    ; pressureUnitsTested =
        2
    ; primeWeightedLogProxy =
        -0.1333333333
    ; proxyCorrectionFactor =
        0.8751733190
    ; absoluteCorrectionGap =
        0.0052752877
    ; relativeCorrectionGap =
        0.0059915908
    ; absoluteLogGap =
        0.0060096124
    ; proxyNumericallyClose =
        true
    ; internalDerivationAvailable =
        false
    ; routeStatus =
        externallyPDFGated
    ; diagnosticNotes =
        "requiredT45Correction = observed t45 mean / current neutral-current t45 mean"
        ∷ "primeWeightedLogProxy tests a two-pressure-unit attenuation over the canonical 15-prime carrier"
        ∷ "the proxy is close in log space, but it is not a PDF carrier derivation"
        ∷ "missing prerequisite remains an external PDF/parton-luminosity carrier or an equivalent typed mass-kernel route"
        ∷ []
    ; noPDFCarrierConstructed =
        tt
    ; noClosurePromotion =
        tt
    }

canonicalPDFCarrierLogRatioNoPromotion :
  PDFCarrierLogRatioDiagnostic.noClosurePromotion
    canonicalPDFCarrierLogRatioDiagnostic
    ≡ tt
canonicalPDFCarrierLogRatioNoPromotion = refl
