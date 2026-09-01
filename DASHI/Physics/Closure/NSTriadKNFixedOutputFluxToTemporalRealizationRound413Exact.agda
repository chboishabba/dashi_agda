module DASHI.Physics.Closure.NSTriadKNFixedOutputFluxToTemporalRealizationRound413Exact where

------------------------------------------------------------------------
-- ROUND413 / BIDI TEMPORAL COMPILER TARGET
--
-- This owner records the exact intended composition:
--
--   R406 fixed-output instantaneous identity
--     + R409 actual scalar derivative of the SAME flux
--     + ordinary real FTC/integration laws
--   -> R393 literal temporal realization.
--
-- No replacement observable and no replacement debt are admitted.  The only
-- missing mathematics in this composition is ordinary scalar analysis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

round413UsesSameR406Flux : Bool
round413UsesSameR406Flux = true

round413UsesSameLiteralR378Debt : Bool
round413UsesSameLiteralR378Debt = true

round413NeedsOnlyScalarDerivativeAndFTC : Bool
round413NeedsOnlyScalarDerivativeAndFTC = true

round413IntroducesNewNSCancellationEstimate : Bool
round413IntroducesNewNSCancellationEstimate = false

round413UsesSameR406FluxIsTrue : round413UsesSameR406Flux ≡ true
round413UsesSameR406FluxIsTrue = refl

round413IntroducesNewNSCancellationEstimateIsFalse :
  round413IntroducesNewNSCancellationEstimate ≡ false
round413IntroducesNewNSCancellationEstimateIsFalse = refl
