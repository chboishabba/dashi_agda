module DASHI.Programmes.FRACDASHCompilerCorrectionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- BIDI cut for FRACDASH.
--
-- The satellite already identifies the correct compiler theorem: an exact
-- one-step commuting square between source and executable semantics.  Once that
-- receipt is supplied, finite-trace correctness is downstream induction rather
-- than a second experimental obligation.
------------------------------------------------------------------------

iterate : ∀ {State : Set} → Nat → (State → State) → State → State
iterate zero step state = state
iterate (suc n) step state = step (iterate n step state)

record OneStepCompiler
    (Source Target : Set)
    (sourceStep : Source → Source)
    (targetStep : Target → Target) : Set₁ where
  constructor oneStepCompiler
  field
    compile : Source → Target
    oneStepCommutes :
      (state : Source) →
      compile (sourceStep state) ≡ targetStep (compile state)

open OneStepCompiler public

finiteTraceCommutes :
  ∀ {Source Target : Set}
    {sourceStep : Source → Source}
    {targetStep : Target → Target}
    (compiler : OneStepCompiler Source Target sourceStep targetStep)
    (n : Nat)
    (state : Source) →
  compile compiler (iterate n sourceStep state) ≡
  iterate n targetStep (compile compiler state)
finiteTraceCommutes compiler zero state = refl
finiteTraceCommutes {sourceStep = sourceStep} {targetStep = targetStep}
    compiler (suc n) state =
  trans
    (oneStepCommutes compiler (iterate n sourceStep state))
    (cong targetStep (finiteTraceCommutes compiler n state))

------------------------------------------------------------------------
-- Decoder/source-readout correctness composes with finite simulation.
------------------------------------------------------------------------

record ObservableCompiler
    (Source Target Observation : Set)
    (sourceStep : Source → Source)
    (targetStep : Target → Target) : Set₁ where
  constructor observableCompiler
  field
    stepCompiler : OneStepCompiler Source Target sourceStep targetStep
    decode : Target → Observation
    sourceReadout : Source → Observation
    readoutCommutes :
      (state : Source) →
      decode (compile stepCompiler state) ≡ sourceReadout state

open ObservableCompiler public

finiteTraceReadoutCorrect :
  ∀ {Source Target Observation : Set}
    {sourceStep : Source → Source}
    {targetStep : Target → Target}
    (compiler : ObservableCompiler Source Target Observation sourceStep targetStep)
    (n : Nat)
    (state : Source) →
  decode compiler
    (iterate n targetStep
      (compile (stepCompiler compiler) state))
  ≡
  sourceReadout compiler (iterate n sourceStep state)
finiteTraceReadoutCorrect {sourceStep = sourceStep} compiler n state =
  trans
    (cong (decode compiler)
      (sym (finiteTraceCommutes (stepCompiler compiler) n state)))
    (readoutCommutes compiler (iterate n sourceStep state))

record FRACDASHCompilerCorrectionBoundary : Set where
  constructor fracdashCompilerCorrectionBoundary
  field
    benchmarkParityIsCompilerCorrectness : Bool
    benchmarkParityIsCompilerCorrectnessIsFalse :
      benchmarkParityIsCompilerCorrectness ≡ false

    oneStepCommutationYieldsFiniteTraceCommutation : Bool
    oneStepCommutationYieldsFiniteTraceCommutationIsTrue :
      oneStepCommutationYieldsFiniteTraceCommutation ≡ true

    invariantSurrogateIsExactDecoderSemantics : Bool
    invariantSurrogateIsExactDecoderSemanticsIsFalse :
      invariantSurrogateIsExactDecoderSemantics ≡ false

canonicalFRACDASHCompilerCorrectionBoundary :
  FRACDASHCompilerCorrectionBoundary
canonicalFRACDASHCompilerCorrectionBoundary =
  fracdashCompilerCorrectionBoundary
    false refl
    true refl
    false refl
