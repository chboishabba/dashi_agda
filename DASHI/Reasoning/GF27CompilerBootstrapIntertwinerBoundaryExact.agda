module DASHI.Reasoning.GF27CompilerBootstrapIntertwinerBoundaryExact where

------------------------------------------------------------------------
-- GF(27) / COMPILER-BOOTSTRAP INTERTWINER BOUNDARY
--
-- The repository already owns the exact Frobenius orbit arithmetic
--
--   27 = 3 fixed + 8 * 3-cycle
--
-- and explicitly records the supplied compiler-bootstrap picture as an
-- analogy rather than a semantic identification.  This owner states the
-- exact additional object required to promote that analogy:
--
--   compiler state --compile--> compiler state
--        |                         |
--      encode                    encode
--        v                         v
--   GF(27) state --Frob_3--> GF(27) state.
--
-- A real compiler/bootstrap claim therefore needs an actual finite compiler
-- carrier, an actual compile transition, an observation/quotient identifying
-- the compared states, and the commutative square below.  Finite-field orbit
-- arithmetic alone cannot inhabit this interface.
--
-- EXECUTABLE PRESENTATION NOTE:
-- `scripts/plot_e6_gf27_action_graphs.py` uses
--
--     F3[a] / (a^3 + 2a + 1)
--
-- as a concrete plotting presentation.  The alternative cubic `a^3+a+2`
-- appearing in one supplied infographic is reducible over F3 (a=2 is a root),
-- so it is not used as a GF(27) defining polynomial.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.JMDFrobeniusThreeTateTraceCrossPollinationExact as Prior

record CompilerFrobeniusIntertwiner : Set₁ where
  field
    CompilerState : Set
    Field27State : Set
    compile : CompilerState → CompilerState
    frobenius : Field27State → Field27State
    encode : CompilerState → Field27State
    intertwines : (state : CompilerState) →
      encode (compile state) ≡ frobenius (encode state)
open CompilerFrobeniusIntertwiner public

record CompilerBootstrapObservationReceipt
    (model : CompilerFrobeniusIntertwiner) : Set₁ where
  field
    Observation : Set
    observeCompiler : CompilerState model → Observation
    observeField : Field27State model → Observation
    encodingObservationCompatible : (state : CompilerState model) →
      observeCompiler state ≡ observeField (encode model state)
open CompilerBootstrapObservationReceipt public

record GF27CompilerBootstrapBoundary : Set where
  constructor gf27-compiler-bootstrap-boundary
  field
    suppliedAnalogyAttributed : Bool
    gf27OrbitArithmeticPaid : Bool
    concreteIrreducibleGF27PlotPresentationPaid : Bool
    compilerIntertwinerInterfaceTyped : Bool
    observationCompatibilityTyped : Bool
    actualCompilerStateCarrierAcquired : Bool
    actualCompileTransitionAcquired : Bool
    actualCompilerToGF27EncodingAcquired : Bool
    actualCompileFrobeniusIntertwiningPaid : Bool
    compilerSemanticsIdentificationPaid : Bool
    note : String
open GF27CompilerBootstrapBoundary public

canonicalGF27CompilerBootstrapBoundary : GF27CompilerBootstrapBoundary
canonicalGF27CompilerBootstrapBoundary =
  gf27-compiler-bootstrap-boundary
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    "GF(27) Frobenius is now an executable finite comparison model, but promotion from structural analogy to compiler semantics requires an actual compiler carrier/transition plus an encode map commuting with Frobenius and an observation-compatible same-object receipt."
