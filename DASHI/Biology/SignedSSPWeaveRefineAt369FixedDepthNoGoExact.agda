module DASHI.Biology.SignedSSPWeaveRefineAt369FixedDepthNoGoExact where

------------------------------------------------------------------------
-- REFINE-AT-369: FIXED-DEPTH ADDRESS NO-GO + MINIMAL TYPED REPAIR
--
-- Existing rich signed-weave metadata stores
--
--   address369 : SSP.Address 3
--
-- and its residual dynamics socket therefore asks for
--
--   stepAddress : WeaveInstruction -> Address 3 -> Address 3.
--
-- If `refineAt369` is intended to mean literal prefix/tree refinement, this
-- type cannot express an increase of address depth: every input and output has
-- definitionally the same depth 3.  Moreover the current instruction is
-- nullary, so it carries no digit/child choice.
--
-- This is a structural no-go, not missing numerical data.  The minimal typed
-- repair is a variable-depth address together with an explicit Digit369 child
-- choice.  The repair below appends the child digit at the END of the finite
-- prefix, preserving the existing prefix semantics of SSP369Ultrametric.
--
-- This file does NOT claim that the signed weave *scientifically means* this
-- tree refinement.  It proves only that, if depth refinement is the intended
-- semantics, the current fixed-depth/nullary interface is insufficient and
-- exhibits the minimal carrier/action shape needed to state that semantics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Geometry.SSP369Ultrametric as SSP

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- 1. Any current stepAddress is definitionally depth-preserving.
------------------------------------------------------------------------

fixedDepthThreeStepPreservesAddressDepth :
  (step : SSP.Address 3 → SSP.Address 3) →
  (address : SSP.Address 3) →
  SSP.addressDepth (step address) ≡ SSP.addressDepth address
fixedDepthThreeStepPreservesAddressDepth step address = refl

currentRefineInstructionCarriesNoChild :
  Signed.WeaveInstruction
currentRefineInstructionCarriesNoChild = Signed.refineAt369

------------------------------------------------------------------------
-- 2. Variable-depth prefix carrier and explicit child refinement.
------------------------------------------------------------------------

record VariableDepthAddress : Set where
  constructor variableDepthAddress
  field
    depth : Nat
    address : SSP.Address depth
open VariableDepthAddress public

snocAddress :
  ∀ {d : Nat} → SSP.Address d → SSP.Digit369 → SSP.Address (suc d)
snocAddress [] child = child ∷ []
snocAddress (digit ∷ rest) child = digit ∷ snocAddress rest child

refineWithChild : SSP.Digit369 → VariableDepthAddress → VariableDepthAddress
refineWithChild child (variableDepthAddress d prefix) =
  variableDepthAddress (suc d) (snocAddress prefix child)

refinementRaisesDepthByOne :
  (child : SSP.Digit369) →
  (state : VariableDepthAddress) →
  depth (refineWithChild child state) ≡ suc (depth state)
refinementRaisesDepthByOne child (variableDepthAddress d prefix) = refl

------------------------------------------------------------------------
-- 3. The child coordinate is genuine data, not a cosmetic parameter.
------------------------------------------------------------------------

snocChildInjective :
  ∀ {d : Nat} →
  (prefix : SSP.Address d) →
  {x y : SSP.Digit369} →
  snocAddress prefix x ≡ snocAddress prefix y →
  x ≡ y
snocChildInjective [] refl = refl
snocChildInjective (digit ∷ rest) refl = refl

digit3NotDigit6 : SSP.digit3 ≢ SSP.digit6
digit3NotDigit6 ()

digit3NotDigit9 : SSP.digit3 ≢ SSP.digit9
digit3NotDigit9 ()

digit6NotDigit9 : SSP.digit6 ≢ SSP.digit9
digit6NotDigit9 ()

childThreeNotChildSix :
  ∀ {d : Nat} (prefix : SSP.Address d) →
  snocAddress prefix SSP.digit3 ≢ snocAddress prefix SSP.digit6
childThreeNotChildSix prefix eq =
  digit3NotDigit6 (snocChildInjective prefix eq)

childThreeNotChildNine :
  ∀ {d : Nat} (prefix : SSP.Address d) →
  snocAddress prefix SSP.digit3 ≢ snocAddress prefix SSP.digit9
childThreeNotChildNine prefix eq =
  digit3NotDigit9 (snocChildInjective prefix eq)

childSixNotChildNine :
  ∀ {d : Nat} (prefix : SSP.Address d) →
  snocAddress prefix SSP.digit6 ≢ snocAddress prefix SSP.digit9
childSixNotChildNine prefix eq =
  digit6NotDigit9 (snocChildInjective prefix eq)

------------------------------------------------------------------------
-- 4. Machine-readable boundary.
------------------------------------------------------------------------

record RefineAt369FixedDepthBoundary : Set where
  constructor refine-at-369-fixed-depth-boundary
  field
    currentRichAddressHasFixedDepthThree : Bool
    everyCurrentAddressStepPreservesDepth : Bool
    currentRefineInstructionCarriesChildChoice : Bool
    literalDepthRefinementExpressibleByCurrentStepType : Bool
    variableDepthAddressRepairConstructed : Bool
    explicitThreeWayChildChoiceTyped : Bool
    childChoiceChangesRefinedAddress : Bool
    variableDepthRepairMigratedIntoRichCompiler : Bool
    sourceSemanticsSelectsChildHere : Bool
open RefineAt369FixedDepthBoundary public

canonicalBoundary : RefineAt369FixedDepthBoundary
canonicalBoundary =
  refine-at-369-fixed-depth-boundary
    true true false false
    true true true
    false false
