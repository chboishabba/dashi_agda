module DASHI.Analysis.RiemannAristotleProjectedCarrierLeanReturnExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-LEVEL LEAN RETURN FOR UNIVERSAL U2
--
-- The bidi Lean patch now contains a literal three-sample Weil balance and an
-- exact post-pole-quotient balance theorem.  The latter consumes an explicit
-- identification of the literal pole response vector with the two deterministic
-- nuisance directions and then uses exact `elim2` cancellation.
--
-- The new Lean files were produced in an environment without the pinned Lean
-- executable.  Therefore this owner records source implementation only and
-- deliberately sets machineCheckedInOwner = false.
------------------------------------------------------------------------

record ProjectedCarrierLeanReturn : Set where
  constructor projected-carrier-lean-return
  field
    theoremName : String
    sourceImplementedInLean : Bool
    sourceImplementedInLeanIsTrue : sourceImplementedInLean ≡ true
    machineCheckedInOwner : Bool
    machineCheckedInOwnerIsFalse : machineCheckedInOwner ≡ false
    transportedIntoAgda : Bool
    transportedIntoAgdaIsFalse : transportedIntoAgda ≡ false
    literalThreeSampleBalanceWritten : Bool
    literalThreeSampleBalanceWrittenIsTrue : literalThreeSampleBalanceWritten ≡ true
    postPoleQuotientCarrierWritten : Bool
    postPoleQuotientCarrierWrittenIsTrue : postPoleQuotientCarrierWritten ≡ true
    exactPoleVectorDecompositionStillRequired : Bool
    exactPoleVectorDecompositionStillRequiredIsTrue :
      exactPoleVectorDecompositionStillRequired ≡ true
    literalPoleQuotientTargetTransversalityStillRequired : Bool
    literalPoleQuotientTargetTransversalityStillRequiredIsTrue :
      literalPoleQuotientTargetTransversalityStillRequired ≡ true
    boundedReading : String

open ProjectedCarrierLeanReturn public

canonicalProjectedCarrierLeanReturn : ProjectedCarrierLeanReturn
canonicalProjectedCarrierLeanReturn =
  projected-carrier-lean-return
    "LiteralWeilThreeSampleProjectedCarrier.postPoleQuotientLiteralBalance"
    true refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    "The universal post-pole-quotient carrier is now implemented as Lean source, but this new patch has no Lean kernel receipt. It still consumes the exact literal pole-vector decomposition and does not prove target transversality, the signed zero-tail estimate, the arithmetic payment, or RH."
