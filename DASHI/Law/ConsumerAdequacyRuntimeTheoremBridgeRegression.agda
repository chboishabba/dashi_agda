module DASHI.Law.ConsumerAdequacyRuntimeTheoremBridgeRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.ConsumerAdequacyRuntimeTheoremBridgeExact as Bridge

boundary : Bridge.ConsumerAdequacyRuntimeTheoremBridgeBoundary
boundary = Bridge.canonicalConsumerAdequacyRuntimeTheoremBridgeBoundary

runtimeCompletenessIsNotFormalAdequacy :
  Bridge.runtimeCoordinateCompletenessIsFormalAdequacy boundary ≡ false
runtimeCompletenessIsNotFormalAdequacy =
  Bridge.runtimeCoordinateCompletenessIsFormalAdequacyIsFalse boundary

formalReceiptRequiresFactorsThrough :
  Bridge.theoremBackedReceiptRequiresAdequateForInhabitant boundary ≡ true
formalReceiptRequiresFactorsThrough =
  Bridge.theoremBackedReceiptRequiresAdequateForInhabitantIsTrue boundary

theoremStringIsNotProof :
  Bridge.theoremRefStringAloneIsProof boundary ≡ false
theoremStringIsNotProof =
  Bridge.theoremRefStringAloneIsProofIsFalse boundary
