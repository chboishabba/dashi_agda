module DASHI.Law.NonFactorabilityRuntimeTheoremBridgeRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.NonFactorabilityRuntimeTheoremBridgeExact as Bridge

boundary : Bridge.NonFactorabilityRuntimeTheoremBridgeBoundary
boundary =
  Bridge.canonicalNonFactorabilityRuntimeTheoremBridgeBoundary

exactFlagIsNotProof :
  Bridge.exactFlagAloneIsQueryAdequacyDefect boundary ≡ false
exactFlagIsNotProof =
  Bridge.exactFlagAloneIsQueryAdequacyDefectIsFalse boundary

theoremStringIsNotProof :
  Bridge.theoremRefStringAloneIsQueryAdequacyDefect boundary ≡ false
theoremStringIsNotProof =
  Bridge.theoremRefStringAloneIsQueryAdequacyDefectIsFalse boundary

checkedReceiptRequiresDefect :
  Bridge.checkedNegativeReceiptRequiresDefectInhabitant boundary ≡ true
checkedReceiptRequiresDefect =
  Bridge.checkedNegativeReceiptRequiresDefectInhabitantIsTrue boundary

checkedDefectBlocksAdequacy :
  Bridge.checkedDefectBlocksFactorsThrough boundary ≡ true
checkedDefectBlocksAdequacy =
  Bridge.checkedDefectBlocksFactorsThroughIsTrue boundary
