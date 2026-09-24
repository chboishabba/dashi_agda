module DASHI.Education.DigitalESDSLRInteropWrapperRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDSLRInteropWrapperExact as Wrap

wrapperCannotCreateAdmission :
  Wrap.InteropWrapperCreatesSourceAuditAdmission → ⊥
wrapperCannotCreateAdmission =
  Wrap.interopWrapperDoesNotCreateSourceAuditAdmission

wrapperCannotCreateTruth :
  Wrap.InteropWrapperCreatesSourceTruth → ⊥
wrapperCannotCreateTruth =
  Wrap.interopWrapperDoesNotCreateSourceTruth

wrapperCannotBecomeSemanticAbi :
  Wrap.InteropWrapperBecomesProductionSemanticABI → ⊥
wrapperCannotBecomeSemanticAbi =
  Wrap.interopWrapperDoesNotBecomeProductionSemanticABI

externalToolPathCannotCreateAuthority :
  Wrap.ExternalToolPathCreatesAuthority → ⊥
externalToolPathCannotCreateAuthority =
  Wrap.externalToolPathDoesNotCreateAuthority
