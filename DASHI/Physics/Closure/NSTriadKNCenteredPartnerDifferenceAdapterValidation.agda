module DASHI.Physics.Closure.NSTriadKNCenteredPartnerDifferenceAdapterValidation where

import DASHI.Physics.Closure.NSTriadKNFixedOutputPairDifferenceDebtExact
open import DASHI.Physics.Closure.NSTriadKNCenteredPartnerDifferenceAdapterExact
  using
    ( compressedPartnerIsDoubleSlotKernel
    ; compressedPartnerDifferenceIsDoubleSlotKernelDifference
    ; fixedOutputSlotKernelIsLiteralOutputFormula
    ; fixedOutputSlotKernelDifferenceIsLiteralOutputFormulaDifference
    )
import DASHI.Physics.Closure.NSTriadKNFixedOutputPairDifferenceAggregateExact
import DASHI.Physics.Closure.NSTriadKNFixedOutputPairDifferencePaymentExact
