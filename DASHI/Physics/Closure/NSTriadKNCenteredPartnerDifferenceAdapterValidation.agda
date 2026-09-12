module DASHI.Physics.Closure.NSTriadKNCenteredPartnerDifferenceAdapterValidation where

import DASHI.Physics.Closure.NSTriadKNFixedOutputPairDifferenceDebtExact
open import DASHI.Physics.Closure.NSTriadKNCenteredPartnerDifferenceAdapterExact
  using
    ( compressedPartnerIsDoubleSlotKernel
    ; compressedPartnerDifferenceIsDoubleSlotKernelDifference
    ; fixedOutputSlotKernelIsLiteralOutputFormula
    ; fixedOutputSlotKernelDifferenceIsLiteralOutputFormulaDifference
    )
open import DASHI.Physics.Closure.NSTriadKNCenteredPartnerSlotDefectExact
  using (compressedPartnerDifferenceNormIsFourSlotDefect)
import DASHI.Physics.Closure.NSTriadKNFixedOutputPairDifferenceAggregateExact
import DASHI.Physics.Closure.NSTriadKNFixedOutputPairDifferencePaymentExact
