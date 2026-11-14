module DASHI.Foundations.F3PrimitiveQuadraticStandardChartValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.F3PrimitiveQuadraticStandardChartExact as Chart

forwardMatrixRecorded :
  Chart.explicitForwardMatrixRecorded Chart.canonicalPrimitiveStandardChartBoundary ≡ true
forwardMatrixRecorded = refl

inverseMatrixRecorded :
  Chart.explicitInverseMatrixRecorded Chart.canonicalPrimitiveStandardChartBoundary ≡ true
inverseMatrixRecorded = refl

roundTripReceiptTyped :
  Chart.roundTripReceiptTyped Chart.canonicalPrimitiveStandardChartBoundary ≡ true
roundTripReceiptTyped = refl

quadraticReceiptTyped :
  Chart.quadraticCompatibilityReceiptTyped Chart.canonicalPrimitiveStandardChartBoundary ≡ true
quadraticReceiptTyped = refl

canonicalReceiptNotInvented :
  Chart.canonicalReceiptInhabitedInThisOwner Chart.canonicalPrimitiveStandardChartBoundary ≡ false
canonicalReceiptNotInvented = refl
