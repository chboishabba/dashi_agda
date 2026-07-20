module DASHI.Physics.Closure.NSCompactGammaConcreteFarTailRegression where

open import DASHI.Physics.Closure.NSCompactGammaConcreteFarTail public

-- Canonical exported names matching the analytic closure checklist.
TL1-divergence-free-cancellation = fourierDivergenceFreeCancellation
TL2-multiplier-commutator-identity = multiplierCommutatorCoefficientIsExact
TL2-smooth-multiplier-gain = smoothMultiplierDifferenceDecays
TL3-far-low-commutator-bound = rawCommutatorEstimate
TL4-leray-L2-stability = l2Contraction
TL4-leray-weighted-stability = weightedStability
TL5-tangent-correction-stability = tangentProjectionUniformOnAdmissibleClass
TL5-corrected-far-low-decay = correctedFarLowDecay
TH1-high-frequency-sobolev-tail = highFrequencySobolevDecay
TH2-far-high-paraproduct-bound = farHighParaproductDecay
TH3-differentiated-numerator-domination = differentiatedFarNumeratorBound
T1-tail-rate-monotonicity = tailRateMonotone
T3-cutoff-uniform-analytic-tail-decay = cutoffUniformAnalyticTailDecay
