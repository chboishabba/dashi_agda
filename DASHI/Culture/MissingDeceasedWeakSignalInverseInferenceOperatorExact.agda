module DASHI.Culture.MissingDeceasedWeakSignalInverseInferenceOperatorExact where

open import DASHI.Core.Prelude
open import DASHI.Core.ScientificOperatorFamilyExact as O

-- Shared shape: observation -> structured candidate -> non-unique inverse fibre.
-- Domain-specific equations and likelihoods remain owned by the original files.

grillmairWeakSignal : O.OperatorFactorisation
grillmairWeakSignal = O.operator-factorisation
  "Carl J. Grillmair"
  "DASHI.Physics.Astrophysics.GrillmairStellarStreamBidiExact"
  O.weakSignalShape
  "stellar catalogue + colour-magnitude filter + distance scan -> stream candidate / orbit-family inference"
  "Matched filtering is the reusable operator; it does not make stellar-stream morphology equivalent to any other domain's signal."

hicksWeakSignal : O.OperatorFactorisation
hicksWeakSignal = O.operator-factorisation
  "Michael David Hicks"
  "DASHI.Physics.Planetary.HicksSmallBodyPhotometryBidiExact"
  O.weakSignalShape
  "time-series photometry + viewing geometry -> phase-folded lightcurve -> rotation/physical-model fibre"
  "Phase folding and inverse physical inference share the operator shape without making asteroid photometry a stellar-stream problem."

zhangXiaoxinWeakSignal : O.OperatorFactorisation
zhangXiaoxinWeakSignal = O.operator-factorisation
  "Zhang Xiaoxin"
  "DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastBidiExact"
  O.weakSignalShape
  "cosmic-ray time series -> whitening + CEEMDAN/CWT -> precursor candidate -> forecast"
  "Signal decomposition shares inverse-inference structure; forecasting thresholds and causal interpretation remain domain-specific."

maiwaldWeakSignal : O.OperatorFactorisation
maiwaldWeakSignal = O.operator-factorisation
  "Frank W. Maiwald"
  "DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopyBidiExact"
  O.weakSignalShape
  "tagged-ion action spectrum -> spectral-feature pattern -> compatible molecular conformer fibre"
  "Spectral matching is an inverse inference; it does not identify a unique molecular state without calculation/calibration assumptions."

thomasWeakSignal : O.OperatorFactorisation
thomasWeakSignal = O.operator-factorisation
  "Jason R. Thomas"
  "DASHI.Biology.JasonThomasSignallingBidiExact"
  O.weakSignalShape
  "perturbation/readout pattern -> candidate target/pathway -> direct-target validation fibre"
  "Screen hits and target candidates are not direct mechanism proof; reverse validation remains mandatory."

weakSignalFactorisations : List O.OperatorFactorisation
weakSignalFactorisations =
  grillmairWeakSignal ∷ hicksWeakSignal ∷ zhangXiaoxinWeakSignal ∷
  maiwaldWeakSignal ∷ thomasWeakSignal ∷ []
