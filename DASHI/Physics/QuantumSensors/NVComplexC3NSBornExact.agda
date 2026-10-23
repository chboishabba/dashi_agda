module DASHI.Physics.QuantumSensors.NVComplexC3NSBornExact where

-- Exact Gaussian rational amplitude: complex C3 coherent intensity, generated
-- signed cross-work, and reuse of NS ABCD finite pair-difference theorem.
-- Mathematical donor Shor cyclic Fourier/Born weights; physical rates not fixed.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as NS

record ComplexQ : Set where
  constructor complex
  field re im : ℚ
open ComplexQ public

_⊕_ : ComplexQ → ComplexQ → ComplexQ
complex a b ⊕ complex c d = complex (a + c) (b + d)

modulusSquared : ComplexQ → ℚ
modulusSquared (complex a b) = a * a + b * b

signedCross : ComplexQ → ComplexQ → ℚ
signedCross (complex a b) (complex c d) =
  (a + a) * c + (b + b) * d

record OpticalTriple : Set where
  constructor triple
  field a b c : ComplexQ
open OpticalTriple public

rotate : OpticalTriple → OpticalTriple
rotate (triple a b c) = triple c a b

rotateCubed : (x : OpticalTriple) → rotate (rotate (rotate x)) ≡ x
rotateCubed (triple a b c) = refl

coherentAmplitude : OpticalTriple → ComplexQ
coherentAmplitude x = a x ⊕ (b x ⊕ c x)

coherentIntensity : OpticalTriple → ℚ
coherentIntensity x = modulusSquared (coherentAmplitude x)

incoherentIntensity : OpticalTriple → ℚ
incoherentIntensity x =
  modulusSquared (a x) + modulusSquared (b x) + modulusSquared (c x)

signedWorkSum : OpticalTriple → ℚ
signedWorkSum x =
  signedCross (a x) (b x)
  + signedCross (b x) (c x)
  + signedCross (c x) (a x)

bornInterferenceDecomposition :
  (x : OpticalTriple) →
  coherentIntensity x ≡ incoherentIntensity x + signedWorkSum x
bornInterferenceDecomposition
  (triple (complex ar ai) (complex br bi) (complex cr ci)) =
    solve (ar ∷ ai ∷ br ∷ bi ∷ cr ∷ ci ∷ [])

coherentIntensityC3 :
  (x : OpticalTriple) →
  coherentIntensity (rotate x) ≡ coherentIntensity x
coherentIntensityC3
  (triple (complex ar ai) (complex br bi) (complex cr ci)) =
    solve (ar ∷ ai ∷ br ∷ bi ∷ cr ∷ ci ∷ [])

record WeightedOpticalTriple : Set where
  constructor weighted
  field
    amplitudes : OpticalTriple
    rAB rBC rCA : ℚ
open WeightedOpticalTriple public

pairWork : WeightedOpticalTriple → List (ℚ × ℚ)
pairWork x =
  (rAB x , signedCross (a (amplitudes x)) (b (amplitudes x))) ∷
  (rBC x , signedCross (b (amplitudes x)) (c (amplitudes x))) ∷
  (rCA x , signedCross (c (amplitudes x)) (a (amplitudes x))) ∷ []

signedOpticalCovariance :
  (x : WeightedOpticalTriple) →
  NS.natAsRational (length (pairWork x)) *
    (0ℚ - NS.weightedWorkSum proj₁ proj₂ (pairWork x))
    + NS.rateSum proj₁ (pairWork x) *
      NS.workSum proj₂ (pairWork x)
  ≡ 0ℚ - NS.pairDifferenceWorkSum proj₁ proj₂ (pairWork x)
signedOpticalCovariance x =
  NS.divisionFreePairDifferenceCentering proj₁ proj₂ (pairWork x)

-- Nonnegative amplitude norm is mathematical; normalized photon counting
-- and physical S/hbar calibration remain separate source-backed obligations.
