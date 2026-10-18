module DASHI.Physics.Optics.DiffuserImagingObserverDynamicRangeExact where

-- Diffuser-mediated computational imaging: a finite, proof-relevant
-- observer/codec boundary.  Optical laws, calibrated PSFs, photon statistics,
-- and restricted-scene inverse estimates are NOT silently postulated.
--
-- Source attribution: 2026-09-27 tutorial transcript (diffuser, translated
-- caustic PSFs, pinhole calibration, deconvolution, depth-dependent encoding).
-- The matrix formulation, saturation counterexample, and observer-fibre
-- analysis below are mathematical reconstruction, not transcript quotations.

open import Agda.Primitive using (Set; Set₁)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊓_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

import DASHI.Foundations.HyperformObserverFactorisationExact as Observer
import DASHI.Physics.Optics.CatastropheDiffractionNormalFormExact as Diffraction
import DASHI.Physics.Holography.AreaLaw as AreaLaw

------------------------------------------------------------------------
-- Calibrated physical encoding.  Every law is a field that must be
-- discharged for a specified optical regime; no arbitrary PSF can pass.
------------------------------------------------------------------------

record DiffuserForwardModel
    (Scene Sensor Position Depth Pattern : Set) : Set₁ where
  field
    zeroScene : Scene
    mixScene : Scene → Scene → Scene
    mixSensor : Sensor → Sensor → Sensor
    pointAt : Position → Depth → Scene
    translate : Position → Pattern → Pattern
    atDepth : Depth → Pattern
    patternToSensor : Pattern → Sensor
    encode : Scene → Sensor

    zeroPreserved : encode zeroScene ≡ mixSensor
      (encode zeroScene) (encode zeroScene)
    superposition : (u v : Scene) →
      encode (mixScene u v) ≡ mixSensor (encode u) (encode v)
    pointResponse : (p : Position) (z : Depth) →
      encode (pointAt p z) ≡
      patternToSensor (translate p (atDepth z))

open DiffuserForwardModel public

-- The chosen scene/sensor carriers must themselves justify addition.
-- In particular, raw clipping cannot be included in 'encode' above unless
-- its corresponding superposition law actually holds.
record Calibration
    {Scene Sensor Position Depth Pattern : Set}
    (M : DiffuserForwardModel Scene Sensor Position Depth Pattern)
    (p : Position) (z : Depth)
    (observedPSF : Sensor) : Set where
  field
    measuredFromPoint :
      observedPSF ≡ encode M (pointAt M p z)

record SingleShotReconstruction
    {Scene Sensor Position Depth Pattern : Set}
    (M : DiffuserForwardModel Scene Sensor Position Depth Pattern)
    (Admissible : Scene → Set) : Set₁ where
  field
    decode : Sensor → Scene
    roundTrip : (x : Scene) → Admissible x →
      decode (encode M x) ≡ x

open SingleShotReconstruction public

-- Recovery implies injectivity on *the admitted scene class*.
roundTripImpliesIdentifiable :
  ∀ {Scene Sensor Position Depth Pattern : Set}
    {M : DiffuserForwardModel Scene Sensor Position Depth Pattern}
    {C : Scene → Set} →
  (R : SingleShotReconstruction M C) →
  (x y : Scene) → C x → C y →
  encode M x ≡ encode M y → x ≡ y
roundTripImpliesIdentifiable R x y cx cy e =
  trans (sym (roundTrip R x cx))
    (trans (cong (decode R) e) (roundTrip R y cy))

-- Merely assigning different depth PSFs is not an inverse theorem.
-- A depth-resolving model still needs a restricted-class inverse receipt.
DepthPatternsDistinct :
  ∀ {Scene Sensor Position Depth Pattern : Set} →
  DiffuserForwardModel Scene Sensor Position Depth Pattern → Set
DepthPatternsDistinct {Depth = Depth} M =
  (z w : Depth) → atDepth M z ≡ atDepth M w → z ≡ w

------------------------------------------------------------------------
-- Saturation is a *nonlinear* sensor operation after the linear encoder.
-- The finite collision is fully computational, not a physical assumption.
------------------------------------------------------------------------

clipAtOne : ℕ → ℕ
clipAtOne n = n ⊓ suc zero

one two : ℕ
one = suc zero
two = suc one

oneClipsToOne : clipAtOne one ≡ one
oneClipsToOne = refl

twoClipsToOne : clipAtOne two ≡ one
twoClipsToOne = refl

saturatedCollision : clipAtOne one ≡ clipAtOne two
saturatedCollision =
  trans oneClipsToOne (sym twoClipsToOne)

oneNotTwo : one ≡ two → ⊥
oneNotTwo ()

-- No decoder, however complicated, can invert this clipping map on
-- every natural-valued input.  Independent unsaturated measurements may
-- of course supply additional information.
noUniversalDecoderAfterClip :
  (decoder : ℕ → ℕ) →
  ((n : ℕ) → decoder (clipAtOne n) ≡ n) →
  ⊥
noUniversalDecoderAfterClip decoder correct =
  oneNotTwo
    (trans (sym (correct one))
      (trans (cong decoder saturatedCollision) (correct two)))

-- The same collision persists under every postprocessing/recharting.
postprocessingDoesNotRepairClip :
  ∀ {Output : Set} →
  (post : ℕ → Output) →
  post (clipAtOne one) ≡ post (clipAtOne two)
postprocessingDoesNotRepairClip post =
  cong post saturatedCollision

------------------------------------------------------------------------
-- Overlap is addition before digitisation.  It is NOT max-selection.
------------------------------------------------------------------------

twoOverlappingUnitContributions : one + one ≡ two
twoOverlappingUnitContributions = refl

overlapThenClip : clipAtOne (one + one) ≡ one
overlapThenClip = refl

------------------------------------------------------------------------
-- A consumer requiring the true charge distinguishes the collision.
-- This is the exact observer-fibre obstruction: a displayed/decoded
-- output cannot restore information absent from the recorded sample.
------------------------------------------------------------------------

clipFibreWitness :
  (post : ℕ → ℕ) →
  post (clipAtOne one) ≡ post (clipAtOne two)
clipFibreWitness = postprocessingDoesNotRepairClip

------------------------------------------------------------------------
-- Explicit boundaries, not claimed theorems:
--  * Shot noise, read noise, ADC quantisation and spectral colour channels
--    require separate stochastic/calibration records.
--  * "Sufficient variation with depth" is NOT global 3D injectivity.
--  * A real stable inverse requires a quantitative restricted lower bound
--    on distinguishability plus a physical noise/model-error budget.
--  * The imported AreaLaw is an entropy-count vocabulary, not evidence
--    that optical holography obeys gravitational holographic area scaling.
--  * Diffraction's wave-optics normal form requires its own explicit receipt.
--  * Physical mask design should optimise distinguishability jointly with
--    full-well occupancy and background-dependent photon noise.
------------------------------------------------------------------------
