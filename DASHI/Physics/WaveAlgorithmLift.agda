module DASHI.Physics.WaveAlgorithmLift where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
open import DASHI.Physics.ShiftUnitaryLikeConstraint as SULC

------------------------------------------------------------------------
-- DASHI wave-algorithm lift.
--
-- This module packages the full algorithmic correspondence requested by the
-- wave interpretation of DASHI:
--
--   ternary sign / support  -> finite phase / zero amplitude
--   branching              -> superposition
--   invariant check         -> phase action
--   pruning                 -> exact or observational cancellation
--   fixed point / orbit     -> coherent eigen-object
--   quotient / decode       -> observation and projection
--   renormalisation tower   -> lift / project compatibility
--   action / MDL            -> observable concentration obligation
--
-- The existing finite integer-pair wave carrier supports exact algebraic
-- witnesses below.  Genuine Hilbert-space, analytic-unitary, spectral,
-- continuum, and quantum-speedup claims remain explicit obligations.

------------------------------------------------------------------------
-- 1. Balanced-ternary carrier and involution.

data Trit : Set where
  neg zero pos : Trit

tritInvolution : Trit → Trit
tritInvolution neg = pos
tritInvolution zero = zero
tritInvolution pos = neg

tritInvolution² : (t : Trit) → tritInvolution (tritInvolution t) ≡ t
tritInvolution² neg = refl
tritInvolution² zero = refl
tritInvolution² pos = refl

tritSupport : Trit → Bool
tritSupport neg = true
tritSupport zero = false
tritSupport pos = true

tritPhase : Trit → SPTI4.Phase4
tritPhase neg = SPTI4.φ2
tritPhase zero = SPTI4.φ0
tritPhase pos = SPTI4.φ0

------------------------------------------------------------------------
-- 2. Exact finite wave encoding.
--
-- `zero` is zero amplitude.  `pos` and `neg` are opposite phase-basis waves.

zeroWave : SDWS.DiscreteWave
zeroWave = SDWS.mkDiscreteWave (+ 0) (+ 0)

encodeTritWave : Trit → SDWS.DiscreteWave
encodeTritWave neg = SDWS.encodePhase4 SPTI4.φ2
encodeTritWave zero = zeroWave
encodeTritWave pos = SDWS.encodePhase4 SPTI4.φ0

waveNeg : SDWS.DiscreteWave → SDWS.DiscreteWave
waveNeg ψ = SDWS.mulI (SDWS.mulI ψ)

encodeInvolutionAsPhaseOpposition :
  (t : Trit) →
  encodeTritWave (tritInvolution t) ≡ waveNeg (encodeTritWave t)
encodeInvolutionAsPhaseOpposition neg = refl
encodeInvolutionAsPhaseOpposition zero = refl
encodeInvolutionAsPhaseOpposition pos = refl

encodedTritNormSq : Trit → ℤ
encodedTritNormSq t = SULC.waveNormSq (encodeTritWave t)

zeroHasZeroNorm : encodedTritNormSq zero ≡ + 0
zeroHasZeroNorm = refl

posHasUnitNorm : encodedTritNormSq pos ≡ + 1
posHasUnitNorm = refl

negHasUnitNorm : encodedTritNormSq neg ≡ + 1
negHasUnitNorm = refl

------------------------------------------------------------------------
-- 3. Generic wave inference surface.
--
-- `Wave` may later be instantiated by the current finite `DiscreteWave`, a
-- finite field of such waves, or a stronger analytic carrier.  No law is
-- smuggled into the data fields: every substantive property is explicit.

record WaveInferenceSurface : Set₁ where
  field
    Hypothesis : Set
    Wave : Set
    Observable : Set

    zeroAmplitude : Wave
    superpose : Wave → Wave → Wave
    phaseAction : Hypothesis → Wave → Wave
    evolve : Wave → Wave
    observe : Wave → Observable

    coherent : Wave → Bool
    admissible : Hypothesis → Bool

------------------------------------------------------------------------
-- 4. Reversible / unitary obligations.
--
-- These fields state the exact laws required before the finite phase-action
-- language may be promoted to a genuine reversible or unitary algorithm.

record ReversibleWaveObligations
  (W : WaveInferenceSurface) : Set₁ where
  open WaveInferenceSurface W
  field
    undo : Wave → Wave
    leftInverse : (ψ : Wave) → undo (evolve ψ) ≡ ψ
    rightInverse : (ψ : Wave) → evolve (undo ψ) ≡ ψ

record NormPreservingWaveObligations
  (W : WaveInferenceSurface) : Set₁ where
  open WaveInferenceSurface W
  field
    Norm : Set
    norm : Wave → Norm
    evolvePreservesNorm : (ψ : Wave) → norm (evolve ψ) ≡ norm ψ
    phasePreservesNorm :
      (h : Hypothesis) → (ψ : Wave) →
      norm (phaseAction h ψ) ≡ norm ψ

------------------------------------------------------------------------
-- 5. Interference replaces pruning only when a cancellation law is supplied.

record InterferencePruningBridge
  (W : WaveInferenceSurface) : Set₁ where
  open WaveInferenceSurface W
  field
    opposite : Wave → Wave
    rejectsByCancellation :
      (h : Hypothesis) → admissible h ≡ false → (ψ : Wave) →
      superpose (phaseAction h ψ) (opposite (phaseAction h ψ))
        ≡ zeroAmplitude

------------------------------------------------------------------------
-- 6. Coherent eigen-objects are the wave analogue of fixed/low-action orbits.

record CoherentEigenObject
  (W : WaveInferenceSurface) : Set where
  open WaveInferenceSurface W
  field
    state : Wave
    eigenPhase : Wave → Wave
    phaseLocked : evolve state ≡ eigenPhase state
    coherenceWitness : coherent state ≡ true

------------------------------------------------------------------------
-- 7. Projection / observation boundary.
--
-- Observation is deliberately separate from evolution.  The record supports
-- deterministic finite observations as well as later probability-valued ones.

record ProjectionBoundary
  (W : WaveInferenceSurface) : Set₁ where
  open WaveInferenceSurface W
  field
    Classical : Set
    project : Observable → Classical
    observationallyZero : Wave → Bool
    cancelledIsUnobservable :
      (ψ : Wave) → observationallyZero ψ ≡ true →
      observe ψ ≡ observe zeroAmplitude

------------------------------------------------------------------------
-- 8. Renormalisation / refinement tower.
--
-- This is the theorem-thin general form of the existing finite project/embed
-- modules.  Exact commutation is strongest; `agreesAfterObservation` supports
-- the repo's weaker observational compatibility seams without conflating them.

record WaveRefinementTower
  (coarse fine : WaveInferenceSurface) : Set₁ where
  open WaveInferenceSurface coarse renaming
    (Wave to CoarseWave; Observable to CoarseObservable;
     evolve to evolveCoarse; observe to observeCoarse)
  open WaveInferenceSurface fine renaming
    (Wave to FineWave; Observable to FineObservable;
     evolve to evolveFine; observe to observeFine)
  field
    lift : CoarseWave → FineWave
    projectWave : FineWave → CoarseWave
    projectObservable : FineObservable → CoarseObservable

    projectAfterLift :
      (ψ : CoarseWave) → projectWave (lift ψ) ≡ ψ

    exactEvolutionCompatibility :
      (ψ : CoarseWave) → evolveFine (lift ψ) ≡ lift (evolveCoarse ψ)

    agreesAfterObservation :
      (ψ : CoarseWave) →
      projectObservable (observeFine (lift ψ)) ≡ observeCoarse ψ

------------------------------------------------------------------------
-- 9. Action / MDL concentration boundary.
--
-- Compression is not identified with norm preservation.  Promotion requires a
-- separate code/action surface showing that coherent observable descriptions
-- do not lengthen under the selected evolution or projection.

record WaveMDLConcentration
  (W : WaveInferenceSurface) : Set₁ where
  open WaveInferenceSurface W
  field
    Code : Set
    Length : Set
    codeObservable : Observable → Code
    descriptionLength : Code → Length
    noLongerThan : Length → Length → Bool

    coherentEvolutionDoesNotLengthen :
      (ψ : Wave) → coherent ψ ≡ true →
      noLongerThan
        (descriptionLength (codeObservable (observe (evolve ψ))))
        (descriptionLength (codeObservable (observe ψ)))
        ≡ true

------------------------------------------------------------------------
-- 10. Complete wave-algorithm package.

record DASHIWaveAlgorithm : Set₁ where
  field
    surface : WaveInferenceSurface
    reversible : ReversibleWaveObligations surface
    normPreserving : NormPreservingWaveObligations surface
    interferenceBridge : InterferencePruningBridge surface
    projectionBoundary : ProjectionBoundary surface
    mdlConcentration : WaveMDLConcentration surface
    nonClaimBoundary : List String

waveAlgorithmNonClaimBoundary : List String
waveAlgorithmNonClaimBoundary =
  "Finite sign/phase encoding is exact on the current integer-pair carrier"
  ∷ "The generic records state promotion obligations; they do not inhabit them"
  ∷ "Destructive interference replaces pruning only under an explicit cancellation witness"
  ∷ "Observation and projection are separate from reversible evolution"
  ∷ "MDL concentration is a separate law and does not follow from norm preservation alone"
  ∷ "No analytic Hilbert space, self-adjoint Hamiltonian, Born rule, continuum PDE, physical quantisation, or quantum speedup is claimed"
  ∷ []
