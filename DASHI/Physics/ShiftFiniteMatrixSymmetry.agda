module DASHI.Physics.ShiftFiniteMatrixSymmetry where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftFiniteGaugeSymmetry as SFGS
open import DASHI.Physics.ShiftPhaseTableInterference as SPTI4

------------------------------------------------------------------------
-- Finite matrix-action packaging over the current discrete-wave lane.
--
-- The first surface is the existing Phase4/C4 quarter-turn action on a
-- single integer-pair wave. The second surface is a bounded doublet-action
-- analogue that introduces swap and componentwise phase actions without
-- claiming full matrix groups, SU(2), or continuum structure.

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

phaseActIdentity :
  (w : SDWS.DiscreteWave) →
  SFGS.phaseAct SPTI4.φ0 w ≡ w
phaseActIdentity w = refl

MatrixPhaseActComposeTarget : Set
MatrixPhaseActComposeTarget =
  (φ ψ : SPTI4.Phase4) →
  (w : SDWS.DiscreteWave) →
  SFGS.phaseAct (SFGS.phaseAdd4 φ ψ) w
    ≡
  SFGS.phaseAct φ (SFGS.phaseAct ψ w)

MatrixPhaseActInverseTarget : Set
MatrixPhaseActInverseTarget =
  (φ : SPTI4.Phase4) →
  (w : SDWS.DiscreteWave) →
  SFGS.phaseAct (SFGS.phaseInv4 φ) (SFGS.phaseAct φ w)
    ≡
  w

record FiniteMatrixSymmetry : Set₁ where
  field
    G : Set
    Carrier : Set
    act : G → Carrier → Carrier
    compose : G → G → G
    identity : G
    inverse : G → G
    actIdentity :
      (x : Carrier) →
      act identity x ≡ x
    actComposeTarget : Set
    actInverseTarget :
      Set
    nonClaimBoundary : List String

phase4MatrixSymmetry : FiniteMatrixSymmetry
phase4MatrixSymmetry =
  record
    { G = SPTI4.Phase4
    ; Carrier = SDWS.DiscreteWave
    ; act = SFGS.phaseAct
    ; compose = SFGS.phaseAdd4
    ; identity = SPTI4.φ0
    ; inverse = SFGS.phaseInv4
    ; actIdentity = phaseActIdentity
    ; actComposeTarget = MatrixPhaseActComposeTarget
    ; actInverseTarget = MatrixPhaseActInverseTarget
    ; nonClaimBoundary =
        "Finite C4 matrix-action surface only"
        ∷ "This is U(1)-like quarter-turn transport, not full continuous U(1)"
        ∷ "Generic compose and inverse equalities remain theorem-thin target surfaces in this lane"
        ∷ "No Hilbert-space, analytic unitarity, or continuum structure is implied"
        ∷ []
    }

record WaveDoublet : Set where
  constructor mkWaveDoublet
  field
    ψ₁ : SDWS.DiscreteWave
    ψ₂ : SDWS.DiscreteWave

data DoubletOp : Set where
  idD : DoubletOp
  swapD : DoubletOp
  phase1D : SPTI4.Phase4 → DoubletOp
  phase2D : SPTI4.Phase4 → DoubletOp

actDoublet : DoubletOp → WaveDoublet → WaveDoublet
actDoublet idD x = x
actDoublet swapD x =
  mkWaveDoublet
    (WaveDoublet.ψ₂ x)
    (WaveDoublet.ψ₁ x)
actDoublet (phase1D φ) x =
  mkWaveDoublet
    (SFGS.phaseAct φ (WaveDoublet.ψ₁ x))
    (WaveDoublet.ψ₂ x)
actDoublet (phase2D φ) x =
  mkWaveDoublet
    (WaveDoublet.ψ₁ x)
    (SFGS.phaseAct φ (WaveDoublet.ψ₂ x))

sampleDoublet : WaveDoublet
sampleDoublet =
  mkWaveDoublet
    (SDWS.encodePhase4 SPTI4.φ0)
    (SDWS.encodePhase4 SPTI4.φ1)

nonAbelianLeft :
  WaveDoublet
nonAbelianLeft =
  actDoublet swapD (actDoublet (phase1D SPTI4.φ1) sampleDoublet)

nonAbelianRight :
  WaveDoublet
nonAbelianRight =
  actDoublet (phase1D SPTI4.φ1) (actDoublet swapD sampleDoublet)

nonAbelianWitness :
  nonAbelianLeft ≢ nonAbelianRight
nonAbelianWitness ()

record ShiftFiniteMatrixSymmetry : Set₁ where
  field
    phaseMatrixAction : FiniteMatrixSymmetry
    doubletCarrier : Set
    doubletAction : DoubletOp → WaveDoublet → WaveDoublet
    doubletWitnessLeft : DoubletOp
    doubletWitnessRight : DoubletOp
    sampleCarrierPoint : WaveDoublet
    nonAbelianWitnessSurface : Set
    nonClaimBoundary : List String

shiftFiniteMatrixSymmetry : ShiftFiniteMatrixSymmetry
shiftFiniteMatrixSymmetry =
  record
    { phaseMatrixAction = phase4MatrixSymmetry
    ; doubletCarrier = WaveDoublet
    ; doubletAction = actDoublet
    ; doubletWitnessLeft = swapD
    ; doubletWitnessRight = phase1D SPTI4.φ1
    ; sampleCarrierPoint = sampleDoublet
    ; nonAbelianWitnessSurface = nonAbelianLeft ≢ nonAbelianRight
    ; nonClaimBoundary =
        "Finite matrix-action packaging only"
        ∷ "Doublet action is a first bounded non-abelian analogue, not SU(2)"
        ∷ "The non-abelian witness is a concrete swap/phase ordering witness on one sampled doublet"
        ∷ "No Hilbert-space, continuum gauge group, or analytic matrix theory claim is implied"
        ∷ []
    }
