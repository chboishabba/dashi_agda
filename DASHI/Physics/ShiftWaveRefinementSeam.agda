module DASHI.Physics.ShiftWaveRefinementSeam where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.SchrodingerGapPhaseWaveShiftInstance as SPWSI
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftPhaseTableInterference as SPTI4

------------------------------------------------------------------------
-- Richer finite refinement seam over the current shift-wave carrier.
--
-- This stays theorem-thin and finite:
--   * coarse observations forget the explicit wave pair and keep named shadows,
--   * fine observations retain the finite wave package,
--   * project/embed only compare these two finite views of the same carrier,
--   * transport compatibility is stated for the existing discrete advance only.

data RefinementToken : Set where
  carrier-only amplitude-shadow phase-shadow wave-shadow phase-wave : RefinementToken

record CoarseObservation : Set where
  constructor mkCoarseObservation
  field
    token : RefinementToken
    carrier : SPWSI.ShiftWavePhaseState
    amplitudeShadow : SDWS.DiscreteWave
    phaseClassShadow : SPTI4.Phase4

record FineObservation : Set where
  constructor mkFineObservation
  field
    token : RefinementToken
    carrier : SPWSI.ShiftWavePhaseState
    wave : SDWS.DiscreteWave
    phaseClass : SPTI4.Phase4

coarseObserve :
  SPWSI.ShiftWavePhaseState → CoarseObservation
coarseObserve w =
  mkCoarseObservation
    phase-shadow
    w
    (SDWS.waveOfData
      (SPWSI.shiftPhaseWaveAmplitude w)
      (SPTI4.phaseClass4 w))
    (SPTI4.phaseClass4 w)

fineObserve :
  SPWSI.ShiftWavePhaseState → FineObservation
fineObserve w =
  mkFineObservation
    phase-wave
    w
    (SDWS.discreteWaveOf w)
    (SPTI4.phaseClass4 w)

projectFine :
  FineObservation → CoarseObservation
projectFine obs =
  mkCoarseObservation
    phase-shadow
    (FineObservation.carrier obs)
    (FineObservation.wave obs)
    (FineObservation.phaseClass obs)

embedCoarse :
  CoarseObservation → FineObservation
embedCoarse obs =
  fineObserve (CoarseObservation.carrier obs)

advanceCoarseObservation :
  CoarseObservation → CoarseObservation
advanceCoarseObservation obs =
  coarseObserve
    (SPWSI.advanceWavePhaseState (CoarseObservation.carrier obs))

advanceFineObservation :
  FineObservation → FineObservation
advanceFineObservation obs =
  fineObserve
    (SPWSI.advanceWavePhaseState (FineObservation.carrier obs))

projectFineAgreement : Set
projectFineAgreement =
  (w : SPWSI.ShiftWavePhaseState) →
  projectFine (fineObserve w) ≡ coarseObserve w

embedCoarseAgreement : Set
embedCoarseAgreement =
  (w : SPWSI.ShiftWavePhaseState) →
  FineObservation.carrier (embedCoarse (coarseObserve w)) ≡ w

coarseTransportCompatibility : Set
coarseTransportCompatibility =
  (w : SPWSI.ShiftWavePhaseState) →
  advanceCoarseObservation (coarseObserve w)
    ≡
  coarseObserve (SPWSI.advanceWavePhaseState w)

fineTransportCompatibility : Set
fineTransportCompatibility =
  (w : SPWSI.ShiftWavePhaseState) →
  advanceFineObservation (fineObserve w)
    ≡
  fineObserve (SPWSI.advanceWavePhaseState w)

carrierAdvanceCompatibility : Set
carrierAdvanceCompatibility =
  (w : SPWSI.ShiftWavePhaseState) →
  DDSI.shiftPressureAdvance (SPWSI.ShiftWavePhaseState.carrier w)
    ≡
  SPWSI.ShiftWavePhaseState.carrier (SPWSI.advanceWavePhaseState w)

waveShadowAgreement : Set
waveShadowAgreement =
  (w : SPWSI.ShiftWavePhaseState) →
  CoarseObservation.amplitudeShadow (coarseObserve w)
    ≡
  FineObservation.wave (fineObserve w)

phaseClassAgreement : Set
phaseClassAgreement =
  (w : SPWSI.ShiftWavePhaseState) →
  CoarseObservation.phaseClassShadow (coarseObserve w)
    ≡
  FineObservation.phaseClass (fineObserve w)

projectFineAgreement-witness : projectFineAgreement
projectFineAgreement-witness w = refl

embedCoarseAgreement-witness : embedCoarseAgreement
embedCoarseAgreement-witness w = refl

coarseTransportCompatibility-witness : coarseTransportCompatibility
coarseTransportCompatibility-witness w = refl

fineTransportCompatibility-witness : fineTransportCompatibility
fineTransportCompatibility-witness w = refl

carrierAdvanceCompatibility-witness : carrierAdvanceCompatibility
carrierAdvanceCompatibility-witness w = refl

waveShadowAgreement-witness : waveShadowAgreement
waveShadowAgreement-witness w = refl

phaseClassAgreement-witness : phaseClassAgreement
phaseClassAgreement-witness w = refl

record ShiftWaveRefinementSeam : Setω where
  field
    coarseToken : RefinementToken
    fineToken : RefinementToken
    coarseObservation : Set
    fineObservation : Set
    observeCoarse :
      SPWSI.ShiftWavePhaseState → coarseObservation
    observeFine :
      SPWSI.ShiftWavePhaseState → fineObservation
    project :
      fineObservation → coarseObservation
    embed :
      coarseObservation → fineObservation
    projectAgreement : Set
    embedAgreement : Set
    coarseTransport : Set
    fineTransport : Set
    carrierAdvance : Set
    waveAgreement : Set
    phaseAgreement : Set
    nonClaimBoundary : List String

shiftWaveRefinementSeam : ShiftWaveRefinementSeam
shiftWaveRefinementSeam =
  record
    { coarseToken = phase-shadow
    ; fineToken = phase-wave
    ; coarseObservation = CoarseObservation
    ; fineObservation = FineObservation
    ; observeCoarse = coarseObserve
    ; observeFine = fineObserve
    ; project = projectFine
    ; embed = embedCoarse
    ; projectAgreement = projectFineAgreement
    ; embedAgreement = embedCoarseAgreement
    ; coarseTransport = coarseTransportCompatibility
    ; fineTransport = fineTransportCompatibility
    ; carrierAdvance = carrierAdvanceCompatibility
    ; waveAgreement = waveShadowAgreement
    ; phaseAgreement = phaseClassAgreement
    ; nonClaimBoundary =
        "Finite refinement seam only"
        ∷ "coarse observations retain carrier plus finite amplitude/phase shadows"
        ∷ "fine observations retain the integer-pair wave package"
        ∷ "project/embed compare finite observation surfaces on the same carrier"
        ∷ "transport compatibility is only for the current discrete advance"
        ∷ "No limit, topology, derivative, PDE, or continuum refinement claim is implied"
        ∷ []
    }
