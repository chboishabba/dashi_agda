module DASHI.Physics.Closure.TSFVNonseparableTransitionKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Vec using (Vec; []; _∷_; map)

import DASHI.Physics.Foundations.HistoryLocalActionAccumulationExact as Action
import DASHI.Physics.Foundations.TransitionActionNonseparabilityExact as Nonsep
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCandidate256Witness as Witness
import DASHI.Physics.Closure.TSFVCandidate256CalibrationLawDiagnostic as TSFV
import DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary as Surrogate
import Ontology.DNA.ChemistryQuotient as CDQ
import Ontology.DNA.ChemistrySheetHamiltonian as CSH
import Ontology.DNA.ChemistryUVCoordinates as UV

------------------------------------------------------------------------
-- A genuine Candidate256 transition kernel from existing quotient structure.
--
-- Unlike the older I× candidate, which is pair-valued but endpoint-separable,
-- this kernel compares the U-coordinate vectors of two quotient
-- representatives coordinate-by-coordinate using the already-existing
-- countCrossBandCoupling mismatch kernel.
------------------------------------------------------------------------

transitionMismatch :
  Surrogate.Candidate256QuotientClass →
  Surrogate.Candidate256QuotientClass →
  Nat
transitionMismatch left right =
  CSH.countCrossBandCoupling
    (map CSH.signStrength (CDQ.ChemistryFeature.u left))
    (map CSH.signStrength (CDQ.ChemistryFeature.u right))

transitionKernel : Nonsep.TransitionActionKernel
transitionKernel =
  record
    { State = Surrogate.Candidate256QuotientClass
    ; localAction = transitionMismatch
    ; kernelReading =
        "Candidate256 structural transition kernel: coordinatewise mismatch of the quotient U-vectors. This is a genuine pair interaction at the structural carrier level, not yet a calibrated physical action."
    }

------------------------------------------------------------------------
-- Exact T compatibility.
-- Candidate256 T flips the last Strength coordinate.  Simultaneously flipping
-- the corresponding coordinate in both endpoints preserves equality/mismatch.
------------------------------------------------------------------------

sameSignFlipStrength :
  (x y : CDQ.Strength) →
  CSH.sameSign
    (CSH.signStrength (TSFV.flipStrength x))
    (CSH.signStrength (TSFV.flipStrength y))
  ≡
  CSH.sameSign (CSH.signStrength x) (CSH.signStrength y)
sameSignFlipStrength CDQ.weak CDQ.weak = refl
sameSignFlipStrength CDQ.weak CDQ.strong = refl
sameSignFlipStrength CDQ.strong CDQ.weak = refl
sameSignFlipStrength CDQ.strong CDQ.strong = refl

countMismatchFlipLastInvariant :
  {n : Nat} →
  (u v : Vec CDQ.Strength (suc n)) →
  CSH.countCrossBandCoupling
    (map CSH.signStrength (TSFV.flipLastStrength u))
    (map CSH.signStrength (TSFV.flipLastStrength v))
  ≡
  CSH.countCrossBandCoupling
    (map CSH.signStrength u)
    (map CSH.signStrength v)
countMismatchFlipLastInvariant {zero} (u ∷ []) (v ∷ [])
  rewrite sameSignFlipStrength u v
  with CSH.sameSign (CSH.signStrength u) (CSH.signStrength v)
... | true = refl
... | false = refl
countMismatchFlipLastInvariant {suc n} (u ∷ us) (v ∷ vs)
  with CSH.sameSign (CSH.signStrength u) (CSH.signStrength v)
... | true = countMismatchFlipLastInvariant us vs
... | false
  rewrite countMismatchFlipLastInvariant us vs = refl

transitionMismatchTInvariant :
  (left right : Surrogate.Candidate256QuotientClass) →
  transitionMismatch
    (TSFV.candidate256QuotientT left)
    (TSFV.candidate256QuotientT right)
  ≡
  transitionMismatch left right
transitionMismatchTInvariant
  (CDQ.chemistryFeature leftU leftV)
  (CDQ.chemistryFeature rightU rightV) =
  countMismatchFlipLastInvariant leftU rightU

transitionLocalActionSystem : Action.LocalActionSystem
transitionLocalActionSystem =
  record
    { State = Surrogate.Candidate256QuotientClass
    ; localAction = transitionMismatch
    ; actionReading =
        "Additive finite-history action candidate generated from the nonseparable Candidate256 transition-mismatch kernel."
    }

transitionLocalActionSymmetry :
  Action.LocalActionSymmetry transitionLocalActionSystem
transitionLocalActionSymmetry =
  record
    { transform = TSFV.candidate256QuotientT
    ; transformInvolutive = TSFV.candidate256QuotientTInvolutive
    ; localActionInvariant = transitionMismatchTInvariant
    }

------------------------------------------------------------------------
-- Canonical left/right witness.
-- The existing Candidate256 witness differs in exactly one U coordinate.
------------------------------------------------------------------------

candidateLeft : Surrogate.Candidate256QuotientClass
candidateLeft = UV.feature256 Witness.leftUV256

candidateRight : Surrogate.Candidate256QuotientClass
candidateRight = UV.feature256 Witness.rightUV256

leftLeftZero : transitionMismatch candidateLeft candidateLeft ≡ 0
leftLeftZero = refl

rightRightZero : transitionMismatch candidateRight candidateRight ≡ 0
rightRightZero = refl

leftRightOne : transitionMismatch candidateLeft candidateRight ≡ 1
leftRightOne = refl

rightLeftOne : transitionMismatch candidateRight candidateLeft ≡ 1
rightLeftOne = refl

sumZeroLeft :
  (m n : Nat) →
  m + n ≡ 0 →
  m ≡ 0
sumZeroLeft zero n eq = refl
sumZeroLeft (suc m) n ()

sumZeroRight :
  (m n : Nat) →
  m + n ≡ 0 →
  n ≡ 0
sumZeroRight zero zero eq = refl
sumZeroRight zero (suc n) ()
sumZeroRight (suc m) n ()

oneNotZero : 1 ≡ 0 → ⊥
oneNotZero ()

transitionMismatchNonseparable :
  Nonsep.NonseparableTransition transitionKernel
transitionMismatchNonseparable separable =
  oneNotZero mixedImpossible
  where
    open Nonsep.EndpointSeparable separable

    leftPotentialZero : leftPotential candidateLeft ≡ 0
    leftPotentialZero =
      sumZeroLeft
        (leftPotential candidateLeft)
        (rightPotential candidateLeft)
        (trans (sym (decomposition candidateLeft candidateLeft)) leftLeftZero)

    rightPotentialZero : rightPotential candidateRight ≡ 0
    rightPotentialZero =
      sumZeroRight
        (leftPotential candidateRight)
        (rightPotential candidateRight)
        (trans (sym (decomposition candidateRight candidateRight)) rightRightZero)

    mixedImpossible : 1 ≡ 0
    mixedImpossible
      rewrite leftPotentialZero | rightPotentialZero =
      trans (sym leftRightOne) (decomposition candidateLeft candidateRight)

canonicalTransitionActionTarget : Nonsep.TransitionActionTarget
canonicalTransitionActionTarget =
  record
    { kernel = transitionKernel
    ; nonseparable = transitionMismatchNonseparable
    ; targetReading =
        "Exact structural witness: Candidate256 already contains a T-invariant, genuinely nonseparable transition kernel once the existing coordinatewise mismatch geometry is applied across successive quotient representatives."
    }

------------------------------------------------------------------------
-- Accumulated finite-history consequences.
------------------------------------------------------------------------

transitionTrace : List (Action.Step transitionLocalActionSystem)
transitionTrace =
  (candidateLeft , candidateRight)
  ∷ (candidateRight , candidateLeft)
  ∷ []

transitionHistoryAction : Nat
transitionHistoryAction =
  Action.historyAction transitionLocalActionSystem transitionTrace

transitionTraceTInvariant :
  Action.historyAction
    transitionLocalActionSystem
    (Action.transformTrace transitionLocalActionSymmetry transitionTrace)
  ≡
  transitionHistoryAction
transitionTraceTInvariant =
  Action.historyActionInvariant transitionLocalActionSymmetry transitionTrace

record TSFVNonseparableTransitionKernelBoundary : Set where
  constructor tsfvNonseparableTransitionKernelBoundary
  field
    structuralNonseparabilityIsPhysicalAction : Bool
    structuralNonseparabilityIsPhysicalActionIsFalse :
      structuralNonseparabilityIsPhysicalAction ≡ false

    mismatchCountHasPhysicalActionUnits : Bool
    mismatchCountHasPhysicalActionUnitsIsFalse :
      mismatchCountHasPhysicalActionUnits ≡ false

    tInvariantInteractionDeterminesHbarPhase : Bool
    tInvariantInteractionDeterminesHbarPhaseIsFalse :
      tInvariantInteractionDeterminesHbarPhase ≡ false

canonicalTSFVNonseparableTransitionKernelBoundary :
  TSFVNonseparableTransitionKernelBoundary
canonicalTSFVNonseparableTransitionKernelBoundary =
  tsfvNonseparableTransitionKernelBoundary
    false refl
    false refl
    false refl
