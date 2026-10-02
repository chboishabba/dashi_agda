module DASHI.Physics.CondensedMatter.YbSbTwoINTNonunitarySelectedExact where

------------------------------------------------------------------------
-- YbSb2 INT selected-state formalisation.
--
-- Primary source:
-- A. Kataria et al.,
-- "Observation of Time-Reversal Symmetry Breaking in the Type-I
-- Superconductor YbSb2", Physical Review Letters, accepted 3 Aug 2026.
-- DOI 10.1103/drzq-lfn5; arXiv:2601.07460.
--
-- Source formulas:
--
--   Delta-hat = (i tau_y) tensor (d . s)(i sigma_y)
--   d = Delta_0 eta
--   q = i (eta x eta*) != 0
--
-- The paper's displayed surface calculation uses
--
--   eta = (1/sqrt(2)) (1, exp(i pi/4), 0).
--
-- This file does NOT claim to derive the material ground state from
-- microscopic interactions.  It provides:
--
--  1. a finite exact carrier for the sign/orientation of the TR-odd
--     nonunitarity witness q;
--  2. global gauge phases that leave q unchanged;
--  3. time reversal that flips q;
--  4. a selected nonzero-q witness;
--  5. the theorem that this selected state cannot be time-reversal
--     invariant even after an arbitrary global gauge phase.
--
-- The reusable proof is imported from
-- SuperconductingTimeReversalGaugeObstructionExact.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.CondensedMatter.SuperconductingTimeReversalGaugeObstructionExact as TR

data Chirality : Set where
  zeroQ positiveQ negativeQ : Chirality

negateQ : Chirality → Chirality
negateQ zeroQ = zeroQ
negateQ positiveQ = negativeQ
negateQ negativeQ = positiveQ

fixedQIsZero :
  (q : Chirality) →
  q ≡ negateQ q →
  q ≡ zeroQ
fixedQIsZero zeroQ p = refl
fixedQIsZero positiveQ ()
fixedQIsZero negativeQ ()

-- Four exact tags for a global superconducting phase.  q is gauge
-- invariant, so the selected q-coordinate is intentionally unaffected
-- by every constructor here.
data GlobalPhase : Set where
  phase0 phaseQuarter phaseHalf phaseThreeQuarter : GlobalPhase

-- selectedINT represents the source-selected nonunitary orientation;
-- conjugateINT is its time-reversed partner; unitaryINT is the q=0 lane.
data INTState : Set where
  unitaryINT selectedINT conjugateINT : INTState

globalGauge : GlobalPhase → INTState → INTState
globalGauge g x = x

reverseINT : INTState → INTState
reverseINT unitaryINT = unitaryINT
reverseINT selectedINT = conjugateINT
reverseINT conjugateINT = selectedINT

qWitness : INTState → Chirality
qWitness unitaryINT = zeroQ
qWitness selectedINT = positiveQ
qWitness conjugateINT = negativeQ

gaugeLeavesQ :
  (g : GlobalPhase) (x : INTState) →
  qWitness (globalGauge g x) ≡ qWitness x
gaugeLeavesQ g x = refl

timeReverseFlipsQ :
  (x : INTState) →
  qWitness (reverseINT x) ≡ negateQ (qWitness x)
timeReverseFlipsQ unitaryINT = refl
timeReverseFlipsQ selectedINT = refl
timeReverseFlipsQ conjugateINT = refl

intTRSystem : TR.TROddGaugeWitnessSystem
intTRSystem =
  record
    { State = INTState
    ; Gauge = GlobalPhase
    ; Witness = Chirality
    ; gaugeAction = globalGauge
    ; timeReverse = reverseINT
    ; witness = qWitness
    ; zeroWitness = zeroQ
    ; negateWitness = negateQ
    ; gaugeInvariant = gaugeLeavesQ
    ; timeReverseOdd = timeReverseFlipsQ
    ; fixedPointIsZero = fixedQIsZero
    }

selectedQNonzero :
  TR.WitnessNonzero intTRSystem selectedINT
selectedQNonzero ()

selectedINTBreaksTRUpToGauge :
  TR.TRGaugeEquivalent intTRSystem selectedINT → ⊥
selectedINTBreaksTRUpToGauge =
  TR.nonzeroTROddWitnessObstructsTRGaugeEquivalence
    intTRSystem
    selectedINT
    selectedQNonzero

-- Source-selected eta tag.  This is a provenance-bearing selection, not
-- yet a formal complex-vector calculation of i(eta x eta*).
data EtaSelection : Set where
  paperEta paperEtaConjugate : EtaSelection

stateOfEta : EtaSelection → INTState
stateOfEta paperEta = selectedINT
stateOfEta paperEtaConjugate = conjugateINT

paperEtaQNonzero :
  TR.WitnessNonzero intTRSystem (stateOfEta paperEta)
paperEtaQNonzero = selectedQNonzero

paperEtaBreaksTRUpToGauge :
  TR.TRGaugeEquivalent intTRSystem (stateOfEta paperEta) → ⊥
paperEtaBreaksTRUpToGauge = selectedINTBreaksTRUpToGauge
