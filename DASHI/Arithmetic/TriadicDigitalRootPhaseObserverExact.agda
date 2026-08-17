module DASHI.Arithmetic.TriadicDigitalRootPhaseObserverExact where

------------------------------------------------------------------------
-- ARISTOTLE / HARMONIC CONTEXT
--
-- The supplied Tesla369 development proves that positive decimal digital
-- roots {3,6,9} are exactly the visible representatives of divisibility by 3.
-- Existing DASHI parity already realizes roots as Z/9 residues.  This module
-- composes that exact layer with the new C9 -> C3 quotient used by the phase
-- character weld.
--
-- No new numerology is introduced: the statement is exactly that the
-- triadic digital-root subset is the zero fibre of reduction mod 3.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Arithmetic.DecimalDigitalRootNonaryExact as Digital
import DASHI.Foundations.CyclicNineCharacterPullbackExact as Pullback

rootPhase : Digital.PositiveDigitalRoot9 → Phase.Phase3
rootPhase root = Pullback.c9ToC3 (Digital.rootResidue9 root)

triadicRootProjectsToPhaseZero :
  (root : Digital.PositiveDigitalRoot9) →
  Digital.TriadicDigitalRoot root →
  rootPhase root ≡ Phase.phase0
triadicRootProjectsToPhaseZero Digital.root3 Digital.root3IsTriadic = refl
triadicRootProjectsToPhaseZero Digital.root6 Digital.root6IsTriadic = refl
triadicRootProjectsToPhaseZero Digital.root9 Digital.root9IsTriadic = refl

phaseZeroImpliesTriadicRoot :
  (root : Digital.PositiveDigitalRoot9) →
  rootPhase root ≡ Phase.phase0 →
  Digital.TriadicDigitalRoot root
phaseZeroImpliesTriadicRoot Digital.root1 ()
phaseZeroImpliesTriadicRoot Digital.root2 ()
phaseZeroImpliesTriadicRoot Digital.root3 equality = Digital.root3IsTriadic
phaseZeroImpliesTriadicRoot Digital.root4 ()
phaseZeroImpliesTriadicRoot Digital.root5 ()
phaseZeroImpliesTriadicRoot Digital.root6 equality = Digital.root6IsTriadic
phaseZeroImpliesTriadicRoot Digital.root7 ()
phaseZeroImpliesTriadicRoot Digital.root8 ()
phaseZeroImpliesTriadicRoot Digital.root9 equality = Digital.root9IsTriadic

-- The visible 3/6/9 filter is therefore exactly one fibre of the C9 -> C3
-- observer, not an invariant of arbitrary operations on the nine-state ring.
record TriadicDigitalRootPhaseBoundary : Set where
  field
    digitalRootResidueLayerReused : Bool
    triadicSetIsPhaseZeroFibre : Bool
    phaseZeroFibreConverseProved : Bool
    allNineRootsCollapseToPhaseZero : Bool

canonicalTriadicDigitalRootPhaseBoundary :
  TriadicDigitalRootPhaseBoundary
canonicalTriadicDigitalRootPhaseBoundary =
  record
    { digitalRootResidueLayerReused = true
    ; triadicSetIsPhaseZeroFibre = true
    ; phaseZeroFibreConverseProved = true
    ; allNineRootsCollapseToPhaseZero = false
    }
