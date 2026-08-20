module DASHI.Moonshine.AristotleZetaFrobeniusCrossPollinationEverything where

------------------------------------------------------------------------
-- Focused aggregate for the later Tesla369 / palette-character / Frobenius
-- cross-pollination described in the supplied material.
--
-- This is intentionally NOT added to the pinned Aristotle source-parity
-- manifest: the supplied PDF is later than that snapshot.  The modules below
-- are theorem-producing DASHI welds that reuse existing carriers and preserve
-- the boundary between source parity and cross-pollination.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Arithmetic.DecimalDigitalRootNonaryExact as Digital
import DASHI.Arithmetic.TriadicDigitalRootPhaseObserverExact as Triadic
import DASHI.Foundations.Phase3RootCharacterWeldExact as Root3
import DASHI.Foundations.TernaryNineRingFieldFibreSeparationExact as Nine
import DASHI.Foundations.CyclicNineCharacterPullbackExact as Pullback
import DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact as Separation

------------------------------------------------------------------------
-- Regression witnesses across the weld.
------------------------------------------------------------------------

zetaInverseRegression :
  Root3.phaseInverse Phase.phase1 ≡ Phase.phase2
zetaInverseRegression = Root3.zetaInverseIsZetaSquared

characterRotationRegression :
  Root3.character Phase.phase2 (Root3.zetaRotate Phase.phase1)
  ≡ Root3.phaseMul Phase.phase2 (Root3.character Phase.phase2 Phase.phase1)
characterRotationRegression =
  Root3.characterDiagonalizesRotation Phase.phase2 Phase.phase1

f9FrobeniusRegression :
  Nine.f9Cube (Base.tri-mid , Base.tri-high)
  ≡ Nine.f9Conjugate (Base.tri-mid , Base.tri-high)
f9FrobeniusRegression =
  Nine.f9CubeIsFrobenius (Base.tri-mid , Base.tri-high)

f9TraceRetractRegression :
  Nine.frobeniusTraceRetract (Base.tri-high , Base.tri-mid)
  ≡ Base.tri-high
f9TraceRetractRegression =
  Nine.traceRetractIsFirstCoordinate (Base.tri-high , Base.tri-mid)

c9CharacterPullbackRegression :
  Pullback.c9CharacterSectionRow Phase.phase1
  ≡ Root3.characterRow Phase.phase1
c9CharacterPullbackRegression =
  Pullback.c9SectionReproducesC3CharacterTable Phase.phase1

triadicRootSixIsPhaseZero :
  Triadic.rootPhase Digital.root6 ≡ Phase.phase0
triadicRootSixIsPhaseZero =
  Triadic.triadicRootProjectsToPhaseZero
    Digital.root6 Digital.root6IsTriadic

-- Digital root 9 is residue zero in the cyclic C9 lane; this is not the same
-- statement as Frobenius fixedness in the F9 lane.
digitalRootNineIsCyclicZero :
  Digital.rootResidue9 Digital.root9 ≡ Base.non-0
digitalRootNineIsCyclicZero = refl

cyclicNineStillNotAdditiveF9 :
  Separation.Q9NonaryGroupIsomorphism → ⊥
cyclicNineStillNotAdditiveF9 =
  Nine.noAdditiveGroupIdentificationWithC9
