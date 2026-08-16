module DASHI.Moonshine.OggPhaseFrickeSynthesisRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁)

import Base369 as Base
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.D4IrrepFiniteFrickeEquivariantExact as D4Fricke
import DASHI.Biology.JFineCoarseRelativeScaleExact as Scale
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Fricke
import DASHI.Biology.TernaryPhaseQuotientJCoarseBridgeExact as Coarse
import DASHI.Cognition.PhaseEnrichedTrit as Phase3
import DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact as Nonary
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Foundations.TernaryPhaseShapeIncidenceExact as Incidence

------------------------------------------------------------------------
-- Exact 27 -> 9 -> 3^9 coarse/fine weld.
------------------------------------------------------------------------

phaseQuotientRoundTrip :
  (pair : Phase.PhaseQuotient9) →
  Coarse.balancedPairToPhaseQuotient
    (Coarse.phaseQuotientToBalancedPair pair) ≡ pair
phaseQuotientRoundTrip = Coarse.phaseQuotientRoundTrip

jCoarseIsNine : Scale.jCoarseFrequency ≡ 9
jCoarseIsNine = Coarse.jCoarseCountMatchesPhaseQuotient

jFineIsStructuredThreePowerNine :
  Fine.phaseFineCardinality ≡ 19683
jFineIsStructuredThreePowerNine = Fine.phaseFineCardinalityIs19683

jAbsoluteIsStructuredThreePowerEleven :
  Fine.phaseAbsoluteCardinality ≡ Scale.jAbsoluteFineFrequency
jAbsoluteIsStructuredThreePowerEleven =
  Fine.phaseAbsoluteMatchesExistingJScale

fineCodecEncodeDecode :
  (fine : Harmonic.FineFrequency) →
  Fine.encodePhaseFineField (Fine.decodePhaseFineField fine) ≡ fine
fineCodecEncodeDecode = Fine.encodeAfterDecodePhaseFine

------------------------------------------------------------------------
-- Joint C3-phase / S3-shape incidence.
------------------------------------------------------------------------

cyclicUnitPhase0IsIdentity :
  Incidence.shapeAtFactor Phase3.phase0 (inj₁ Phase.unitCyclic)
  ≡ Shape.identityShape
cyclicUnitPhase0IsIdentity = Incidence.unitCyclicPhase0IsIdentity

reflectiveUnitPhase2IsTransposition :
  Incidence.shapeAtFactor Phase3.phase2 (inj₁ Phase.unitReflective)
  ≡ Shape.transpositionShape
reflectiveUnitPhase2IsTransposition =
  Incidence.unitReflectivePhase2IsTransposition

------------------------------------------------------------------------
-- Nine-state carrier equality does not collapse C3 x C3 into C9.
------------------------------------------------------------------------

q9AndC9CannotBeGroupIsomorphic :
  Nonary.Q9NonaryGroupIsomorphism → ⊥
q9AndC9CannotBeGroupIsomorphic =
  Nonary.q9NonaryGroupIsomorphismImpossible

------------------------------------------------------------------------
-- The spatial j=4 five-species restriction is carried through the completed
-- ten-sector finite Fricke chart, with orientation flip exactly complement.
------------------------------------------------------------------------

mode09CarriesMultiplicityTwo :
  D4Fricke.j4MultiplicityAtMode Fricke.mode09 ≡ 2
mode09CarriesMultiplicityTwo = D4Fricke.j4Mode09MultiplicityIsTwo

mode45CarriesMultiplicityTwo :
  D4Fricke.j4MultiplicityAtMode Fricke.mode45 ≡ 2
mode45CarriesMultiplicityTwo = D4Fricke.j4Mode45MultiplicityIsTwo

finiteFrickeEquivariance :
  (sector : D4Fricke.D4OrientedSector) →
  D4Fricke.sectorToCompletedFine (D4Fricke.flipSector sector)
  ≡
  Fricke.complementState (D4Fricke.sectorToCompletedFine sector)
finiteFrickeEquivariance = D4Fricke.sectorComplementEquivariant
