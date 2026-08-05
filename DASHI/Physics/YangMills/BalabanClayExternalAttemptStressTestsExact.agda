module DASHI.Physics.YangMills.BalabanClayExternalAttemptStressTestsExact where

------------------------------------------------------------------------
-- EXTERNAL STRESS-TEST SOURCES
--
-- Henry Watt, "The Yang-Mills Mass Gap: From Proof Attempts to Dissolution
-- by Recontextualisation", WCCC Principia, Document 35 v12 (2026).
-- No DOI recorded.
--
-- Harold D. Kirk III, "Mass Gap and Nontriviality for Four-Dimensional SU(2)
-- Yang-Mills via Karcher Blocking and Exact Haar-Pivot Matching" (2026).
-- No DOI recorded in the supplied manuscript.
--
-- Hans Henrik Rugh, "Cones and gauges in complex spaces: Spectral gaps and
-- complex Perron-Frobenius theory", Annals of Mathematics 171 (2010),
-- 1707--1752. DOI: 10.4007/annals.2010.171.1707.
--
-- These sources are not imported as proof authority.  Their useful failure
-- modes are discharged by the checked DASHI countermodels below.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayLowerBoundCountermodelExact as Lower
import DASHI.Physics.YangMills.BalabanClayUniformPerronContractionExact as Perron
import DASHI.Physics.YangMills.BalabanClayNormingFamilyOperatorBoundExact as Norming

factorMismatchDoesNotForceGapCollapse :
  Lower.VanishingBoundPositiveQuantityCountermodel
factorMismatchDoesNotForceGapCollapse = Lower.factorMismatchCountermodel

finiteConeDiameterDoesNotGiveUniformDiameter :
  ∀ proposedBound →
  (∀ extent →
    Perron._≤ᴺ_
      (Perron.finiteVolumeProjectiveDiameter extent)
      proposedBound) →
  Perron.Empty
finiteConeDiameterDoesNotGiveUniformDiameter = Perron.noUniformDiameterBound

oneObservableDoesNotGiveOperatorNorm :
  Norming.NonNormingTestCountermodel
oneObservableDoesNotGiveOperatorNorm =
  Norming.oneObservableDoesNotControlOperatorNorm

externalAttemptStressTestsLevel : ProofLevel
externalAttemptStressTestsLevel = machineChecked
