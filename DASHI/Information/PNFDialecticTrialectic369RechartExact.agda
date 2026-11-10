module DASHI.Information.PNFDialecticTrialectic369RechartExact where

-- Existing source owners:
-- CellDialectic <-> three 27-state hypervoxels (T^9)
-- ObserverMatrix3 SSPTrit <-> the SAME T^9 carrier.
-- Their composition is a literal two-sided carrier equivalence.
--
-- This is a mathematical *rechart*. Neither ontology, economic factor
-- meaning, psychological status nor MP distribution is transported
-- automatically by this finite bijection.

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Dialectic
import DASHI.Reasoning.Trialectic369HypervoxelUltrametricExact as Trialectic
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Information.PNFTrialecticSpectralDescentExact as Charts
import DASHI.Information.PNFMP36927ChartNaturalityExact as MP369
import DASHI.Information.PNFSpectralGeometry as PNF
import DASHI.Information.PNFMarchenkoPasturFiniteExact as MP

dialecticTo369Observer :
  Dialectic.CellDialectic →
  Observer.ObserverMatrix3 SSP.SSPTrit
dialecticTo369Observer d =
  Trialectic.fabricToObserver (Dialectic.cellDialecticToHyperform d)

observer369ToDialectic :
  Observer.ObserverMatrix3 SSP.SSPTrit →
  Dialectic.CellDialectic
observer369ToDialectic m =
  Dialectic.hyperformToCellDialectic (Trialectic.observerToFabric m)

dialectic369ObserverRoundTrip :
  (d : Dialectic.CellDialectic) →
  observer369ToDialectic (dialecticTo369Observer d) ≡ d
dialectic369ObserverRoundTrip d =
  trans
    (cong Dialectic.hyperformToCellDialectic
      (Trialectic.fabricObserverRoundTrip
        (Dialectic.cellDialecticToHyperform d)))
    (Dialectic.cellDialecticHyperformRoundTrip d)

observer369DialecticRoundTrip :
  (m : Observer.ObserverMatrix3 SSP.SSPTrit) →
  dialecticTo369Observer (observer369ToDialectic m) ≡ m
observer369DialecticRoundTrip m =
  trans
    (cong Trialectic.fabricToObserver
      (Dialectic.hyperformCellDialecticRoundTrip
        (Trialectic.observerToFabric m)))
    (Trialectic.observerFabricRoundTrip m)

-- Explicitly selected numeric encoding is required; the trits
-- themselves are NOT stock returns, PNF activations or MP eigenvalues.
-- Once such an encoding is supplied, the EXISTING MP classifier
-- commutes with chart restriction, as a pointwise operation.
dialecticEncodedMPRestrictionAB :
  (K : PNF.ScalarStructure) →
  (C : MP.MPFiniteCalibration K) →
  (classifier : PNF.NoiseClassifier K (MP.calibratedMPBand K C)) →
  (encode : SSP.SSPTrit → PNF.ScalarStructure.Scalar K) →
  (d : Dialectic.CellDialectic) →
  Charts.abOf
    (MP369.mpClassifyObserver K C classifier
      (Charts.mapObserver encode (dialecticTo369Observer d)))
  ≡
  Charts.mapAB
    (PNF.NoiseClassifier.classify classifier)
    (Charts.abOf
      (Charts.mapObserver encode (dialecticTo369Observer d)))
dialecticEncodedMPRestrictionAB K C classifier encode d =
  MP369.mpClassifiedChartABAgreesWithGlobal
    K C classifier (Charts.mapObserver encode (dialecticTo369Observer d))
