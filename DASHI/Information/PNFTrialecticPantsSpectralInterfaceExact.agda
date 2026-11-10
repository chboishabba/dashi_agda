module DASHI.Information.PNFTrialecticPantsSpectralInterfaceExact where

-- Two independent compatibility tests are retained:
-- (1) local spectral evidence on the 369 A/B, B/C, C/A cover agrees
--     at overlapping entries and descends to a global 3x3 evidence chart;
-- (2) a selected hyperfabric/pants seam has a full BranchChannel
--     InterfaceMatch (proposition, capacity, phase, wave and openness).
-- One compatibility test NEVER pays the other automatically.
--
-- This is finite interface transport; not a TQFT, measure-theoretic
-- Marchenko-Pastur law, global PSD gluing, or triadic semantic admission.

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Reasoning.TypedHyperfabricPantsGluingBridgeExact as HyperPants
import DASHI.Information.PNFTrialecticSpectralDescentExact as Charts

record SpectralPantsJointSeam (View : Set) : Set₁ where
  field
    spectralCharts : Charts.SpectralMatchingFamily View
    realizeChannel : View → Pants.BranchChannel
    channelInterfaceAtA :
      Pants.InterfaceMatch
        (realizeChannel
          (Charts.aaAB (Charts.localAB spectralCharts)))
        (realizeChannel
          (Charts.aaCA (Charts.localCA spectralCharts)))

open SpectralPantsJointSeam public

globalObserverFromSpectralPantsSeam :
  {View : Set} →
  SpectralPantsJointSeam View →
  Observer.ObserverMatrix3 View
globalObserverFromSpectralPantsSeam s =
  Charts.glueSpectral (spectralCharts s)

-- The observer overlap equality survives the domain-specific
-- realization as a channel. It is not the *whole* InterfaceMatch.
sameRealizedChannelAtA :
  {View : Set} →
  (s : SpectralPantsJointSeam View) →
  realizeChannel s (Charts.aaAB (Charts.localAB (spectralCharts s)))
  ≡ realizeChannel s (Charts.aaCA (Charts.localCA (spectralCharts s)))
sameRealizedChannelAtA s =
  cong (realizeChannel s) (Charts.overlapA (spectralCharts s))

pantsPropositionAgreesAtA :
  {View : Set} →
  (s : SpectralPantsJointSeam View) →
  Pants.propositionType
    (Pants.channelBoundary
      (realizeChannel s (Charts.aaAB (Charts.localAB (spectralCharts s)))))
  ≡
  Pants.propositionType
    (Pants.channelBoundary
      (realizeChannel s (Charts.aaCA (Charts.localCA (spectralCharts s)))))
pantsPropositionAgreesAtA s =
  Pants.InterfaceMatch.propositionMatches (channelInterfaceAtA s)

pantsCapacityAgreesAtA :
  {View : Set} →
  (s : SpectralPantsJointSeam View) →
  Pants.boundaryCapacity
    (Pants.channelBoundary
      (realizeChannel s (Charts.aaAB (Charts.localAB (spectralCharts s)))))
  ≡
  Pants.boundaryCapacity
    (Pants.channelBoundary
      (realizeChannel s (Charts.aaCA (Charts.localCA (spectralCharts s)))))
pantsCapacityAgreesAtA s =
  Pants.InterfaceMatch.capacityMatches (channelInterfaceAtA s)

-- Existing concrete pants/hyperfabric witness is reused as its
-- original owner; nothing here claims that every arbitrary spectral
-- chart can inherit that specimen's interface.
existingCanonicalHyperfabricPantsInterfaceReused :
  HyperPants.seamInterface HyperPants.canonicalPantsGluing
  ≡ Pants.outerInnerMatch
existingCanonicalHyperfabricPantsInterfaceReused =
  HyperPants.canonicalPantsGluingReusesExactInterfaceMatch

-- Pointwise spectral observations can be mapped and reglued exactly.
-- Covariance eigendecomposition, spectral clipping, MP null calibration
-- and covariance PSD are NONPOINTWISE, and are outside this theorem.
pointwiseSpectralDescentPreserved :
  {A B : Set} → (f : A → B) →
  (s : SpectralPantsJointSeam A) →
  Charts.mapObserver f (globalObserverFromSpectralPantsSeam s)
  ≡ Charts.glueSpectral
      (Charts.mapMatchingFamily f (spectralCharts s))
pointwiseSpectralDescentPreserved f s =
  Charts.pointwiseSpectralClassificationCommutesWithGluing
    f (spectralCharts s)
