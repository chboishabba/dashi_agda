module DASHI.Biology.GABANeuroAIContextParetoSnowballRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.GABANeuroAIContextParetoSnowballExact as P
import DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact as Pareto
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball

paretoOwnerReused : Pareto.RecursiveParetoCompatibility
paretoOwnerReused = P.paretoCompatibility P.canonicalAcquisitionParetoBoundary

peripheralCentralRoutesToExperiment :
  P.discoveryRoute P.peripheralCentralTransportAcquisition ≡ Snowball.experimentalDesign
peripheralCentralRoutesToExperiment = refl

crossParticipantDecoderRemainsUnpaid :
  P.status P.crossParticipantDecoderTransferAcquisition ≡ P.unresolvedTransfer
crossParticipantDecoderRemainsUnpaid = refl

metaNeuroAIProvenanceRemainsSplit :
  P.status P.metaNeuroAIAcquisition ≡ P.paidAndWelded
metaNeuroAIProvenanceRemainsSplit = refl

canonicalParetoSnowballRegression : P.GABANeuroAIParetoSnowballBoundary
canonicalParetoSnowballRegression = P.canonicalGABANeuroAIParetoSnowballBoundary
