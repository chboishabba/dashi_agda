{-# OPTIONS --safe #-}
module DASHI.Physics.TeleportationPKCausalIdentifiabilityBridgeExact where

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.InverseProblemIdentifiabilityBidiExact as Inverse
import DASHI.Reasoning.FibreRoutingSufficiencyCausalInterventionSnowballExact as Causal
import DASHI.Physics.TeleportationPsychokinesisEvidenceCutExact as PK

-- Exact finite observational collision: same registered outcome, different
-- latent explanation. Illustrative countermodel, not observed PK evidence.
data Explanation : Set where
  proposedNonstandardCoupling ordinaryApparatusCoupling : Explanation

data RegisteredOutcome : Set where
  sameRNGContrast : RegisteredOutcome

registered : Explanation → RegisteredOutcome
registered _ = sameRNGContrast

explanationIdentity : Explanation → Explanation
explanationIdentity e = e

pkCollision : INF.NonFactorabilityWitness registered explanationIdentity
pkCollision = INF.nonFactorabilityWitness
  proposedNonstandardCoupling ordinaryApparatusCoupling refl (λ ())

noMechanismIdentificationFromSingleContrast :
  INF.FactorsThrough registered explanationIdentity → ⊥
noMechanismIdentificationFromSingleContrast =
  INF.witnessRulesOutEveryFlatFactorisation pkCollision

-- Same obstruction translated into the canonical inverse-problem owner.
singleChannel : Inverse.ForwardModel
singleChannel = Inverse.forward-model
  Explanation RegisteredOutcome registered
  "illustrative RNG-contrast observational projection"

singleChannelDegeneracy : Inverse.DistinctDegeneracyWitness singleChannel
singleChannelDegeneracy = Inverse.distinct-degeneracy-witness
  (Inverse.identifiability-witness
    proposedNonstandardCoupling ordinaryApparatusCoupling refl)
  (λ ())

singleChannelNotGloballyIdentifiable :
  Inverse.GloballyIdentifiable singleChannel → ⊥
singleChannelNotGloballyIdentifiable =
  Inverse.distinctDegeneracyRefutesGlobalIdentifiability
    singleChannel singleChannelDegeneracy

-- Declared second discriminator is a chosen distinguishing coordinate;
-- its eventual empirical calibration is NOT provided by this theorem.
data CouplingFingerprint : Set where
  proposedSignature ordinarySignature : CouplingFingerprint

fingerprint : Explanation → CouplingFingerprint
fingerprint proposedNonstandardCoupling = proposedSignature
fingerprint ordinaryApparatusCoupling = ordinarySignature

pairedChannels : Inverse.MultiChannelModel
pairedChannels = Inverse.multi-channel-model
  Explanation RegisteredOutcome CouplingFingerprint
  registered fingerprint
  "single RNG contrast plus independently validated coupling discriminator"

pairedSeparates : Inverse.FusionSeparates pairedChannels
pairedSeparates = Inverse.fusion-separates proof
  where
  proof : (x y : Explanation) →
    Inverse.f₁ pairedChannels x ≡ Inverse.f₁ pairedChannels y →
    Inverse.f₂ pairedChannels x ≡ Inverse.f₂ pairedChannels y →
    x ≡ y
  proof proposedNonstandardCoupling proposedNonstandardCoupling _ _ = refl
  proof proposedNonstandardCoupling ordinaryApparatusCoupling _ ()
  proof ordinaryApparatusCoupling proposedNonstandardCoupling _ ()
  proof ordinaryApparatusCoupling ordinaryApparatusCoupling _ _ = refl

pairedIdentifies :
  (x y : Explanation) →
  Inverse.f₁ pairedChannels x ≡ Inverse.f₁ pairedChannels y →
  Inverse.f₂ pairedChannels x ≡ Inverse.f₂ pairedChannels y →
  x ≡ y
pairedIdentifies = Inverse.fusionEqualityIdentifies
  pairedChannels pairedSeparates

-- Existing Ibrahim causal boundary is consumed, not reconstructed.
causalPriorArt : Causal.FibreSufficiencyCausalInterventionBoundary
causalPriorArt = Causal.canonicalFibreSufficiencyCausalInterventionBoundary

historicalReport : PK.AttributedClaim
historicalReport = PK.afrlDavis2004
