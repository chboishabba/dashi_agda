module Ontology.DNA.SynthesisSequencingRiskSurface where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (fst; snd)
open import Data.Vec using (Vec)

open import Ontology.DNA.Supervoxel4Adic using (Base)

import Ontology.DNA.ChannelCodingSurface as CCS
import Ontology.DNA.CrossoverAbstractChannelLaws as CACL
import Ontology.DNA.CrossoverSemanticChecksumLaws as CSCL

------------------------------------------------------------------------
-- Small bounded synthesis/sequencing-facing risk owner surface for the
-- localized DNA lane.
--
-- This remains interface-like and theorem-thin. It does not claim realistic
-- wet-lab validity. It only gives typed risk categories over the current
-- physical-channel carrier and exact compatibility witnesses with the
-- already-landed crossover/channel/checksum owners.

data RiskLevel : Set where
  low medium high : RiskLevel

classifyRiskLevel : Nat → RiskLevel
classifyRiskLevel zero = low
classifyRiskLevel (suc zero) = medium
classifyRiskLevel (suc (suc _)) = high

record SynthesisSequencingRiskProfile : Set where
  constructor synthesisSequencingRiskProfile
  field
    substitution : Nat
    indel : Nat
    dropout : Nat
    substitutionLevel : RiskLevel
    indelLevel : RiskLevel
    dropoutLevel : RiskLevel
    recoveryBoundary : Nat

riskProfile :
  CCS.PhysicalChannelModel → Nat → SynthesisSequencingRiskProfile
riskProfile ch recoveryBoundary =
  synthesisSequencingRiskProfile
    (CCS.PhysicalChannelModel.substitutionRisk ch)
    (CCS.PhysicalChannelModel.indelRisk ch)
    (CCS.PhysicalChannelModel.dropoutRisk ch)
    (classifyRiskLevel (CCS.PhysicalChannelModel.substitutionRisk ch))
    (classifyRiskLevel (CCS.PhysicalChannelModel.indelRisk ch))
    (classifyRiskLevel (CCS.PhysicalChannelModel.dropoutRisk ch))
    recoveryBoundary

record SynthesisSequencingRiskSurface : Set₁ where
  field
    integratedChannel : CCS.IntegratedChannelSurface
    abstractChannel : CACL.CrossoverAbstractChannelLawSurface
    semanticChecksum : CSCL.CrossoverSemanticChecksumLawSurface
    profile : SynthesisSequencingRiskProfile

    channelProfileSubstitutionExact :
      SynthesisSequencingRiskProfile.substitution profile
        ≡
      CCS.PhysicalChannelModel.substitutionRisk
        (CCS.IntegratedChannelSurface.channel integratedChannel)

    channelProfileIndelExact :
      SynthesisSequencingRiskProfile.indel profile
        ≡
      CCS.PhysicalChannelModel.indelRisk
        (CCS.IntegratedChannelSurface.channel integratedChannel)

    channelProfileDropoutExact :
      SynthesisSequencingRiskProfile.dropout profile
        ≡
      CCS.PhysicalChannelModel.dropoutRisk
        (CCS.IntegratedChannelSurface.channel integratedChannel)

    recoveryBoundaryExact :
      SynthesisSequencingRiskProfile.recoveryBoundary profile
        ≡
      CCS.IntegratedChannelSurface.recoveryBoundary integratedChannel

    emitLengthRiskCompatible :
      ∀ {n} (xs : Vec Base n) →
      CACL.CrossoverAbstractChannelLawSurface.emitLengthCanonical
        abstractChannel xs
      ≡
      CACL.CrossoverAbstractChannelLawSurface.emitLengthCanonical
        abstractChannel xs

    semanticChecksumRiskCompatible :
      ∀ {n} (xs : Vec Base n) →
      CSCL.CrossoverSemanticChecksumLawSurface.emitSemanticChecksumPairCanonical
        semanticChecksum xs
      ≡
      CSCL.CrossoverSemanticChecksumLawSurface.emitSemanticChecksumPairCanonical
        semanticChecksum xs

    nextStepAdmissibilityRiskCompatible :
      ∀ {n} (xs : Vec Base n) (b : Base) →
      CSCL.CrossoverSemanticChecksumLawSurface.emitNextStepAdmissibilityCanonical
        semanticChecksum xs b
      ≡
      CSCL.CrossoverSemanticChecksumLawSurface.emitNextStepAdmissibilityCanonical
        semanticChecksum xs b

profileSubstitutionExactWitness :
  SynthesisSequencingRiskProfile.substitution
    (riskProfile
      (CCS.IntegratedChannelSurface.channel CCS.integratedChannelSurface)
      (CCS.IntegratedChannelSurface.recoveryBoundary CCS.integratedChannelSurface))
    ≡
  CCS.PhysicalChannelModel.substitutionRisk
    (CCS.IntegratedChannelSurface.channel CCS.integratedChannelSurface)
profileSubstitutionExactWitness = refl

profileIndelExactWitness :
  SynthesisSequencingRiskProfile.indel
    (riskProfile
      (CCS.IntegratedChannelSurface.channel CCS.integratedChannelSurface)
      (CCS.IntegratedChannelSurface.recoveryBoundary CCS.integratedChannelSurface))
    ≡
  CCS.PhysicalChannelModel.indelRisk
    (CCS.IntegratedChannelSurface.channel CCS.integratedChannelSurface)
profileIndelExactWitness = refl

profileDropoutExactWitness :
  SynthesisSequencingRiskProfile.dropout
    (riskProfile
      (CCS.IntegratedChannelSurface.channel CCS.integratedChannelSurface)
      (CCS.IntegratedChannelSurface.recoveryBoundary CCS.integratedChannelSurface))
    ≡
  CCS.PhysicalChannelModel.dropoutRisk
    (CCS.IntegratedChannelSurface.channel CCS.integratedChannelSurface)
profileDropoutExactWitness = refl

recoveryBoundaryExactWitness :
  SynthesisSequencingRiskProfile.recoveryBoundary
    (riskProfile
      (CCS.IntegratedChannelSurface.channel CCS.integratedChannelSurface)
      (CCS.IntegratedChannelSurface.recoveryBoundary CCS.integratedChannelSurface))
    ≡
  CCS.IntegratedChannelSurface.recoveryBoundary CCS.integratedChannelSurface
recoveryBoundaryExactWitness = refl

emitLengthRiskCompatibleWitness :
  ∀ {n} (xs : Vec Base n) →
  CACL.CrossoverAbstractChannelLawSurface.emitLengthCanonical
    CACL.crossoverAbstractChannelLawSurface xs
  ≡
  CACL.CrossoverAbstractChannelLawSurface.emitLengthCanonical
    CACL.crossoverAbstractChannelLawSurface xs
emitLengthRiskCompatibleWitness xs = refl

semanticChecksumRiskCompatibleWitness :
  ∀ {n} (xs : Vec Base n) →
  CSCL.CrossoverSemanticChecksumLawSurface.emitSemanticChecksumPairCanonical
    CSCL.crossoverSemanticChecksumLawSurface xs
  ≡
  CSCL.CrossoverSemanticChecksumLawSurface.emitSemanticChecksumPairCanonical
    CSCL.crossoverSemanticChecksumLawSurface xs
semanticChecksumRiskCompatibleWitness xs = refl

nextStepAdmissibilityRiskCompatibleWitness :
  ∀ {n} (xs : Vec Base n) (b : Base) →
  CSCL.CrossoverSemanticChecksumLawSurface.emitNextStepAdmissibilityCanonical
    CSCL.crossoverSemanticChecksumLawSurface xs b
  ≡
  CSCL.CrossoverSemanticChecksumLawSurface.emitNextStepAdmissibilityCanonical
    CSCL.crossoverSemanticChecksumLawSurface xs b
nextStepAdmissibilityRiskCompatibleWitness xs b = refl

synthesisSequencingRiskSurface : SynthesisSequencingRiskSurface
synthesisSequencingRiskSurface = record
  { integratedChannel = CCS.integratedChannelSurface
  ; abstractChannel = CACL.crossoverAbstractChannelLawSurface
  ; semanticChecksum = CSCL.crossoverSemanticChecksumLawSurface
  ; profile =
      riskProfile
        (CCS.IntegratedChannelSurface.channel CCS.integratedChannelSurface)
        (CCS.IntegratedChannelSurface.recoveryBoundary CCS.integratedChannelSurface)
  ; channelProfileSubstitutionExact = profileSubstitutionExactWitness
  ; channelProfileIndelExact = profileIndelExactWitness
  ; channelProfileDropoutExact = profileDropoutExactWitness
  ; recoveryBoundaryExact = recoveryBoundaryExactWitness
  ; emitLengthRiskCompatible = emitLengthRiskCompatibleWitness
  ; semanticChecksumRiskCompatible = semanticChecksumRiskCompatibleWitness
  ; nextStepAdmissibilityRiskCompatible =
      nextStepAdmissibilityRiskCompatibleWitness
  }
