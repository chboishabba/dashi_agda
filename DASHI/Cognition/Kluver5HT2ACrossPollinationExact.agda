module DASHI.Cognition.Kluver5HT2ACrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Biology.KluverFormConstantPsychedelicBoundaryExact as KluverBoundary
import DASHI.Biology.Psychedelic5HT2AAttentionBoundaryExact as HT2A
import DASHI.Cognition.LogPolarKluverDerivationExact as LogPolar

------------------------------------------------------------------------
-- CROSS-POLLINATION BOUNDARY
--
-- This module deliberately composes two separately attributed lanes:
--
--   A. cortical mode / log-polar projection -> Kluever geometry
--   B. 5-HT2A-dependent psychedelic perturbation -> candidate relevance /
--      salience reweighting
--
-- The composition is a DASHI hypothesis architecture.  Neither source family
-- is attributed the claims of the other, and neither geometry nor receptor
-- evidence is treated as a unique inverse explanation of a reported percept.
------------------------------------------------------------------------

data FiveHT2AAloneDerivesKluverGeometry : Set where

data KluverGeometryIdentifiesFiveHT2ACause : Set where

data SalienceCandidateProvesEntityMessage : Set where

fiveHT2ADoesNotAloneDeriveKluverGeometry :
  FiveHT2AAloneDerivesKluverGeometry → ⊥
fiveHT2ADoesNotAloneDeriveKluverGeometry ()

kluverGeometryDoesNotIdentifyFiveHT2ACause :
  KluverGeometryIdentifiesFiveHT2ACause → ⊥
kluverGeometryDoesNotIdentifyFiveHT2ACause ()

salienceCandidateDoesNotProveEntityMessage :
  SalienceCandidateProvesEntityMessage → ⊥
salienceCandidateDoesNotProveEntityMessage ()

record Kluver5HT2ACrossPollination : Set where
  constructor kluver5HT2ACrossPollination
  field
    logPolarGeometry :
      LogPolar.FiniteLogPolarSpiralDerivation

    corticalMagnification :
      LogPolar.FiniteCorticalMagnificationWitness

    logPolarBoundary :
      LogPolar.LogPolarKluverAuthorityBoundary

    psychedelic5HT2ABoundary :
      HT2A.Psychedelic5HT2AAttentionBoundary

    psychedelicSalienceComposition :
      HT2A.PsychedelicSalienceComposition

    kluverPsychedelicBoundary :
      KluverBoundary.KluverPsychedelicBoundary

    geometryAndPharmacologyAreSeparateEvidenceLayers : Bool
    geometryAndPharmacologyAreSeparateEvidenceLayersIsTrue :
      geometryAndPharmacologyAreSeparateEvidenceLayers ≡ true

    jointMechanismIsCandidate : Bool
    jointMechanismIsCandidateIsTrue :
      jointMechanismIsCandidate ≡ true

    jointMechanismEmpiricallyClosed : Bool
    jointMechanismEmpiricallyClosedIsFalse :
      jointMechanismEmpiricallyClosed ≡ false

    visualFormUniquelyDeterminesDrugOrReceptor : Bool
    visualFormUniquelyDeterminesDrugOrReceptorIsFalse :
      visualFormUniquelyDeterminesDrugOrReceptor ≡ false

    feltImportanceProvesExternalAgency : Bool
    feltImportanceProvesExternalAgencyIsFalse :
      feltImportanceProvesExternalAgency ≡ false

open Kluver5HT2ACrossPollination public

canonicalKluver5HT2ACrossPollination :
  Kluver5HT2ACrossPollination
canonicalKluver5HT2ACrossPollination =
  kluver5HT2ACrossPollination
    LogPolar.canonicalFiniteLogPolarSpiralDerivation
    LogPolar.canonicalFiniteCorticalMagnificationWitness
    LogPolar.canonicalLogPolarKluverAuthorityBoundary
    HT2A.canonicalPsychedelic5HT2AAttentionBoundary
    HT2A.canonicalPsychedelicSalienceComposition
    KluverBoundary.canonicalKluverPsychedelicBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
