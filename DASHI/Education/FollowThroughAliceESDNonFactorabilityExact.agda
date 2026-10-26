module DASHI.Education.FollowThroughAliceESDNonFactorabilityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Biology.AliceBrownCorpusLoom as Alice
import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Braid
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Principles

-- Original Follow Through evaluations, House et al.'s critique, and later
-- Direct Instruction literature are DISTINCT historical source roots.
-- These synthetic cases are DASHI mathematics, not recovered study records.
-- A test score alone does not determine whether a student exercised
-- constitutive epistemic agency (voice, contestation, local choice).
data EducationHistory : Set where
  masteryWithConstitutiveVoice : EducationHistory
  masteryWithoutConstitutiveVoice : EducationHistory

data AcademicSurface : Set where equalMastery : AcademicSurface
data AgencySurface : Set where agentic : AgencySurface
                               nonAgentic : AgencySurface

academicProjection : EducationHistory → AcademicSurface
academicProjection masteryWithConstitutiveVoice = equalMastery
academicProjection masteryWithoutConstitutiveVoice = equalMastery

agencyProjection : EducationHistory → AgencySurface
agencyProjection masteryWithConstitutiveVoice = agentic
agencyProjection masteryWithoutConstitutiveVoice = nonAgentic

agencyDiffers :
  agencyProjection masteryWithConstitutiveVoice ≡
  agencyProjection masteryWithoutConstitutiveVoice → ⊥
agencyDiffers ()

academicScoreCannotDetermineAgencyWitness :
  INF.NonFactorabilityWitness academicProjection agencyProjection
academicScoreCannotDetermineAgencyWitness =
  INF.nonFactorabilityWitness
    masteryWithConstitutiveVoice
    masteryWithoutConstitutiveVoice
    refl agencyDiffers

academicScoreCannotDetermineAgency :
  INF.FactorsThrough academicProjection agencyProjection → ⊥
academicScoreCannotDetermineAgency =
  INF.witnessRulesOutEveryFlatFactorisation
    academicScoreCannotDetermineAgencyWitness

-- Existing canonical owners are retained, not restated or assigned
-- to the historical researchers as discoveries.
aliceCorpus : Alice.AliceBrownCorpusLoom
aliceCorpus = Alice.canonicalAliceBrownCorpusLoom

esdEvidenceBraid : Braid.EvidenceBraidBoundary
esdEvidenceBraid = Braid.canonicalEvidenceBraidBoundary

transferCandidateCount : Nat
transferCandidateCount = Principles.transferablePrincipleCount

claimBoundary : String
claimBoundary =
  "Synthetic non-factorability only: equal assessed attainment does not identify agency. Not an estimate of Direct Instruction effectiveness, an ESD outcome, or a recovered Follow Through student record."
