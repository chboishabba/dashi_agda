module DASHI.Governance.DecisionPotentialAuthorityOrthogonalityExact where

------------------------------------------------------------------------
-- DECISION POTENTIAL != LEGAL AUTHORITY
--
-- Cross-pollination of the finite active-inference comparison with the merged
-- parent authority-routing fibre.  A potential can supply pressure over a
-- decision fibre; it does not thereby issue authority over that fibre.
-- Conversely, an authority route does not determine an observer's potential
-- landscape.
--
-- These are structural finite countermodels, not legal advice and not a claim
-- that Nat-valued potential is an empirical measure of any real institution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.PNF.ActiveInferenceFibreBoundaryExact as Potential
import DASHI.Ontology.ProgenitorParentAuthorityRoutingNonfactorabilityExact as ParentAuthority
open import DASHI.Ontology.ProgenitorParentProjectionFibre

record PotentialAuthorityEpisode : Set where
  constructor potentialAuthorityEpisode
  field
    potentialObserver : Potential.PolicyObserver
    candidatePolicy : Potential.Policy
    authorityCarrier : ParentCarrier

open PotentialAuthorityEpisode public

potentialReadout : PotentialAuthorityEpisode → Nat
potentialReadout episode =
  Potential.expectedPotential
    (potentialObserver episode)
    (candidatePolicy episode)

authorityReadout : PotentialAuthorityEpisode → ParentAuthority.ParentAuthorityRoute
authorityReadout episode =
  ParentAuthority.routeParentAuthority (authorityCarrier episode)

------------------------------------------------------------------------
-- 1. Same potential, different authority.
------------------------------------------------------------------------

personRemainDonor personRemainAdoptive : PotentialAuthorityEpisode
personRemainDonor =
  potentialAuthorityEpisode
    Potential.person Potential.remain anonymousDonorCarrier
personRemainAdoptive =
  potentialAuthorityEpisode
    Potential.person Potential.remain adoptiveCarrier

samePotentialAcrossDifferentAuthority :
  potentialReadout personRemainDonor
  ≡ potentialReadout personRemainAdoptive
samePotentialAcrossDifferentAuthority = refl

authorityDiffersAtSamePotential :
  authorityReadout personRemainDonor
  ≡ authorityReadout personRemainAdoptive → ⊥
authorityDiffersAtSamePotential = ParentAuthority.routesDiffer

potentialCannotDetermineAuthorityWitness :
  NF.NonFactorabilityWitness potentialReadout authorityReadout
potentialCannotDetermineAuthorityWitness =
  NF.nonFactorabilityWitness
    personRemainDonor
    personRemainAdoptive
    samePotentialAcrossDifferentAuthority
    authorityDiffersAtSamePotential

potentialCannotIssueAuthority :
  NF.FactorsThrough potentialReadout authorityReadout → ⊥
potentialCannotIssueAuthority =
  NF.witnessRulesOutEveryFlatFactorisation
    potentialCannotDetermineAuthorityWitness

------------------------------------------------------------------------
-- 2. Same authority, different observer-indexed potential.
------------------------------------------------------------------------

institutionRemainDonor : PotentialAuthorityEpisode
institutionRemainDonor =
  potentialAuthorityEpisode
    Potential.institution Potential.remain anonymousDonorCarrier

sameAuthorityAcrossDifferentPotentialObservers :
  authorityReadout personRemainDonor
  ≡ authorityReadout institutionRemainDonor
sameAuthorityAcrossDifferentPotentialObservers = refl

personInstitutionRemainPotentialDiffer :
  potentialReadout personRemainDonor
  ≡ potentialReadout institutionRemainDonor → ⊥
personInstitutionRemainPotentialDiffer ()

authorityCannotDeterminePotentialWitness :
  NF.NonFactorabilityWitness authorityReadout potentialReadout
authorityCannotDeterminePotentialWitness =
  NF.nonFactorabilityWitness
    personRemainDonor
    institutionRemainDonor
    sameAuthorityAcrossDifferentPotentialObservers
    personInstitutionRemainPotentialDiffer

authorityDoesNotDetermineObserverPotential :
  NF.FactorsThrough authorityReadout potentialReadout → ⊥
authorityDoesNotDetermineObserverPotential =
  NF.witnessRulesOutEveryFlatFactorisation
    authorityCannotDeterminePotentialWitness

------------------------------------------------------------------------
-- 3. Indexed optima remain separate from authority routing.
------------------------------------------------------------------------

observerMinimaDiffer :
  Potential.minimumPolicy Potential.person
  ≡ Potential.minimumPolicy Potential.institution → ⊥
observerMinimaDiffer = Potential.observerIndexedMinimaDiffer

record PotentialAuthorityBoundary : Set where
  constructor potentialAuthorityBoundary
  field
    potentialDeterminesAuthority : Bool
    authorityDeterminesPotential : Bool
    institutionalMinimumIsUniversalMinimum : Bool
    potentialMaySupplyDirectionalPressure : Bool
    authorityRequiresIndependentWitness : Bool

canonicalPotentialAuthorityBoundary : PotentialAuthorityBoundary
canonicalPotentialAuthorityBoundary =
  potentialAuthorityBoundary false false false true true
