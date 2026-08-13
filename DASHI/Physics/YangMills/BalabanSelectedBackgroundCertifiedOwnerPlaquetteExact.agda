module DASHI.Physics.YangMills.BalabanSelectedBackgroundCertifiedOwnerPlaquetteExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Ramon E. Moore, R. Baker Kearfott, Michael J. Cloud,
-- "Introduction to Interval Analysis", SIAM, 2009.
-- DOI: 10.1137/1.9780898717716.
--
-- DASHI CONTRIBUTION
--
-- Round 47 reduced G2 to correlated singleton extraction plus four owner
-- inequalities with slack.  This module makes the quantitative route more
-- concrete: the four owner inequalities are generated from certified rational
-- upper enclosures.  A finite K_A^+ / Green-kernel computation may therefore
-- emit rational centres/radii and coefficient certificates; Agda converts them
-- to the exact slack object and then to LiteralSelectedPlaquetteFamily.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualAuthorityExact as Authority
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedSingletonClosureExact as Closure
import DASHI.Physics.YangMills.BalabanSelectedCertifiedOwnerEnclosureExact as Certified
import DASHI.Physics.YangMills.BalabanSelectedBackgroundLiteralPlaquetteFamilyProducerExact as Producer
import DASHI.Physics.YangMills.BalabanSelectedSinglePlaquetteWitnessExact as Plaquette

record CertifiedCorrelatedSingleton
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₂ where
  field
    extraction : Closure.CorrelatedSingletonExtractionData
      background bondField plaquette
    ownerEnclosures :
      Certified.CertifiedCorrelatedOwnerEnclosures
        (Authority.canonicalCorrelatedResidualFamily
          (Closure.residualAuthority extraction))
        (Wilson.plaquetteCrossCharge bondField plaquette)

open CertifiedCorrelatedSingleton public

certifiedCorrelatedSingletonToWithSlack :
  ∀ {background bondField plaquette} →
  CertifiedCorrelatedSingleton background bondField plaquette →
  Producer.CorrelatedSingletonWithSlack background bondField plaquette
certifiedCorrelatedSingletonToWithSlack data = record
  { Producer.CorrelatedSingletonWithSlack.extraction = extraction data
  ; Producer.CorrelatedSingletonWithSlack.ownerBounds =
      Certified.certifiedEnclosuresToOwnerBounds (ownerEnclosures data) }

certifiedCorrelatedSingletonToLiteralWitness :
  ∀ {background bondField plaquette} →
  CertifiedCorrelatedSingleton background bondField plaquette →
  Plaquette.LiteralSelectedPlaquetteWitness background bondField plaquette
certifiedCorrelatedSingletonToLiteralWitness data =
  Producer.correlatedSingletonWithSlackToLiteralWitness
    (certifiedCorrelatedSingletonToWithSlack data)

record CertifiedCorrelatedSingletonFamily
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4) : Set₂ where
  field
    atPlaquette : ∀ plaquette →
      CertifiedCorrelatedSingleton background bondField plaquette

open CertifiedCorrelatedSingletonFamily public

certifiedCorrelatedSingletonFamilyToLiteralFamily :
  ∀ {background bondField} →
  CertifiedCorrelatedSingletonFamily background bondField →
  Plaquette.LiteralSelectedPlaquetteFamily background bondField
certifiedCorrelatedSingletonFamilyToLiteralFamily family = record
  { Plaquette.LiteralSelectedPlaquetteFamily.atPlaquette = λ plaquette →
      certifiedCorrelatedSingletonToLiteralWitness (atPlaquette family plaquette) }

selectedCertifiedOwnerPlaquetteLevel : ProofLevel
selectedCertifiedOwnerPlaquetteLevel = machineChecked

selectedCertifiedOwnerPlaquetteFamilyLevel : ProofLevel
selectedCertifiedOwnerPlaquetteFamilyLevel = machineChecked
