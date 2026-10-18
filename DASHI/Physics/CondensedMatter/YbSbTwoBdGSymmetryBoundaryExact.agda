module DASHI.Physics.CondensedMatter.YbSbTwoBdGSymmetryBoundaryExact where

------------------------------------------------------------------------
-- ATTRIBUTION
--
-- SOURCE: Kataria et al., arXiv:2601.07460 / PRL accepted 3 Aug 2026.
-- They model the normal state by a 3D massive Dirac Hamiltonian, construct
-- an INT BdG model, report a full quasiparticle gap, and calculate
-- zero-energy SABS plus a linearly dispersing Majorana branch at Gamma.
--
-- DASHI CONTRIBUTION:
-- * symmetry-classification firewall;
-- * TRSB excludes a DIII witness even when BdG particle-hole symmetry holds;
-- * typed Majorana surface witness separating zero energy, self-conjugacy,
--   boundary localization, and dispersion.
--
-- OPEN:
-- * this file does not reproduce the transfer-matrix numerical spectrum;
-- * this file does not identify a measured surface signal with the modeled
--   Majorana branch.
------------------------------------------------------------------------

open import Data.Empty using (⊥)

import DASHI.Physics.CondensedMatter.SuperconductingTimeReversalGaugeObstructionExact as TR
import DASHI.Physics.CondensedMatter.YbSbTwoINTNonunitarySelectedExact as INT

record BdGSymmetryFacts : Set₁ where
  field
    ParticleHole TimeReversal Chiral : Set

open BdGSymmetryFacts public

record IsDIII (S : BdGSymmetryFacts) : Set where
  constructor dIII
  field
    particleHole : ParticleHole S
    timeReversal : TimeReversal S

record IsClassDCompatible (S : BdGSymmetryFacts) : Set where
  constructor classD
  field
    particleHole : ParticleHole S
    noTimeReversal : TimeReversal S → ⊥

trsbExcludesDIII :
  (S : BdGSymmetryFacts) →
  (TimeReversal S → ⊥) →
  IsDIII S →
  ⊥
trsbExcludesDIII S noTR d =
  noTR (IsDIII.timeReversal d)

phsAndTRSBIsClassDCompatible :
  (S : BdGSymmetryFacts) →
  ParticleHole S →
  (TimeReversal S → ⊥) →
  IsClassDCompatible S
phsAndTRSBIsClassDCompatible S phs noTR =
  classD phs noTR

SelectedINTTimeReversal : Set
SelectedINTTimeReversal =
  TR.TRGaugeEquivalent INT.intTRSystem INT.selectedINT

selectedINTNoTimeReversal :
  SelectedINTTimeReversal → ⊥
selectedINTNoTimeReversal =
  INT.selectedINTBreaksTRUpToGauge

record SelectedINTBdGSourcePackage : Set₁ where
  field
    ParticleHoleSymmetry : Set
    particleHoleWitness : ParticleHoleSymmetry

open SelectedINTBdGSourcePackage public

selectedINTBdGFacts :
  SelectedINTBdGSourcePackage →
  BdGSymmetryFacts
selectedINTBdGFacts P =
  record
    { ParticleHole = ParticleHoleSymmetry P
    ; TimeReversal = SelectedINTTimeReversal
    ; Chiral = ⊥
    }

selectedINTBdGNotDIII :
  (P : SelectedINTBdGSourcePackage) →
  IsDIII (selectedINTBdGFacts P) →
  ⊥
selectedINTBdGNotDIII P =
  trsbExcludesDIII
    (selectedINTBdGFacts P)
    selectedINTNoTimeReversal

selectedINTBdGClassDCompatible :
  (P : SelectedINTBdGSourcePackage) →
  IsClassDCompatible (selectedINTBdGFacts P)
selectedINTBdGClassDCompatible P =
  phsAndTRSBIsClassDCompatible
    (selectedINTBdGFacts P)
    (particleHoleWitness P)
    selectedINTNoTimeReversal

record MajoranaSurfaceWitness : Set₁ where
  field
    Mode : Set
    selectedMode : Mode

    ZeroEnergy : Set
    zeroEnergyWitness : ZeroEnergy

    ParticleHoleSelfConjugate : Set
    particleHoleSelfConjugateWitness :
      ParticleHoleSelfConjugate

    BoundaryLocalized : Set
    boundaryLocalizedWitness : BoundaryLocalized

    LinearlyDispersingNearGamma : Set
    linearlyDispersingNearGammaWitness :
      LinearlyDispersingNearGamma

record KatariaEffectiveModelSurfaceResult : Set₁ where
  field
    witness : MajoranaSurfaceWitness
