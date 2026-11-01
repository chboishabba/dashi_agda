module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoMagneticCellIdentificationExact where

------------------------------------------------------------------------
-- DATA -> CRYSTAL -> MAGNETIC ORDER (source scoped)
--
-- H. Cein Mandujano et al., Phys Rev B 110, 144420 (2024).
-- DOI 10.1103/PhysRevB.110.144420
--   Chemical SG P63/mmc #194, a=6.8828(1) Angstrom,
--   c=12.4535(3) Angstrom, Co Wyckoff 2a, full cell Z=8.
--   Neutron propagation k=(0,0,0); magnetic SG
--   P6_3'/m'm'c (BNS #194.268), staggered c-axis Co moments;
--   1.08(11) mu_B per Co at 120 K, 1.35(11) at 10 K.
--   Magnetic Bragg indices (101), (111).
--
-- M. Sprague et al., Nat Commun (2026).
-- DOI 10.1038/s41467-026-76784-x
--   In-plane 2x2 structure, 7 K spin-resolved + ordinary ARPES
--   and DFT; nodal kz=0 and pi/c, off-nodal kz ~ pi/(2c).
--
-- This module gives an EXACT TWO-SITE INSTANCE of a mirror that
-- exchanges the two Co 2a layer representatives (z=0,z=1/2,
-- in fractional units).  It is NOT a full P63/mmc / MSG
-- 194.268 representation, which requires nonsymmorphic translations,
-- a reciprocal lattice, and Bloch-phase compatibility.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

record SourceRole : Set where
  constructor sourceRole
  field
    doi : String
    subject : String
    role : String
    exclusion : String

neutronSource : SourceRole
neutronSource = sourceRole
  "10.1103/PhysRevB.110.144420"
  "Co1/4TaSe2 XRD and neutron diffraction"
  "P63/mmc #194; magnetic P6_3'/m'm'c #194.268; k=(0,0,0); axial A-type AFM"
  "Does not directly measure momentum-resolved spin band structure"

arpesSource : SourceRole
arpesSource = sourceRole
  "10.1038/s41467-026-76784-x"
  "Co1/4TaSe2 ARPES and DFT"
  "Momentum-selective g-wave splitting, nodal planes and temperature evolution"
  "Does not by itself determine unique tight-binding parameters or moire coupling"

data Co2a : Set where
  fractionalZ0 fractionalZHalf : Co2a

-- On just the two sites, reflection in the z=1/4 plane exchanges
-- representatives, agreeing with the paper's opposite-sublattice
-- mirror statement.  Exact fractional coordinate proof requires
-- the genuine crystallographic-coordinate carrier.
mirrorAcrossQuarter : Co2a → Co2a
mirrorAcrossQuarter fractionalZ0 = fractionalZHalf
mirrorAcrossQuarter fractionalZHalf = fractionalZ0

mirrorAcrossQuarterSquared : (x : Co2a) →
  mirrorAcrossQuarter (mirrorAcrossQuarter x) ≡ x
mirrorAcrossQuarterSquared fractionalZ0 = refl
mirrorAcrossQuarterSquared fractionalZHalf = refl

data AxialMoment : Set where
  positiveC negativeC : AxialMoment

oppositeMoment : AxialMoment → AxialMoment
oppositeMoment positiveC = negativeC
oppositeMoment negativeC = positiveC

oppositeMomentSquared : (m : AxialMoment) →
  oppositeMoment (oppositeMoment m) ≡ m
oppositeMomentSquared positiveC = refl
oppositeMomentSquared negativeC = refl

orderedCoMoment : Co2a → AxialMoment
orderedCoMoment fractionalZ0 = positiveC
orderedCoMoment fractionalZHalf = negativeC

-- For the actual two-layer magnetic assignment this is computation,
-- rather than an unexplained new postulate.
oppositeLayerOrdering : (site : Co2a) →
  orderedCoMoment (mirrorAcrossQuarter site)
    ≡ oppositeMoment (orderedCoMoment site)
oppositeLayerOrdering fractionalZ0 = refl
oppositeLayerOrdering fractionalZHalf = refl

-- Pair cancellation is at the level of signed moment *directions*
-- and equal multiplicities; it does not overrule the observed weak
-- in-plane ferromagnetic component or determine the neutron moment.
data MagneticPair : Set where
  pairedCoLayers : MagneticPair

pairPositiveMultiplicity : MagneticPair → Nat
pairPositiveMultiplicity pairedCoLayers = suc zero

pairNegativeMultiplicity : MagneticPair → Nat
pairNegativeMultiplicity pairedCoLayers = suc zero

pairCompensation : (p : MagneticPair) →
  pairPositiveMultiplicity p ≡ pairNegativeMultiplicity p
pairCompensation pairedCoLayers = refl
