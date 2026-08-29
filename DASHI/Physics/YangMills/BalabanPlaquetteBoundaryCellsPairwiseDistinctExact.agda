module DASHI.Physics.YangMills.BalabanPlaquetteBoundaryCellsPairwiseDistinctExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Prove that the four positive bond cells on every literal side-four Wilson
-- plaquette are pairwise distinct.  The only pairs sharing an axis are
--
--   (mu,x)        versus (mu,x+nu),
--   (nu,x+mu)     versus (nu,x),
--
-- and a one-step translation on the side-four cyclic carrier has no fixed
-- point.  This finite geometric fact is the missing hypothesis allowing the
-- Boolean subset projector to decompose into four disjoint slot projectors and
-- hence forcing all Mobius degrees above one to vanish.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Empty; Product; pair; CyclicIndex; four; zeroᵢ; sucᵢ)
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge4
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33LiteralBondCellIncidenceExact as Cell

------------------------------------------------------------------------
-- One side-four step has no fixed point.
------------------------------------------------------------------------

next4NotFixed : ∀ index → Hodge4.next4 index ≡ index → Empty
next4NotFixed zeroᵢ ()
next4NotFixed (sucᵢ zeroᵢ) ()
next4NotFixed (sucᵢ (sucᵢ zeroᵢ)) ()
next4NotFixed (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) ()

site0 : Hodge4.Site4 → Hodge4.Index4
site0 (pair (pair x0 x1) (pair x2 x3)) = x0

site1 : Hodge4.Site4 → Hodge4.Index4
site1 (pair (pair x0 x1) (pair x2 x3)) = x1

site2 : Hodge4.Site4 → Hodge4.Index4
site2 (pair (pair x0 x1) (pair x2 x3)) = x2

site3 : Hodge4.Site4 → Hodge4.Index4
site3 (pair (pair x0 x1) (pair x2 x3)) = x3

shiftForwardNotFixed : ∀ axis site →
  Hodge4.shiftForward axis site ≡ site → Empty
shiftForwardNotFixed zeroᵢ site equality =
  next4NotFixed (site0 site) (cong site0 equality)
shiftForwardNotFixed (sucᵢ zeroᵢ) site equality =
  next4NotFixed (site1 site) (cong site1 equality)
shiftForwardNotFixed (sucᵢ (sucᵢ zeroᵢ)) site equality =
  next4NotFixed (site2 site) (cong site2 equality)
shiftForwardNotFixed (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site equality =
  next4NotFixed (site3 site) (cong site3 equality)

------------------------------------------------------------------------
-- Projections out of the bond-cell product.
------------------------------------------------------------------------

cellAxis : Cell.BondCell4 → Hodge4.Axis4
cellAxis (pair axis site) = axis

cellSite : Cell.BondCell4 → Hodge4.Site4
cellSite (pair axis site) = site

axisPairDistinct : ∀ axes →
  Plaquette.pairLeft axes ≡ Plaquette.pairRight axes → Empty
axisPairDistinct Plaquette.pair01 ()
axisPairDistinct Plaquette.pair02 ()
axisPairDistinct Plaquette.pair03 ()
axisPairDistinct Plaquette.pair12 ()
axisPairDistinct Plaquette.pair13 ()
axisPairDistinct Plaquette.pair23 ()

------------------------------------------------------------------------
-- Six pairwise non-collision theorems.
------------------------------------------------------------------------

boundaryCell0Not1 : ∀ plaquette →
  Boundary.boundaryCell0 plaquette ≡ Boundary.boundaryCell1 plaquette → Empty
boundaryCell0Not1 (pair site axes) equality =
  axisPairDistinct axes (cong cellAxis equality)

boundaryCell0Not2 : ∀ plaquette →
  Boundary.boundaryCell0 plaquette ≡ Boundary.boundaryCell2 plaquette → Empty
boundaryCell0Not2 (pair site axes) equality =
  shiftForwardNotFixed (Plaquette.pairRight axes) site
    (cong cellSite equality)

boundaryCell0Not3 : ∀ plaquette →
  Boundary.boundaryCell0 plaquette ≡ Boundary.boundaryCell3 plaquette → Empty
boundaryCell0Not3 (pair site axes) equality =
  axisPairDistinct axes (cong cellAxis equality)

boundaryCell1Not2 : ∀ plaquette →
  Boundary.boundaryCell1 plaquette ≡ Boundary.boundaryCell2 plaquette → Empty
boundaryCell1Not2 (pair site axes) equality =
  axisPairDistinct axes (cong cellAxis equality)

boundaryCell1Not3 : ∀ plaquette →
  Boundary.boundaryCell1 plaquette ≡ Boundary.boundaryCell3 plaquette → Empty
boundaryCell1Not3 (pair site axes) equality =
  shiftForwardNotFixed (Plaquette.pairLeft axes) site
    (cong cellSite equality)

boundaryCell2Not3 : ∀ plaquette →
  Boundary.boundaryCell2 plaquette ≡ Boundary.boundaryCell3 plaquette → Empty
boundaryCell2Not3 (pair site axes) equality =
  axisPairDistinct axes (cong cellAxis equality)

plaquetteBoundaryCellsPairwiseDistinctLevel : ProofLevel
plaquetteBoundaryCellsPairwiseDistinctLevel = machineChecked
