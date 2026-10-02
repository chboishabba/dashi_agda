module DASHI.Physics.CondensedMatter.YbSbTwoBdGParticleHoleAdapterExact where

------------------------------------------------------------------------
-- ATTRIBUTION
--
-- SOURCE / MODEL INPUT:
-- a concrete YbSb2 effective model must provide h(k), pairing blocks,
-- momentum inversion and the transpose/conjugation identities.
--
-- DASHI DERIVATION:
-- those identities imply the canonical Nambu particle-hole relation, which
-- then discharges the PHS field used by the selected-INT symmetry classifier.
--
-- OPEN:
-- no concrete source numerical matrix is identified here.
------------------------------------------------------------------------

import DASHI.Physics.CondensedMatter.BdGNambuParticleHoleExact as Nambu
import DASHI.Physics.CondensedMatter.YbSbTwoBdGSymmetryBoundaryExact as Boundary

record YbSbTwoBdGAlgebraicModel : Set₁ where
  field
    carrier : Nambu.AdditiveCarrier
    alg : Nambu.BdGAlgebra carrier
    model : Nambu.BdGModel carrier alg

open YbSbTwoBdGAlgebraicModel public

ParticleHoleSymmetry :
  YbSbTwoBdGAlgebraicModel →
  Set
ParticleHoleSymmetry M =
  (k : Nambu.K (model M)) →
  Nambu.particleHoleBlock
    (carrier M)
    (alg M)
    (Nambu.canonicalBdG (model M) k)
  ≡
  Nambu.negateBlock
    (carrier M)
    (Nambu.canonicalBdG
      (model M)
      (Nambu.negK (model M) k))

particleHoleSymmetry :
  (M : YbSbTwoBdGAlgebraicModel) →
  ParticleHoleSymmetry M
particleHoleSymmetry M =
  Nambu.canonicalBdGParticleHole (model M)

toSelectedINTBdGSourcePackage :
  (M : YbSbTwoBdGAlgebraicModel) →
  Boundary.SelectedINTBdGSourcePackage
toSelectedINTBdGSourcePackage M =
  record
    { ParticleHoleSymmetry = ParticleHoleSymmetry M
    ; particleHoleWitness = particleHoleSymmetry M
    }

algebraicModelSelectedINTNotDIII :
  (M : YbSbTwoBdGAlgebraicModel) →
  Boundary.IsDIII
    (Boundary.selectedINTBdGFacts
      (toSelectedINTBdGSourcePackage M))
  →
  Data.Empty.⊥
algebraicModelSelectedINTNotDIII M =
  Boundary.selectedINTBdGNotDIII
    (toSelectedINTBdGSourcePackage M)

algebraicModelSelectedINTClassDCompatible :
  (M : YbSbTwoBdGAlgebraicModel) →
  Boundary.IsClassDCompatible
    (Boundary.selectedINTBdGFacts
      (toSelectedINTBdGSourcePackage M))
algebraicModelSelectedINTClassDCompatible M =
  Boundary.selectedINTBdGClassDCompatible
    (toSelectedINTBdGSourcePackage M)
