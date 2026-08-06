module DASHI.Physics.YangMills.BalabanClayDyadicPhysicalClusteringExponentExact where

------------------------------------------------------------------------
-- PRIMARY CONTEXT
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", in The Millennium Prize Problems,
-- Clay Mathematics Institute / American Mathematical Society, 2006.
-- No DOI is assigned to the problem description used here.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II", Communications in
-- Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- DASHI CONTRIBUTION
--
-- Close the exact unit conversion for a dyadic cutoff tower.  Starting with a
-- physical separation D, define
--
--   a_0=1,       a_(k+1)=a_k/2,
--   n_0=D,       n_(k+1)=2 n_k,
--   m_lat(k)=m_phys a_k.
--
-- Finite induction proves
--
--   a_k n_k = D,
--   m_lat(k)n_k = m_phys D
--
-- at every cutoff.  Hence a lattice estimate with rate m_lat(k) is already a
-- physical estimate with rate m_phys; no exponent is lost when the mesh is
-- refined.  The remaining physical theorem is the uniform positive lower
-- bound m_lat(k) >= a_k m_phys and the covariance/activity estimate carrying
-- that rate, not the conversion of units.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

half two : ℚ
half = + 1 / 2
two = + 2 / 1

dyadicSpacing : Nat → ℚ
dyadicSpacing zero = + 1 / 1
dyadicSpacing (suc cutoff) = dyadicSpacing cutoff * half

refinedLatticeSeparation : Nat → ℚ → ℚ
refinedLatticeSeparation zero physicalSeparation = physicalSeparation
refinedLatticeSeparation (suc cutoff) physicalSeparation =
  two * refinedLatticeSeparation cutoff physicalSeparation

dyadicSpacingTimesRefinedSeparation : ∀ cutoff physicalSeparation →
  dyadicSpacing cutoff * refinedLatticeSeparation cutoff physicalSeparation
  ≡ physicalSeparation
dyadicSpacingTimesRefinedSeparation zero physicalSeparation =
  ℚRing.solve-∀ physicalSeparation
dyadicSpacingTimesRefinedSeparation (suc cutoff) physicalSeparation =
  trans
    (ℚRing.solve-∀
      (dyadicSpacing cutoff)
      (refinedLatticeSeparation cutoff physicalSeparation))
    (dyadicSpacingTimesRefinedSeparation cutoff physicalSeparation)

latticeMass : Nat → ℚ → ℚ
latticeMass cutoff physicalMass =
  physicalMass * dyadicSpacing cutoff

latticeDecayExponent : Nat → ℚ → ℚ → ℚ
latticeDecayExponent cutoff physicalMass physicalSeparation =
  latticeMass cutoff physicalMass
  * refinedLatticeSeparation cutoff physicalSeparation

physicalDecayExponent : ℚ → ℚ → ℚ
physicalDecayExponent physicalMass physicalSeparation =
  physicalMass * physicalSeparation

latticeExponentIsPhysicalExponent :
  ∀ cutoff physicalMass physicalSeparation →
  latticeDecayExponent cutoff physicalMass physicalSeparation
  ≡ physicalDecayExponent physicalMass physicalSeparation
latticeExponentIsPhysicalExponent cutoff physicalMass physicalSeparation =
  trans
    (ℚRing.solve-∀
      physicalMass
      (dyadicSpacing cutoff)
      (refinedLatticeSeparation cutoff physicalSeparation))
    (cong
      (λ distance → physicalMass * distance)
      (dyadicSpacingTimesRefinedSeparation cutoff physicalSeparation))

record DyadicClusteringBound
    (Observable Bound : Set) : Set₁ where
  field
    covarianceAtCutoff : Nat → Observable → Observable → Bound
    envelope : ℚ → Bound
    BoundLessEqual : Bound → Bound → Set
    physicalMass : ℚ
    physicalSeparation : Observable → Observable → ℚ

    latticeClustering : ∀ cutoff left right →
      BoundLessEqual
        (covarianceAtCutoff cutoff left right)
        (envelope
          (latticeDecayExponent cutoff physicalMass
            (physicalSeparation left right)))

open DyadicClusteringBound public

latticeClusteringHasExactPhysicalExponent :
  ∀ {Observable Bound}
    (dataSet : DyadicClusteringBound Observable Bound)
    cutoff left right →
  BoundLessEqual dataSet
    (covarianceAtCutoff dataSet cutoff left right)
    (envelope dataSet
      (physicalDecayExponent
        (physicalMass dataSet)
        (physicalSeparation dataSet left right)))
latticeClusteringHasExactPhysicalExponent dataSet cutoff left right =
  subst
    (λ exponent →
      BoundLessEqual dataSet
        (covarianceAtCutoff dataSet cutoff left right)
        (envelope dataSet exponent))
    (latticeExponentIsPhysicalExponent cutoff
      (physicalMass dataSet)
      (physicalSeparation dataSet left right))
    (latticeClustering dataSet cutoff left right)

exactDyadicDistanceConversionLevel : ProofLevel
exactDyadicDistanceConversionLevel = machineChecked

exactDyadicPhysicalExponentLevel : ProofLevel
exactDyadicPhysicalExponentLevel = machineChecked

physicalUniformClusteringProducerLevel : ProofLevel
physicalUniformClusteringProducerLevel = conditional
