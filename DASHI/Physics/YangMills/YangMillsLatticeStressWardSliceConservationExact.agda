module DASHI.Physics.YangMills.YangMillsLatticeStressWardSliceConservationExact where

------------------------------------------------------------------------
-- ROUND83: DISCRETE STRESS WARD IDENTITY -> EXACT SLICE-CHARGE CONSERVATION
--
-- PRIMARY SOURCE / DIRECT LATTICE PRECEDENT
--
-- Sergio Caracciolo, Giuseppe Curci, Pietro Menotti and Andrea Pelissetto,
-- "The Energy-Momentum Tensor for Lattice Gauge Theories",
-- Annals of Physics 197 (1990), 119--153.
-- DOI: 10.1016/0003-4916(90)90203-Z.
--
-- The paper constructs the lattice energy-momentum tensor by imposing the Ward
-- identities associated with its conservation, perturbatively and
-- nonperturbatively.  That is the right direction for the Clay route: the local
-- operator must earn the translation-generator interpretation from its Ward
-- identity rather than being named T_{mu nu} by analogy.
--
-- DASHI CONTRIBUTION
--
-- Prove the finite periodic-lattice algebra that is normally left implicit.
-- A forward divergence telescopes exactly.  Therefore all three spatial
-- divergence sums vanish on a periodic slice.  If the local stress Ward identity
-- says
--
--       Delta Q_0 + sum_i div_i T_{i0} = 0,
--
-- then the slice energy charge has exactly zero temporal increment.
--
-- This is not yet the continuum theorem `integral T00 = H_OS`: renormalized
-- stress construction, continuum passage, and identification with the SAME OS
-- translation generator remain physical.  But no extra analytic lemma is needed
-- merely to pass from the lattice Ward identity to finite-volume charge
-- conservation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

forwardDifference : (Nat → ℚ) → Nat → ℚ
forwardDifference flux n = flux (suc n) - flux n

differencePartial : (Nat → ℚ) → Nat → ℚ
differencePartial flux zero = 0ℚ
differencePartial flux (suc n) =
  differencePartial flux n + forwardDifference flux n

differencePartialTelescopes :
  (flux : Nat → ℚ) → ∀ count →
  differencePartial flux count ≡ flux count - flux zero
differencePartialTelescopes flux zero =
  ℚRing.solve-∀ (flux zero)
differencePartialTelescopes flux (suc count)
  rewrite differencePartialTelescopes flux count =
  ℚRing.solve-∀ (flux zero) (flux count) (flux (suc count))

periodicDifferencePartialZero :
  (flux : Nat → ℚ) → ∀ count →
  flux count ≡ flux zero →
  differencePartial flux count ≡ 0ℚ
periodicDifferencePartialZero flux count closes
  rewrite differencePartialTelescopes flux count
  | closes =
  ℚRing.solve-∀ (flux zero)

record PeriodicSpatialFlux : Set₁ where
  field
    fluxX fluxY fluxZ : Nat → ℚ
    extentX extentY extentZ : Nat

    periodicX : fluxX extentX ≡ fluxX zero
    periodicY : fluxY extentY ≡ fluxY zero
    periodicZ : fluxZ extentZ ≡ fluxZ zero

open PeriodicSpatialFlux public

spatialDivergencePartial : PeriodicSpatialFlux → ℚ
spatialDivergencePartial dataSet =
  differencePartial (fluxX dataSet) (extentX dataSet)
  + differencePartial (fluxY dataSet) (extentY dataSet)
  + differencePartial (fluxZ dataSet) (extentZ dataSet)

spatialPeriodicDivergenceCancels :
  (dataSet : PeriodicSpatialFlux) →
  spatialDivergencePartial dataSet ≡ 0ℚ
spatialPeriodicDivergenceCancels dataSet
  rewrite periodicDifferencePartialZero
    (fluxX dataSet) (extentX dataSet) (periodicX dataSet)
  | periodicDifferencePartialZero
    (fluxY dataSet) (extentY dataSet) (periodicY dataSet)
  | periodicDifferencePartialZero
    (fluxZ dataSet) (extentZ dataSet) (periodicZ dataSet) =
  ℚRing.solve []

record LatticeStressWardSlice : Set₁ where
  field
    spatialFlux : PeriodicSpatialFlux
    temporalChargeDifference : ℚ

    -- Finite-volume integrated form of the local nu=0 Ward identity.
    discreteWardBalance :
      temporalChargeDifference + spatialDivergencePartial spatialFlux ≡ 0ℚ

open LatticeStressWardSlice public

temporalChargeDifferenceZero :
  (dataSet : LatticeStressWardSlice) →
  temporalChargeDifference dataSet ≡ 0ℚ
temporalChargeDifferenceZero dataSet =
  let
    normalized : temporalChargeDifference dataSet + 0ℚ ≡ 0ℚ
    normalized = subst
      (λ divergence → temporalChargeDifference dataSet + divergence ≡ 0ℚ)
      (spatialPeriodicDivergenceCancels (spatialFlux dataSet))
      (discreteWardBalance dataSet)
  in
  trans
    (sym (ℚP.+-identityʳ (temporalChargeDifference dataSet)))
    normalized

record LatticeStressWardCharge : Set₁ where
  field
    wardSlice : LatticeStressWardSlice
    chargeBefore chargeAfter : ℚ
    temporalDifferenceIsChargeDifference :
      temporalChargeDifference wardSlice ≡ chargeAfter - chargeBefore

open LatticeStressWardCharge public

sliceChargeDifferenceZero :
  (dataSet : LatticeStressWardCharge) →
  chargeAfter dataSet - chargeBefore dataSet ≡ 0ℚ
sliceChargeDifferenceZero dataSet =
  trans
    (sym (temporalDifferenceIsChargeDifference dataSet))
    (temporalChargeDifferenceZero (wardSlice dataSet))

periodicStressWardSliceConservationLevel : ProofLevel
periodicStressWardSliceConservationLevel = machineChecked

caraccioloCurciMenottiPelissettoLatticeStressWardLevel : ProofLevel
caraccioloCurciMenottiPelissettoLatticeStressWardLevel = standardImported

-- Physical remainder: construct/renormalize the SAME Yang--Mills stress tensor,
-- pass its Ward identity through the continuum limit, and identify the conserved
-- charge with the OS translation generator.  The finite periodic telescoping
-- above is no longer part of that hard remainder.
physicalContinuumStressWardOSGeneratorIdentificationLevel : ProofLevel
physicalContinuumStressWardOSGeneratorIdentificationLevel = conditional
