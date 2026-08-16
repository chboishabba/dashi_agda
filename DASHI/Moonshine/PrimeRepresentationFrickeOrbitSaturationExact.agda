module DASHI.Moonshine.PrimeRepresentationFrickeOrbitSaturationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7, pp. 1-8.
-- MR 417184; no DOI assigned.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230-239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Compose two independently constructed results:
--
-- * PrimeRepresentationFrickeCouplingExact reconstructs g(X0(p)) from the
--   SO(3) order-two/order-three character data plus p=dim(V_j).
-- * PrimeFrickeOrbitSaturationExact characterises finite Fricke genus-zero as
--   saturation of the fixed-point budget r_p = 2*g(X0(p))+2.
--
-- The resulting theorem is the exact finite reduction chain
--
--   SO(3) character spectrum
--      -> representation-derived X0 topological budget
--      -> arithmetic Fricke fixed-point saturation
--      -> genus zero / Ogg on the 19-prime odd control scan.
--
-- The class-number fixed-point count remains an independent arithmetic input;
-- this module does not pretend that finite subgroup representation data alone
-- predicts that arithmetic count.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeFrickeGenusControlExact as Fricke
import DASHI.Moonshine.PrimeFrickeOrbitSaturationExact as Saturation
import DASHI.Moonshine.PrimeRepresentationFrickeCouplingExact as Coupling

representationTopologicalBudget :
  Matrix.OddPrimeCandidateUnder72 → Nat
representationTopologicalBudget prime =
  2 * Coupling.representationX0Genus prime + 2

representationBudgetMatchesFrickeBudget :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  representationTopologicalBudget prime
  ≡ Saturation.topologicalBudget (Fricke.frickeRow prime)
representationBudgetMatchesFrickeBudget prime =
  cong (λ genus → 2 * genus + 2)
    (Coupling.representationX0GenusMatchesFricke prime)

representationOrbitSaturated :
  Matrix.OddPrimeCandidateUnder72 → Bool
representationOrbitSaturated prime =
  Saturation.natEqual
    (Fricke.frickeFixedPointCount (Fricke.frickeRow prime))
    (representationTopologicalBudget prime)

representationSaturationMatchesModularSaturation :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  representationOrbitSaturated prime
  ≡ Saturation.frickeOrbitSaturated prime
representationSaturationMatchesModularSaturation prime
  rewrite representationBudgetMatchesFrickeBudget prime = refl

representationSaturationMatchesCoupledDefectClosure :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  representationOrbitSaturated prime
  ≡ Coupling.representationArithmeticFrickeClosed prime
representationSaturationMatchesCoupledDefectClosure prime =
  trans
    (representationSaturationMatchesModularSaturation prime)
    (trans
      (Saturation.saturationMatchesGenusZero prime)
      (sym (Coupling.coupledClosureMatchesFrickeGenusZero prime)))

representationSaturationMatchesExternalOgg :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  representationOrbitSaturated prime
  ≡ Matrix.externalOggLabel prime
representationSaturationMatchesExternalOgg prime =
  trans
    (representationSaturationMatchesModularSaturation prime)
    (Saturation.saturationMatchesExternalOgg prime)

prime29RepresentationSaturated :
  representationOrbitSaturated Matrix.prime29 ≡ true
prime29RepresentationSaturated = refl

prime37RepresentationNotSaturated :
  representationOrbitSaturated Matrix.prime37 ≡ false
prime37RepresentationNotSaturated = refl

prime67RepresentationNotSaturated :
  representationOrbitSaturated Matrix.prime67 ≡ false
prime67RepresentationNotSaturated = refl

prime71RepresentationSaturated :
  representationOrbitSaturated Matrix.prime71 ≡ true
prime71RepresentationSaturated = refl

record PrimeRepresentationFrickeOrbitSaturationBoundary : Set where
  field
    representationDerivedBudgetConstructed : Bool
    representationDerivedBudgetConstructedIsTrue :
      representationDerivedBudgetConstructed ≡ true
    representationBudgetEqualsModularBudgetOnScan : Bool
    representationBudgetEqualsModularBudgetOnScanIsTrue :
      representationBudgetEqualsModularBudgetOnScan ≡ true
    representationSaturationMatchesOggOnScan : Bool
    representationSaturationMatchesOggOnScanIsTrue :
      representationSaturationMatchesOggOnScan ≡ true
    classNumberFixedPointsDerivedFromRepresentation : Bool
    classNumberFixedPointsDerivedFromRepresentationIsFalse :
      classNumberFixedPointsDerivedFromRepresentation ≡ false

canonicalPrimeRepresentationFrickeOrbitSaturationBoundary :
  PrimeRepresentationFrickeOrbitSaturationBoundary
canonicalPrimeRepresentationFrickeOrbitSaturationBoundary =
  record
    { representationDerivedBudgetConstructed = true
    ; representationDerivedBudgetConstructedIsTrue = refl
    ; representationBudgetEqualsModularBudgetOnScan = true
    ; representationBudgetEqualsModularBudgetOnScanIsTrue = refl
    ; representationSaturationMatchesOggOnScan = true
    ; representationSaturationMatchesOggOnScanIsTrue = refl
    ; classNumberFixedPointsDerivedFromRepresentation = false
    ; classNumberFixedPointsDerivedFromRepresentationIsFalse = refl
    }
