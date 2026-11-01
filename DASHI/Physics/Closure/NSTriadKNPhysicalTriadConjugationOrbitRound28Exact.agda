module DASHI.Physics.Closure.NSTriadKNPhysicalTriadConjugationOrbitRound28Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- The ordered triad involution
--
--   (k,p,q) |-> (-k,-p,-q)
--
-- is lifted from lattice incidence to the literal cutoff carrier and output
-- fibres.  The conjugate triad has a concrete representative in the opposite
-- output fibre, and its Plucker coordinates and squared interaction-plane area
-- are proved unchanged.  This supplies the combinatorial involution required
-- by the later nonlinear Fourier-reality proof without quotienting away
-- orientation or multiplicity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer using (ℤ; _+_; _-_; _*_; -_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNLuoLiteralGalerkinCarrierRound25Exact as Round25
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadPluckerInvariantRound27Exact as Plucker

module RingZ = NR IntRS.ring
open RingZ using (_⊕_; _⊗_; ⊝_; solve)

conjugateTriadInCutoff :
  ∀ {cutoff triad} →
  Physical.PhysicalTriadInCutoff cutoff triad →
  Physical.PhysicalTriadInCutoff cutoff
    (Symmetry.conjugateTriad triad)
conjugateTriadInCutoff {cutoff} {triad} bounded =
  Physical.triad-in-cutoff
    (Physical.carrierNegationClosed policy
      (Physical.p triad) (Physical.pBounded bounded))
    (Physical.carrierNegationClosed policy
      (Physical.q triad) (Physical.qBounded bounded))
    (Physical.carrierNegationClosed policy
      (Physical.k triad) (Physical.kBounded bounded))
  where
  policy = Physical.literalCutoffRealityPolicy cutoff

conjugateTriadEnumerationHit :
  ∀ {cutoff triad} →
  Physical.PhysicalTriadInCutoff cutoff triad →
  Physical.PhysicalTriadEnumerationHit cutoff
    (Symmetry.conjugateTriad triad)
conjugateTriadEnumerationHit bounded =
  Physical.physicalTriadEnumerationComplete
    (conjugateTriadInCutoff bounded)

record ConjugateOutputFiberWitness
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (triad : Physical.PhysicalTriadIncidence) : Set where
  constructor conjugate-output-fibre-witness
  field
    representative : Physical.PhysicalTriadIncidence
    representativeListed :
      representative Cube.∈
      Output.physicalOutputFiber cutoff (Z3.negateMode output)
    representativeP :
      Physical.p representative
      ≡ Z3.negateMode (Physical.p triad)
    representativeQ :
      Physical.q representative
      ≡ Z3.negateMode (Physical.q triad)
    representativeK :
      Physical.k representative
      ≡ Z3.negateMode output

open ConjugateOutputFiberWitness public

conjugateOutputFiberWitness :
  ∀ {cutoff output triad} →
  triad Cube.∈ Output.physicalOutputFiber cutoff output →
  ConjugateOutputFiberWitness cutoff output triad
conjugateOutputFiberWitness {cutoff} {output} {triad} member =
  conjugate-output-fibre-witness
    (Physical.representative hit)
    (Output.physicalOutputFiberComplete
      (Physical.representativeListed hit)
      outputMeaning)
    (Physical.sameP hit)
    (Physical.sameQ hit)
    outputMeaning
  where
  bounded : Physical.PhysicalTriadInCutoff cutoff triad
  bounded = Round25.physicalOutputFiberCutoffSound member

  hit :
    Physical.PhysicalTriadEnumerationHit cutoff
      (Symmetry.conjugateTriad triad)
  hit = conjugateTriadEnumerationHit bounded

  outputMeaning :
    Physical.k (Physical.representative hit)
    ≡ Z3.negateMode output
  outputMeaning =
    trans
      (Physical.sameK hit)
      (cong Z3.negateMode (Output.physicalOutputFiberSound member))

pluckerConjugateX : ∀ p q →
  Plucker.pluckerX (Z3.negateMode p) (Z3.negateMode q)
  ≡ Plucker.pluckerX p q
pluckerConjugateX
  (Z3.mode px py pz) (Z3.mode qx qy qz) =
  RingZ.solve 6
    (λ px py pz qx qy qz →
      ((⊝ py ⊗ ⊝ qz) ⊕ ⊝ (⊝ pz ⊗ ⊝ qy)
      , (py ⊗ qz) ⊕ ⊝ (pz ⊗ qy)))
    refl px py pz qx qy qz

pluckerConjugateY : ∀ p q →
  Plucker.pluckerY (Z3.negateMode p) (Z3.negateMode q)
  ≡ Plucker.pluckerY p q
pluckerConjugateY
  (Z3.mode px py pz) (Z3.mode qx qy qz) =
  RingZ.solve 6
    (λ px py pz qx qy qz →
      ((⊝ pz ⊗ ⊝ qx) ⊕ ⊝ (⊝ px ⊗ ⊝ qz)
      , (pz ⊗ qx) ⊕ ⊝ (px ⊗ qz)))
    refl px py pz qx qy qz

pluckerConjugateZ : ∀ p q →
  Plucker.pluckerZ (Z3.negateMode p) (Z3.negateMode q)
  ≡ Plucker.pluckerZ p q
pluckerConjugateZ
  (Z3.mode px py pz) (Z3.mode qx qy qz) =
  RingZ.solve 6
    (λ px py pz qx qy qz →
      ((⊝ px ⊗ ⊝ qy) ⊕ ⊝ (⊝ py ⊗ ⊝ qx)
      , (px ⊗ qy) ⊕ ⊝ (py ⊗ qx)))
    refl px py pz qx qy qz

pluckerConjugatePreservesSquaredArea : ∀ p q →
  Plucker.pluckerNormSquared
    (Z3.negateMode p) (Z3.negateMode q)
  ≡ Plucker.pluckerNormSquared p q
pluckerConjugatePreservesSquaredArea p q
  rewrite pluckerConjugateX p q
        | pluckerConjugateY p q
        | pluckerConjugateZ p q = refl

physicalTriadConjugationPreservesSquaredArea :
  (triad : Physical.PhysicalTriadIncidence) →
  Plucker.pluckerNormSquared
    (Physical.p (Symmetry.conjugateTriad triad))
    (Physical.q (Symmetry.conjugateTriad triad))
  ≡
  Plucker.pluckerNormSquared
    (Physical.p triad) (Physical.q triad)
physicalTriadConjugationPreservesSquaredArea triad =
  pluckerConjugatePreservesSquaredArea
    (Physical.p triad) (Physical.q triad)

physicalTriadConjugationOrbitClosed : Bool
physicalTriadConjugationOrbitClosed = true

conjugateOutputFibresConstructed : Bool
conjugateOutputFibresConstructed = true

conjugationPluckerInvariantClosed : Bool
conjugationPluckerInvariantClosed = true

fullNonlinearCoefficientEquivarianceClosed : Bool
fullNonlinearCoefficientEquivarianceClosed = false

physicalTriadConjugationOrbitClosedIsTrue :
  physicalTriadConjugationOrbitClosed ≡ true
physicalTriadConjugationOrbitClosedIsTrue = refl

fullNonlinearCoefficientEquivarianceClosedIsFalse :
  fullNonlinearCoefficientEquivarianceClosed ≡ false
fullNonlinearCoefficientEquivarianceClosedIsFalse = refl
