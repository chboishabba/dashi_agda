module DASHI.Physics.Motors.SmithFilsingerFiniteVolumeFaceIncidenceExact where

-- Arbitrary finite incidence mesh, not merely a one-dimensional chain.
-- Exact cell-to-cell face cancellation on a Nat work carrier.
-- An independent discrete Stokes / Maxwell space-time integration must
-- construct each LocalVolumeCell.localConservation from actual E,H,J
-- and constitutive/memory/ion work. No field, solar source or measured
-- current is inferred by this combinatorial theorem.
--
-- Source attribution: classical finite-volume conservation; Smith/Filsinger
-- source/sink harvesting is the user's independently proposed hypothesis.
-- Reuse canonical order/cancellation from DASHI instead of a new axiom.

open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:=_)

import DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact as Cycle
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

-- Internal fluxes are directed: all work is nonnegative and orientation
-- is represented by choosing incoming vs outgoing. Thus signed scalar
-- flux need not be misidentified with inherently nonnegative field work.
record LocalVolumeCell : Set where
  constructor localVolumeCell
  field
    exteriorIncoming internalIncoming driverWork initialStored : Nat
    exteriorOutgoing internalOutgoing usefulLoad dissipation finalStored : Nat
    localConservation :
      (exteriorIncoming + internalIncoming) + (driverWork + initialStored)
        ≡ (exteriorOutgoing + internalOutgoing)
          + (usefulLoad + (dissipation + finalStored))

-- Generic list sum and the exact finite distributivity theorem.
sumOf : ∀ {A : Set} → (A → Nat) → List A → Nat
sumOf f [] = zero
sumOf f (x ∷ xs) = f x + sumOf f xs

sumPairDistributes :
  ∀ {A : Set} (xs : List A) (f g : A → Nat) →
  sumOf (λ x → f x + g x) xs ≡ sumOf f xs + sumOf g xs
sumPairDistributes [] f g = refl
sumPairDistributes (x ∷ xs) f g =
  trans
    (cong (λ v → (f x + g x) + v)
      (sumPairDistributes xs f g))
    (solve 4
      (λ a b c d → (a :+ b) :+ (c :+ d)
        := (a :+ c) :+ (b :+ d))
      refl (f x) (g x) (sumOf f xs) (sumOf g xs))

inCell : LocalVolumeCell → Nat
inCell c =
  (LocalVolumeCell.exteriorIncoming c
     + LocalVolumeCell.internalIncoming c)
  + (LocalVolumeCell.driverWork c + LocalVolumeCell.initialStored c)

outCell : LocalVolumeCell → Nat
outCell c =
  (LocalVolumeCell.exteriorOutgoing c
    + LocalVolumeCell.internalOutgoing c)
  + (LocalVolumeCell.usefulLoad c
    + (LocalVolumeCell.dissipation c + LocalVolumeCell.finalStored c))

foldLocalConservation :
  (cells : List LocalVolumeCell) →
  sumOf inCell cells ≡ sumOf outCell cells
foldLocalConservation [] = refl
foldLocalConservation (c ∷ cs) =
  cong₂ _+_ (LocalVolumeCell.localConservation c)
    (foldLocalConservation cs)

totalExtIn totalIntIn totalDrive totalInitial : List LocalVolumeCell → Nat
totalExtIn = sumOf LocalVolumeCell.exteriorIncoming
totalIntIn = sumOf LocalVolumeCell.internalIncoming
totalDrive = sumOf LocalVolumeCell.driverWork
totalInitial = sumOf LocalVolumeCell.initialStored

totalExtOut totalIntOut totalLoad totalLoss totalFinal :
  List LocalVolumeCell → Nat
totalExtOut = sumOf LocalVolumeCell.exteriorOutgoing
totalIntOut = sumOf LocalVolumeCell.internalOutgoing
totalLoad = sumOf LocalVolumeCell.usefulLoad
totalLoss = sumOf LocalVolumeCell.dissipation
totalFinal = sumOf LocalVolumeCell.finalStored

inputSplit :
  (cs : List LocalVolumeCell) →
  sumOf inCell cs
    ≡ (totalExtIn cs + totalIntIn cs)
      + (totalDrive cs + totalInitial cs)
inputSplit cs =
  trans
    (sumPairDistributes cs
      (λ c → LocalVolumeCell.exteriorIncoming c
        + LocalVolumeCell.internalIncoming c)
      (λ c → LocalVolumeCell.driverWork c
        + LocalVolumeCell.initialStored c))
    (cong₂ _+_
      (sumPairDistributes cs
        LocalVolumeCell.exteriorIncoming
        LocalVolumeCell.internalIncoming)
      (sumPairDistributes cs
        LocalVolumeCell.driverWork
        LocalVolumeCell.initialStored))

outputSplit :
  (cs : List LocalVolumeCell) →
  sumOf outCell cs
    ≡ (totalExtOut cs + totalIntOut cs)
      + (totalLoad cs + (totalLoss cs + totalFinal cs))
outputSplit cs =
  trans
    (sumPairDistributes cs
      (λ c → LocalVolumeCell.exteriorOutgoing c
        + LocalVolumeCell.internalOutgoing c)
      (λ c → LocalVolumeCell.usefulLoad c
        + (LocalVolumeCell.dissipation c
        + LocalVolumeCell.finalStored c)))
    (cong₂ _+_
      (sumPairDistributes cs
        LocalVolumeCell.exteriorOutgoing
        LocalVolumeCell.internalOutgoing)
      (trans
        (sumPairDistributes cs
          LocalVolumeCell.usefulLoad
          (λ c → LocalVolumeCell.dissipation c
            + LocalVolumeCell.finalStored c))
        (cong (λ z → totalLoad cs + z)
          (sumPairDistributes cs
            LocalVolumeCell.dissipation
            LocalVolumeCell.finalStored))))

-- Derive aggregate energy equality from EACH independent cell work law.
-- There is no independently assumed global conservation equality.
allCellsConserve :
  (cs : List LocalVolumeCell) →
  (totalExtIn cs + totalIntIn cs)
    + (totalDrive cs + totalInitial cs)
    ≡ (totalExtOut cs + totalIntOut cs)
      + (totalLoad cs + (totalLoss cs + totalFinal cs))
allCellsConserve cs =
  trans (sym (inputSplit cs))
    (trans (foldLocalConservation cs) (outputSplit cs))

-- Every genuine mesh-internal face is counted precisely once as entering
-- one volume and precisely once as leaving another volume. The two
-- incidences must be checked against the SAME list of face-work receipts.
-- This is stronger than equating two arbitrary aggregate numbers without
-- an explicit shared-face owner.
record OrientedFaceMesh : Set where
  constructor orientedFaceMesh
  field
    cells : List LocalVolumeCell
    internalFaceWork : List Nat
    incomingFaceIncidence :
      totalIntIn cells ≡ sumOf (λ x → x) internalFaceWork
    outgoingFaceIncidence :
      totalIntOut cells ≡ sumOf (λ x → x) internalFaceWork

incomingReorder : (exterior shared driver stored : Nat) →
  (exterior + shared) + (driver + stored)
    ≡ shared + (exterior + (driver + stored))
incomingReorder e s d u =
  solve 4
    (λ e s d u → (e :+ s) :+ (d :+ u)
      := s :+ (e :+ (d :+ u)))
    refl e s d u

outgoingReorder :
  (exterior shared load loss stored : Nat) →
  (exterior + shared) + (load + (loss + stored))
    ≡ shared + (exterior + (load + (loss + stored)))
outgoingReorder e s l q u =
  solve 5
    (λ e s l q u → (e :+ s) :+ (l :+ (q :+ u))
      := s :+ (e :+ (l :+ (q :+ u))))
    refl e s l q u

-- F10 finite-volume graph theorem. Holds for ANY finite face-incidence
-- topology, including branches and cycles, not only a path/chain.
-- Internal faces cancel exactly; no radiative/heat/load term is dropped.
finiteVolumeExteriorEnergyBalance :
  (mesh : OrientedFaceMesh) →
  totalExtIn (OrientedFaceMesh.cells mesh)
    + (totalDrive (OrientedFaceMesh.cells mesh)
      + totalInitial (OrientedFaceMesh.cells mesh))
  ≡ totalExtOut (OrientedFaceMesh.cells mesh)
    + (totalLoad (OrientedFaceMesh.cells mesh)
      + (totalLoss (OrientedFaceMesh.cells mesh)
      + totalFinal (OrientedFaceMesh.cells mesh)))
finiteVolumeExteriorEnergyBalance mesh =
  Cycle.+-cancelLeft shared lhs rhs
    (trans (sym (incomingReorder ei shared d u))
      (trans
        (cong (λ v → (ei + v) + (d + u))
          (sym (OrientedFaceMesh.incomingFaceIncidence mesh)))
        (trans
          (allCellsConserve cs)
          (trans
            (cong (λ v → (eo + v) + (l + (q + z)))
              (OrientedFaceMesh.outgoingFaceIncidence mesh))
            (outgoingReorder eo shared l q z)))))
  where
    cs : List LocalVolumeCell
    cs = OrientedFaceMesh.cells mesh
    shared : Nat
    shared = sumOf (λ x → x) (OrientedFaceMesh.internalFaceWork mesh)
    ei eo d u l q z : Nat
    ei = totalExtIn cs
    eo = totalExtOut cs
    d = totalDrive cs
    u = totalInitial cs
    l = totalLoad cs
    q = totalLoss cs
    z = totalFinal cs
    lhs : Nat
    lhs = ei + (d + u)
    rhs : Nat
    rhs = eo + (l + (q + z))

-- Use the existing Nat-work order, not a new physics law.
finiteVolumeUsefulBelowAllSuppliedWork :
  (mesh : OrientedFaceMesh) →
  Bound._≤_ (totalLoad (OrientedFaceMesh.cells mesh))
    (totalExtIn (OrientedFaceMesh.cells mesh)
      + (totalDrive (OrientedFaceMesh.cells mesh)
        + totalInitial (OrientedFaceMesh.cells mesh)))
finiteVolumeUsefulBelowAllSuppliedWork mesh =
  Bound.transportUpper (sym (finiteVolumeExteriorEnergyBalance mesh))
    (Bound.transportUpper (sym
      (solve 4
        (λ e l q z →
          e :+ (l :+ (q :+ z))
            := l :+ (e :+ (q :+ z)))
        refl (totalExtOut cs) (totalLoad cs)
          (totalLoss cs) (totalFinal cs)))
      (Bound.≤-append (totalLoad cs)
        (totalExtOut cs + (totalLoss cs + totalFinal cs))))
  where
    cs : List LocalVolumeCell
    cs = OrientedFaceMesh.cells mesh

-- A 2-cell physically oriented face matching example. The incoming
-- internal face work of B and outgoing internal face work of A are 3.
-- Each cell can have independent drive, storage, load and dissipation.
exampleFaceMesh : OrientedFaceMesh
exampleFaceMesh =
  orientedFaceMesh
    ((localVolumeCell 8 0 0 0 3 3 1 1 0 refl)
      ∷ (localVolumeCell 0 3 0 0 0 0 2 1 0 refl) ∷ [])
    (3 ∷ [])
    refl refl

exampleFaceMeshBalances :
  totalExtIn (OrientedFaceMesh.cells exampleFaceMesh)
    + (totalDrive (OrientedFaceMesh.cells exampleFaceMesh)
      + totalInitial (OrientedFaceMesh.cells exampleFaceMesh))
  ≡ totalExtOut (OrientedFaceMesh.cells exampleFaceMesh)
    + (totalLoad (OrientedFaceMesh.cells exampleFaceMesh)
      + (totalLoss (OrientedFaceMesh.cells exampleFaceMesh)
      + totalFinal (OrientedFaceMesh.cells exampleFaceMesh)))
exampleFaceMeshBalances = finiteVolumeExteriorEnergyBalance exampleFaceMesh

-- The true continuous Maxwell/finite-volume connection is still OPEN:
-- physical metric, face orientation and integration; selected E×H
-- trace and surface power; temporal quadrature; material ADE/ion work;
-- boundary source calibration; and actual port voltage/current.
