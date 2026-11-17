module DASHI.Physics.Motors.SmithFilsingerSpatialPortChainExact where

-- All-N finite spatial source/receiver conservation, in Agda.
-- Attribution: the physical Smith/Filsinger differential source/sink and
-- independent solar environment hypothesis is user-origin. This lemma is
-- classical network energy accounting, and uses the pre-existing DASHI
-- Nat polynomial solver and recovery-energy ordering.
--
-- A channel's signed port-work is encoded as two nonnegative directed
-- budgets, not as an unproved external natural-energy generator.
-- No original hardware netlist, Maxwell PDE, full light cone, or solar-work
-- observation is supplied by this theorem.

open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:=_; con)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

-- The upstream/downstream labels are actual directed inter-cell work
-- budgets at a common time window, NOT arbitrary phasor amplitudes.
record SpatialCell (incoming outgoing : Nat) : Set where
  constructor spatialCell
  field
    controlledDriver initialStored usefulLoad heatAndRadiation finalStored : Nat
    localWork :
      incoming + (controlledDriver + initialStored)
        ≡ outgoing + (usefulLoad + (heatAndRadiation + finalStored))

-- A real chain is a dependent composition: the outgoing work of the
-- preceding cell is definitionally the incoming work of the next one.
data SpatialChain : Nat → Nat → Set where
  empty : (boundary : Nat) → SpatialChain boundary boundary
  thenCell : ∀ {first shared last} →
    SpatialCell first shared → SpatialChain shared last →
    SpatialChain first last

sumDrive : ∀ {first last} → SpatialChain first last → Nat
sumDrive (empty _) = 0
sumDrive (thenCell c rest) =
  SpatialCell.controlledDriver c + sumDrive rest

sumInitialStorage : ∀ {first last} → SpatialChain first last → Nat
sumInitialStorage (empty _) = 0
sumInitialStorage (thenCell c rest) =
  SpatialCell.initialStored c + sumInitialStorage rest

sumUsefulLoad : ∀ {first last} → SpatialChain first last → Nat
sumUsefulLoad (empty _) = 0
sumUsefulLoad (thenCell c rest) =
  SpatialCell.usefulLoad c + sumUsefulLoad rest

sumDissipation : ∀ {first last} → SpatialChain first last → Nat
sumDissipation (empty _) = 0
sumDissipation (thenCell c rest) =
  SpatialCell.heatAndRadiation c + sumDissipation rest

sumFinalStorage : ∀ {first last} → SpatialChain first last → Nat
sumFinalStorage (empty _) = 0
sumFinalStorage (thenCell c rest) =
  SpatialCell.finalStored c + sumFinalStorage rest

-- General cancellation of one shared port, from two independently
-- established local conservation laws. All quantities are Nat.
assocToLeft : (a b c : Nat) → a + (b + c) ≡ (a + b) + c
assocToLeft a b c =
  solve 3
    (λ x y z → x :+ (y :+ z) := (x :+ y) :+ z)
    refl a b c

exchangeRemainder : (a b c : Nat) →
  (a + b) + c ≡ (a + c) + b
exchangeRemainder a b c =
  solve 3
    (λ x y z → (x :+ y) :+ z := (x :+ z) :+ y)
    refl a b c

finishRemainder : (a b c : Nat) →
  (a + b) + c ≡ a + (c + b)
finishRemainder a b c =
  solve 3
    (λ x y z → (x :+ y) :+ z := x :+ (z :+ y))
    refl a b c

spliceSharedWork :
  (first shared last inputOne outputOne inputTwo outputTwo : Nat) →
  first + inputOne ≡ shared + outputOne →
  shared + inputTwo ≡ last + outputTwo →
  first + (inputOne + inputTwo)
    ≡ last + (outputOne + outputTwo)
spliceSharedWork first shared last inputOne outputOne inputTwo outputTwo p q =
  trans (assocToLeft first inputOne inputTwo)
    (trans (cong (λ z → z + inputTwo) p)
      (trans (exchangeRemainder shared outputOne inputTwo)
        (trans (cong (λ z → z + outputOne) q)
          (finishRemainder last outputTwo outputOne))))

groupInputs : (driverOne startOne driverTwo startTwo : Nat) →
  (driverOne + driverTwo) + (startOne + startTwo)
    ≡ (driverOne + startOne) + (driverTwo + startTwo)
groupInputs a b c d =
  solve 4
    (λ a b c d →
      ((a :+ c) :+ (b :+ d)) := ((a :+ b) :+ (c :+ d)))
    refl a b c d

groupOutputs :
  (loadOne lossOne endOne loadTwo lossTwo endTwo : Nat) →
  (loadOne + (lossOne + endOne))
    + (loadTwo + (lossTwo + endTwo))
  ≡ (loadOne + loadTwo)
    + ((lossOne + lossTwo) + (endOne + endTwo))
groupOutputs a b c d e f =
  solve 6
    (λ a b c d e f →
      ((a :+ (b :+ c)) :+ (d :+ (e :+ f)))
        := ((a :+ d) :+ ((b :+ e) :+ (c :+ f))))
    refl a b c d e f

combineAdjacentWork :
  (first shared last driverOne storedOne loadOne lossOne endOne
   driverTwo storedTwo loadTwo lossTwo endTwo : Nat) →
  first + (driverOne + storedOne)
    ≡ shared + (loadOne + (lossOne + endOne)) →
  shared + (driverTwo + storedTwo)
    ≡ last + (loadTwo + (lossTwo + endTwo)) →
  first + ((driverOne + driverTwo) + (storedOne + storedTwo))
    ≡ last + ((loadOne + loadTwo)
      + ((lossOne + lossTwo) + (endOne + endTwo)))
combineAdjacentWork first shared last d1 i1 l1 q1 f1 d2 i2 l2 q2 f2 p q =
  trans
    (cong (λ z → first + z) (groupInputs d1 i1 d2 i2))
    (trans
      (spliceSharedWork first shared last
        (d1 + i1) (l1 + (q1 + f1))
        (d2 + i2) (l2 + (q2 + f2)) p q)
      (cong (λ z → last + z) (groupOutputs l1 q1 f1 l2 q2 f2)))

-- TRUE all-N theorem: no fixed grid size and no assumption about
-- relative phase or source geometry. Every inter-cell directed port
-- cancels, leaving only exterior boundaries, admitted sources, useful
-- load, dissipation/radiation and before/after stored energy.
spatialChainWorkBalance :
  ∀ {first last} (chain : SpatialChain first last) →
  first + (sumDrive chain + sumInitialStorage chain)
    ≡ last + (sumUsefulLoad chain
      + (sumDissipation chain + sumFinalStorage chain))
spatialChainWorkBalance (empty boundary) =
  solve 1
    (λ b →
       b :+ (con 0 :+ con 0)
         := b :+ (con 0 :+ (con 0 :+ con 0)))
    refl boundary
spatialChainWorkBalance {first} {last}
  (thenCell {shared = shared} cell rest) =
  combineAdjacentWork
    first shared last
    (SpatialCell.controlledDriver cell)
    (SpatialCell.initialStored cell)
    (SpatialCell.usefulLoad cell)
    (SpatialCell.heatAndRadiation cell)
    (SpatialCell.finalStored cell)
    (sumDrive rest)
    (sumInitialStorage rest)
    (sumUsefulLoad rest)
    (sumDissipation rest)
    (sumFinalStorage rest)
    (SpatialCell.localWork cell)
    (spatialChainWorkBalance rest)

-- The useful load cannot exceed all admitted driving and initial
-- stored work at the incoming boundary. This uses the SAME all-N chain
-- and the existing finite Nat order owner.
outputReorder : (outgoing load loss final : Nat) →
  outgoing + (load + (loss + final))
    ≡ load + (outgoing + (loss + final))
outputReorder a b c d =
  solve 4
    (λ a b c d →
      a :+ (b :+ (c :+ d))
        := b :+ (a :+ (c :+ d)))
    refl a b c d

spatialLoadBoundedByAdmittedInputs :
  ∀ {first last} (chain : SpatialChain first last) →
  Bound._≤_ (sumUsefulLoad chain)
    (first + (sumDrive chain + sumInitialStorage chain))
spatialLoadBoundedByAdmittedInputs {last = last} chain =
  Bound.transportUpper (sym (spatialChainWorkBalance chain))
    (Bound.transportUpper
      (sym (outputReorder last (sumUsefulLoad chain)
        (sumDissipation chain) (sumFinalStorage chain)))
      (Bound.≤-append (sumUsefulLoad chain)
        (last + (sumDissipation chain + sumFinalStorage chain))))

onlyZeroCanBeBelowZero :
  ∀ {n : Nat} → Bound._≤_ n zero → n ≡ zero
onlyZeroCanBeBelowZero Bound.z≤n = refl

-- Source-off negative control for ANY chain size; outgoing work,
-- useful work and losses cannot arise from zero initial storage and
-- zero controller/source inputs.
sourceFreeSpatialChainHasZeroLoad :
  ∀ {last} (chain : SpatialChain 0 last) →
  sumDrive chain ≡ 0 →
  sumInitialStorage chain ≡ 0 →
  sumUsefulLoad chain ≡ 0
sourceFreeSpatialChainHasZeroLoad chain noDriver noStorage
  rewrite noDriver | noStorage =
  onlyZeroCanBeBelowZero (spatialLoadBoundedByAdmittedInputs chain)

-- Nonvacuous two-cell constructor with a shared internal port of 8.
-- First cell: 10 + (1+2) = 8 + (2+(1+2)).
-- Second cell: 8 + (0+1) = 6 + (1+(1+1)).
exampleTwoCellChain : SpatialChain 10 6
exampleTwoCellChain =
  thenCell (spatialCell 1 2 2 1 2 refl)
    (thenCell (spatialCell 0 1 1 1 1 refl)
      (empty 6))

exampleTwoCellConserves :
  10 + (sumDrive exampleTwoCellChain + sumInitialStorage exampleTwoCellChain)
    ≡ 6 + (sumUsefulLoad exampleTwoCellChain
      + (sumDissipation exampleTwoCellChain + sumFinalStorage exampleTwoCellChain))
exampleTwoCellConserves = spatialChainWorkBalance exampleTwoCellChain

-- An original-world environmental-work claim cannot be obtained by
-- relabelling the 'first' boundary Nat as solar energy.
record PhysicalSpatialAccessAdmission
  {first last : Nat} (chain : SpatialChain first last) : Set₁ where
  field
    MeasuredSameOriginalCollectorAndReturnGeometry : Set
    CausalMaxwellSoilIonosphereFieldSolution : Set
    IndependentlyMeteredSourcePortWork : Set
    PlasmaIonAndMaterialEnergyAccounting : Set
    StorageReplenishmentOverFullCycle : Set
    geometry : MeasuredSameOriginalCollectorAndReturnGeometry
    fieldSolution : CausalMaxwellSoilIonosphereFieldSolution
    sourceWork : IndependentlyMeteredSourcePortWork
    materialWork : PlasmaIonAndMaterialEnergyAccounting
    restored : StorageReplenishmentOverFullCycle
