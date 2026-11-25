module DASHI.Physics.Foundations.Hopf369PhaseRetainingObserverCubeExact where

-- P0L: original H05 cube, literal periodic complex coefficient carrier.
-- Source-written, not kernel accepted. The whole-space Hopf -> periodic
-- analytic producer and physical radius/projector authority remain separate.
open import Agda.Primitive using (lzero)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)
import DASHI.Core.GovernedDiagramCore as G
import DASHI.Core.GovernedIndexedResidualCubeExact as Q
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as H
import DASHI.Physics.Plasma.MHDMagneticVectorPotentialHelicalObserverExact as V
import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio

module Spectral (F : C3.RealField lzero)
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
  (S : H.HelicalModeScalars F) where

  record Source : Set where
    constructor source
    field
      mode : Z3.FourierMode
      nonzero : Z3.NonZeroMode mode
      sign : H.HelicitySign
      coefficient : C3.Complex3 F
  open Source public

  -- Preserve the original coefficient, not just its projected norm.
  projected : Source → C3.Complex3 F
  projected a = H.helicalProjector E I S (sign a) (mode a) (coefficient a)

  eigenvalue : Source → C3.Carrier F
  eigenvalue a with sign a
  ... | H.plus = H.modeNorm S (mode a)
  ... | H.minus = C3.negate F (H.modeNorm S (mode a))

  -- n counts order above magnetic helicity. The zero coefficient is
  -- retained independently, not assigned a fictitious inverse-curl weight.
  data Datum (n : Nat) : Set where
    zeroDatum : C3.Complex3 F → Datum n
    modeDatum : Source → C3.Carrier F → Datum n

  seed : Source → Datum zero
  seed a = modeDatum a (C3.real (V.magneticHelicityMode E S (mode a) (projected a)))

  advance : ∀ {n} → Datum n → Datum (suc n)
  advance (zeroDatum b) = zeroDatum b
  advance (modeDatum a w) = modeDatum a (C3.multiply F (eigenvalue a) w)

  advance2 : ∀ {n} → Datum n → Datum (suc (suc n))
  advance2 a = advance (advance a)

  data CutDatum (n : Nat) : Set where
    retained : Datum n → CutDatum n
    omitted : Datum n → CutDatum n

  reopen : ∀ {n} → CutDatum n → Datum n
  reopen (retained a) = a
  reopen (omitted a) = a

  advanceCut : ∀ {n} → CutDatum n → CutDatum (suc n)
  advanceCut (retained a) = retained (advance a)
  advanceCut (omitted a) = omitted (advance a)

  advance2Cut : ∀ {n} → CutDatum n → CutDatum (suc (suc n))
  advance2Cut a = advanceCut (advanceCut a)

  module At (select : Z3.FourierMode → Bool) where

    split : ∀ {n} → Datum n → CutDatum n
    split (zeroDatum b) = retained (zeroDatum b)
    split (modeDatum a w) with select (mode a)
    ... | true = retained (modeDatum a w)
    ... | false = omitted (modeDatum a w)

    reopenSplit : ∀ {n} (a : Datum n) → reopen (split a) ≡ a
    reopenSplit (zeroDatum b) = refl
    reopenSplit (modeDatum a w) with select (mode a)
    ... | true = refl
    ... | false = refl

    splitAdvance : ∀ {n} (a : Datum n) →
      split (advance a) ≡ advanceCut (split a)
    splitAdvance (zeroDatum b) = refl
    splitAdvance (modeDatum a w) with select (mode a)
    ... | true = refl
    ... | false = refl

    splitAdvance2 : ∀ {n} (a : Datum n) →
      split (advance2 a) ≡ advance2Cut (split a)
    splitAdvance2 (zeroDatum b) = refl
    splitAdvance2 (modeDatum a w) with select (mode a)
    ... | true = refl
    ... | false = refl

    cube : Q.Cube
    cube = record
      { A = Datum 0 ; B = Datum 1 ; C = Datum 2 ; D = Datum 3
      ; E = CutDatum 0 ; F = CutDatum 1 ; H = CutDatum 2 ; I = CutDatum 3
      ; x00 = advance ; x10 = advance ; x01 = advanceCut ; x11 = advanceCut
      ; y00 = advance2 ; y10 = advance2 ; y01 = advance2Cut ; y11 = advance2Cut
      ; z00 = split ; z10 = split ; z01 = split ; z11 = split
      }

    faces : Q.Faces cube
    faces = record
      { Rxy0 = λ _ → ⊤ ; Rxz0 = λ _ → ⊤ ; Ryz0 = λ _ → ⊤
      ; Rxy1 = λ _ → ⊤ ; Rxz1 = λ _ → ⊤ ; Ryz1 = λ _ → ⊤
      }

    exactFaces : Q.ExactFaces cube faces
    exactFaces = record
      { pxy0 = G.commutingSquareWitness (λ _ → refl)
      ; pxz0 = G.commutingSquareWitness splitAdvance
      ; pyz0 = G.commutingSquareWitness splitAdvance2
      ; pxy1 = G.commutingSquareWitness (λ _ → refl)
      ; pxz1 = G.commutingSquareWitness splitAdvance
      ; pyz1 = G.commutingSquareWitness splitAdvance2
      }

    residualFaces : Q.ResidualFaces cube faces
    residualFaces = record
      { rxy0 = G.residualSquareWitness (λ _ → tt)
      ; rxz0 = G.residualSquareWitness (λ _ → tt)
      ; ryz0 = G.residualSquareWitness (λ _ → tt)
      ; rxy1 = G.residualSquareWitness (λ _ → tt)
      ; rxz1 = G.residualSquareWitness (λ _ → tt)
      ; ryz1 = G.residualSquareWitness (λ _ → tt)
      }

    allPaths : (a : Datum 0) → Q.xyz cube a ≡ Q.zyx cube a
    allPaths = Q.xyz-zyx exactFaces

  -- An arbitrary independent index (e.g. original Q.Index plus source,
  -- metric, frame, and resolution) supplies its own selector.
  indexed : (K : Set) → (K → Z3.FourierMode → Bool) → Q.IndexedCube K
  indexed K choose = record
    { cubeAt = λ k → At.cube (choose k)
    ; facesAt = λ k → At.faces (choose k)
    ; residualAt = λ k → At.residualFaces (choose k)
    }

-- Causal cube: actual original Bio.signal and Bio.restoreMemory.
-- Four projection faces commute, two chronology faces generally do not.
causalCube : Q.Cube
causalCube = record
  { A = Bio.BiologicalState ; B = Bio.BiologicalState
  ; C = Bio.BiologicalState ; D = Bio.BiologicalState
  ; E = Bio.FutureSufficientCode ; F = Bio.FutureSufficientCode
  ; H = Bio.FutureSufficientCode ; I = Bio.FutureSufficientCode
  ; x00 = Bio.step Bio.signal ; x10 = Bio.step Bio.signal
  ; x01 = Bio.coarseStep Bio.signal ; x11 = Bio.coarseStep Bio.signal
  ; y00 = Bio.step Bio.restoreMemory ; y10 = Bio.step Bio.restoreMemory
  ; y01 = Bio.coarseStep Bio.restoreMemory ; y11 = Bio.coarseStep Bio.restoreMemory
  ; z00 = Bio.project ; z10 = Bio.project ; z01 = Bio.project ; z11 = Bio.project
  }

data SignedChange : Set where
  negative unchanged positive : SignedChange

change : Bool → Bool → SignedChange
change false false = unchanged
change true true = unchanged
change false true = positive
change true false = negative

record OrderResidual (left right : Bool) : Set where
  constructor orderResidual
  field
    first second : Bool
    firstExact : first ≡ left
    secondExact : second ≡ right
    signed : SignedChange
    signedExact : signed ≡ change left right

makeResidual : (l r : Bool) → OrderResidual l r
makeResidual l r = orderResidual l r refl refl (change l r) refl

fineLeft fineRight : Bio.BiologicalState → Bool
fineLeft a = Bio.observe (Bio.step Bio.restoreMemory (Bio.step Bio.signal a))
fineRight a = Bio.observe (Bio.step Bio.signal (Bio.step Bio.restoreMemory a))

coarseLeft coarseRight : Bio.FutureSufficientCode → Bool
coarseLeft a = Bio.coarseObserve
  (Bio.coarseStep Bio.restoreMemory (Bio.coarseStep Bio.signal a))
coarseRight a = Bio.coarseObserve
  (Bio.coarseStep Bio.signal (Bio.coarseStep Bio.restoreMemory a))

causalFaces : Q.Faces causalCube
causalFaces = record
  { Rxy0 = λ a → OrderResidual (fineLeft a) (fineRight a)
  ; Rxy1 = λ a → OrderResidual (coarseLeft a) (coarseRight a)
  ; Rxz0 = λ _ → ⊤ ; Ryz0 = λ _ → ⊤
  ; Rxz1 = λ _ → ⊤ ; Ryz1 = λ _ → ⊤
  }

causalResidualFaces : Q.ResidualFaces causalCube causalFaces
causalResidualFaces = record
  { rxy0 = G.residualSquareWitness (λ a → makeResidual (fineLeft a) (fineRight a))
  ; rxy1 = G.residualSquareWitness (λ a → makeResidual (coarseLeft a) (coarseRight a))
  ; rxz0 = G.residualSquareWitness (λ _ → tt)
  ; ryz0 = G.residualSquareWitness (λ _ → tt)
  ; rxz1 = G.residualSquareWitness (λ _ → tt)
  ; ryz1 = G.residualSquareWitness (λ _ → tt)
  }

pxz0 : G.CommutingSquareWitness (Q.xz0 causalCube causalFaces)
pxz0 = G.commutingSquareWitness (Bio.projectionCommutes Bio.signal)

pyz0 : G.CommutingSquareWitness (Q.yz0 causalCube causalFaces)
pyz0 = G.commutingSquareWitness (Bio.projectionCommutes Bio.restoreMemory)

pxz1 : G.CommutingSquareWitness (Q.xz1 causalCube causalFaces)
pxz1 = G.commutingSquareWitness (Bio.projectionCommutes Bio.signal)

pyz1 : G.CommutingSquareWitness (Q.yz1 causalCube causalFaces)
pyz1 = G.commutingSquareWitness (Bio.projectionCommutes Bio.restoreMemory)

actualFineOrderDiffers : fineLeft Bio.withoutMemory ≡ fineRight Bio.withoutMemory → ⊥
actualFineOrderDiffers = Bio.false≢true

actualCoarseOrderDiffers :
  coarseLeft (Bio.project Bio.withoutMemory) ≡ coarseRight (Bio.project Bio.withoutMemory) → ⊥
actualCoarseOrderDiffers = Bio.false≢true

actualSignedOrderResidual : change (fineLeft Bio.withoutMemory)
  (fineRight Bio.withoutMemory) ≡ positive
actualSignedOrderResidual = refl

-- No universal ExactFaces witness can be manufactured for this causal cube.
notAllCausalFacesExact : Q.ExactFaces causalCube causalFaces → ⊥
notAllCausalFacesExact p = actualFineOrderDiffers
  (cong Bio.observe (G.commutes (Q.pxy0 p) Bio.withoutMemory))
