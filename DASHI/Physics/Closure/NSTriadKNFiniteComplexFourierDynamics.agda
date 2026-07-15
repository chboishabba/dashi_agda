module DASHI.Physics.Closure.NSTriadKNFiniteComplexFourierDynamics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (ℤ)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Relation.Nullary.Decidable using (yes; no)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Algebra
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffModeSupport as Support
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Sector
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy
import DASHI.Physics.Closure.NSTriadKNFiniteTriadCancellationAlgebra as Cancel

open Energy using (ModalTriadTransfer; transferLeft; transferRight; transferOut; conservation)

------------------------------------------------------------------------
-- Finite complex Fourier dynamics, deliberately instantaneous.
--
-- This is not a time-analysis library.  `formalWeightedEnergyDerivative`
-- is the finite algebraic expression which a later differentiability theorem
-- must identify with d/dt E_z.  Separating the two prevents a finite ODE
-- convention from being mistaken for the required continuum argument.
------------------------------------------------------------------------

record FiniteComplexFourierAuthority
    (K : Algebra.ExactOrderedCommutativeRing) : Set₁ where
  field
    Complex : Set
    Vec3C : Set

    zeroComplex : Complex
    _+ᶜ_ : Complex → Complex → Complex
    _*ᶜ_ : Complex → Complex → Complex
    -ᶜ_ : Complex → Complex
    conjugate : Complex → Complex
    realPart : Complex → Scalar.Scalar (Algebra.orderedScalar K)
    complexI : Complex
    embedInteger : ℤ → Complex

    zeroVector : Vec3C
    _+ᵥ_ : Vec3C → Vec3C → Vec3C
    -ᵥ_ : Vec3C → Vec3C
    scaleComplex : Complex → Vec3C → Vec3C
    conjugateVector : Vec3C → Vec3C
    innerC : Vec3C → Vec3C → Complex
    normSq : Vec3C → Scalar.Scalar (Algebra.orderedScalar K)

    waveDot : Lattice.LatticeMode3 → Vec3C → Complex
    leray : Lattice.LatticeMode3 → Vec3C → Vec3C

    realPartAdd :
      (a b : Complex) → realPart (a +ᶜ b) ≡
      Scalar._+_ (Algebra.orderedScalar K) (realPart a) (realPart b)
    realPartNeg :
      (a : Complex) → realPart (-ᶜ a) ≡
      Scalar.neg (Algebra.orderedScalar K) (realPart a)
    realPartZero : realPart zeroComplex ≡ Scalar.zero (Algebra.orderedScalar K)
    innerAddRight :
      (x y z : Vec3C) → innerC x (y +ᵥ z) ≡
      innerC x y +ᶜ innerC x z
    innerConjugateSymmetry :
      (x y : Vec3C) → conjugate (innerC x y) ≡ innerC y x
    innerZeroRight :
      (x : Vec3C) → innerC x zeroVector ≡ zeroComplex
    normSqIsDiagonalInner :
      (x : Vec3C) → normSq x ≡ realPart (innerC x x)

    -- Atomic zero laws used to reduce the singleton self-input orbit.  They
    -- are ordinary complex/vector algebra, not a triad-conservation axiom.
    complexMulZeroRight :
      (a : Complex) → a *ᶜ zeroComplex ≡ zeroComplex
    negComplexZero : -ᶜ zeroComplex ≡ zeroComplex
    scaleComplexZeroScalar :
      (x : Vec3C) → scaleComplex zeroComplex x ≡ zeroVector

    leraySelfAdjoint :
      (k : Lattice.LatticeMode3) → (x y : Vec3C) →
      innerC x (leray k y) ≡ innerC (leray k x) y
    lerayFixesDivergenceFree :
      (k : Lattice.LatticeMode3) → (x : Vec3C) →
      waveDot k x ≡ zeroComplex → leray k x ≡ x
    lerayProducesDivergenceFree :
      (k : Lattice.LatticeMode3) → (x : Vec3C) →
      waveDot k (leray k x) ≡ zeroComplex

    -- The lattice wavevectors are real, so conjugation preserves the
    -- divergence constraint at a fixed Fourier label.
    conjugateVectorPreservesDivergenceFree :
      (k : Lattice.LatticeMode3) → (x : Vec3C) →
      waveDot k x ≡ zeroComplex →
      waveDot k (conjugateVector x) ≡ zeroComplex

    -- This transport is also useful for the legacy labelled-triad pairing.
    -- It is strictly stronger than what the actual modal-energy convention
    -- below needs.
    conjugateVectorDivergenceFreeAtNegatedMode :
      (k : Lattice.LatticeMode3) → (x : Vec3C) →
      waveDot k x ≡ zeroComplex →
      waveDot (Lattice.modeNeg k) (conjugateVector x) ≡ zeroComplex

open FiniteComplexFourierAuthority public

------------------------------------------------------------------------
-- Leray removal against a divergence-free energy test vector.
--
-- This is a concrete finite-dimensional identity.  It does not assert the
-- Navier--Stokes triad cancellation; it only exposes the simplification which
-- makes that later six-term calculation possible.
------------------------------------------------------------------------

lerayDropsAgainstDivergenceFreeOutput :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (k : Lattice.LatticeMode3) →
  (output v : Vec3C A) →
  waveDot A k (conjugateVector A output) ≡ zeroComplex A →
  realPart A
    (innerC A (conjugateVector A output) (leray A k v)) ≡
  realPart A (innerC A (conjugateVector A output) v)
lerayDropsAgainstDivergenceFreeOutput K A k output v outputDF =
  cong (realPart A)
    (trans
      (leraySelfAdjoint A k (conjugateVector A output) v)
      (cong (λ x → innerC A x v)
        (lerayFixesDivergenceFree A k (conjugateVector A output) outputDF)))

lerayDropsAgainstPhysicalOutput :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (k : Lattice.LatticeMode3) →
  (output v : Vec3C A) →
  waveDot A k output ≡ zeroComplex A →
  realPart A
    (innerC A (conjugateVector A output)
      (leray A (Lattice.modeNeg k) v)) ≡
  realPart A (innerC A (conjugateVector A output) v)
lerayDropsAgainstPhysicalOutput K A k output v outputDF =
  lerayDropsAgainstDivergenceFreeOutput K A (Lattice.modeNeg k) output v
    (conjugateVectorDivergenceFreeAtNegatedMode A k output outputDF)

------------------------------------------------------------------------
-- Concrete labelled modal transfers.
--
-- For `τ = (p , q , r)` with p + q + r = 0, its ordered interaction has
-- convolution output `-r` and is paired with `conjugate u_{-r}`.  This is
-- the actual modal-energy pairing for the Fourier equation at output `-r`.
-- Cycling τ gives the corresponding contributions labelled by p and q.
-- Input swaps are combined only off the diagonal, exactly as in the
-- cutoff-convolution reconstruction; p = q retains its singleton occurrence.
------------------------------------------------------------------------

orderedModalInteraction :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (Lattice.LatticeMode3 → Vec3C A) → Lattice.LatticeTriad → Vec3C A
orderedModalInteraction K A u τ =
  scaleComplex A
    (_*ᶜ_ A (complexI A) (waveDot A (Lattice.right τ) (u (Lattice.left τ))))
    (u (Lattice.right τ))

-- The complex summand before applying `- realPart`.  Keeping it explicit
-- makes the later six-occurrence normal form a literal finite expression,
-- rather than a postulated link from modal transfers to cancellation atoms.
orderedModalComplexTerm :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (Lattice.LatticeMode3 → Vec3C A) → Lattice.LatticeTriad → Complex A
orderedModalComplexTerm K A u τ =
  innerC A (conjugateVector A (u (Lattice.modeNeg (Lattice.out τ))))
    (orderedModalInteraction K A u τ)

-- The missing swapped occurrence of a diagonal input orbit carries the same
-- self-input factor.  Incompressibility makes that factor zero, so restoring
-- it for the six-term cancellation normal form does not alter the physical
-- cutoff contribution.
diagonalSelfInputInteractionVectorZero :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Lattice.left τ ≡ Lattice.right τ →
  waveDot A (Lattice.left τ) (u (Lattice.left τ)) ≡ zeroComplex A →
  orderedModalInteraction K A u τ ≡ zeroVector A
diagonalSelfInputInteractionVectorZero K A u τ refl divergence =
  trans
    (cong (λ d → scaleComplex A
      (_*ᶜ_ A (complexI A) d) (u (Lattice.right τ))) divergence)
    (trans
      (cong (λ c → scaleComplex A c (u (Lattice.right τ)))
        (complexMulZeroRight A (complexI A)))
      (scaleComplexZeroScalar A (u (Lattice.right τ))))

-- The instantaneous Fourier state is introduced before the modal-transfer
-- simplification lemmas because those lemmas use its concrete divergence-free
-- witness.  This is a dependency-ordering move only: the dynamics fields are
-- consumed later by the weighted-energy identity.
record FiniteFourierNSState
    (K : Algebra.ExactOrderedCommutativeRing)
    (A : FiniteComplexFourierAuthority K) (M : Nat) : Set₁ where
  field
    coefficient : Lattice.LatticeMode3 → Vec3C A
    velocityDot : Lattice.LatticeMode3 → Vec3C A

    outsideCutoffZero :
      (k : Lattice.LatticeMode3) →
      Sector.inExactCutoff? M k ≡ false → coefficient k ≡ zeroVector A
    reality :
      (k : Lattice.LatticeMode3) →
      coefficient (Lattice.modeNeg k) ≡ conjugateVector A (coefficient k)
    divergenceFree :
      (k : Lattice.LatticeMode3) →
      waveDot A k (coefficient k) ≡ zeroComplex A

    viscosity : Scalar.Scalar (Algebra.orderedScalar K)
    modeSquaredNorm : Lattice.LatticeMode3 → Scalar.Scalar (Algebra.orderedScalar K)
    viscousTerm : Lattice.LatticeMode3 → Vec3C A
    cutoffConvectionTerm : Lattice.LatticeMode3 → Vec3C A
    cutoffBoundaryTerm : Lattice.LatticeMode3 → Vec3C A

    dynamics :
      (k : Lattice.LatticeMode3) →
      velocityDot k ≡
      FiniteComplexFourierAuthority._+ᵥ_ A
        (cutoffConvectionTerm k)
        (FiniteComplexFourierAuthority._+ᵥ_ A
          (viscousTerm k) (cutoffBoundaryTerm k))

open FiniteFourierNSState public

orderedModalTransfer :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (Lattice.LatticeMode3 → Vec3C A) → Lattice.LatticeTriad →
  Scalar.Scalar (Algebra.orderedScalar K)
orderedModalTransfer K A u τ =
  Scalar.neg S
    (realPart A
      (innerC A (conjugateVector A (u (Lattice.modeNeg (Lattice.out τ))))
        (leray A (Lattice.modeNeg (Lattice.out τ))
          (orderedModalInteraction K A u τ))))
  where
  S = Algebra.orderedScalar K

orderedModalTransferNoLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (Lattice.LatticeMode3 → Vec3C A) → Lattice.LatticeTriad →
  Scalar.Scalar (Algebra.orderedScalar K)
orderedModalTransferNoLeray K A u τ =
  Scalar.neg (Algebra.orderedScalar K)
    (realPart A (orderedModalComplexTerm K A u τ))

orderedModalTransferWithoutLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  orderedModalTransfer K A (coefficient u) τ ≡
  orderedModalTransferNoLeray K A (coefficient u) τ
orderedModalTransferWithoutLeray K A M u τ =
  cong (Scalar.neg (Algebra.orderedScalar K))
    (lerayDropsAgainstDivergenceFreeOutput K A (Lattice.modeNeg (Lattice.out τ))
      (coefficient u (Lattice.modeNeg (Lattice.out τ)))
      (orderedModalInteraction K A (coefficient u) τ)
      (conjugateVectorPreservesDivergenceFree A
        (Lattice.modeNeg (Lattice.out τ))
        (coefficient u (Lattice.modeNeg (Lattice.out τ)))
        (divergenceFree u (Lattice.modeNeg (Lattice.out τ)))))

canonicalModalTransfer :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (Lattice.LatticeMode3 → Vec3C A) → Lattice.LatticeTriad →
  Scalar.Scalar (Algebra.orderedScalar K)
canonicalModalTransfer K A u τ
  with Support.latticeModeDecEq (Lattice.left τ) (Lattice.right τ)
... | yes _ = orderedModalTransfer K A u τ
... | no _ = Scalar._+_ S
  (orderedModalTransfer K A u τ)
  (orderedModalTransfer K A u (Lattice.triadSwap τ))
  where
  S = Algebra.orderedScalar K

canonicalModalTransferNoLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (Lattice.LatticeMode3 → Vec3C A) → Lattice.LatticeTriad →
  Scalar.Scalar (Algebra.orderedScalar K)
canonicalModalTransferNoLeray K A u τ
  with Support.latticeModeDecEq (Lattice.left τ) (Lattice.right τ)
... | yes _ = orderedModalTransferNoLeray K A u τ
... | no _ = Scalar._+_ S
  (orderedModalTransferNoLeray K A u τ)
  (orderedModalTransferNoLeray K A u (Lattice.triadSwap τ))
  where
  S = Algebra.orderedScalar K

-- A uniform two-occurrence form is used only for the cancellation normal
-- form.  On a diagonal input pair its extra swapped occurrence is exactly
-- zero by incompressibility, so this restores algebraic symmetry without
-- changing the physical singleton-orbit convention.
uniformModalTransferNoLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (Lattice.LatticeMode3 → Vec3C A) → Lattice.LatticeTriad →
  Scalar.Scalar (Algebra.orderedScalar K)
uniformModalTransferNoLeray K A u τ = Scalar._+_ S
  (orderedModalTransferNoLeray K A u τ)
  (orderedModalTransferNoLeray K A u (Lattice.triadSwap τ))
  where S = Algebra.orderedScalar K

swapPreservesDiagonalInputs :
  (τ : Lattice.LatticeTriad) →
  Lattice.left τ ≡ Lattice.right τ →
  Lattice.left (Lattice.triadSwap τ) ≡
  Lattice.right (Lattice.triadSwap τ)
swapPreservesDiagonalInputs (Lattice.mkLatticeTriad left right out) refl = refl

orderedModalTransferNoLerayZeroFromDiagonal :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  Lattice.left τ ≡ Lattice.right τ →
  orderedModalTransferNoLeray K A (coefficient u) τ ≡
  Scalar.zero (Algebra.orderedScalar K)
orderedModalTransferNoLerayZeroFromDiagonal K A M u τ left≡right =
  trans
    (cong (Scalar.neg S)
      (trans
        (cong (realPart A)
          (trans
            (cong (innerC A test)
              (diagonalSelfInputInteractionVectorZero K A (coefficient u) τ
                left≡right (divergenceFree u (Lattice.left τ))))
            (innerZeroRight A test)))
        (realPartZero A)))
    (Algebra.negZero K)
  where
  S = Algebra.orderedScalar K
  test = conjugateVector A
    (coefficient u (Lattice.modeNeg (Lattice.out τ)))

canonicalModalTransferNoLerayEqualsUniform :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  canonicalModalTransferNoLeray K A (coefficient u) τ ≡
  uniformModalTransferNoLeray K A (coefficient u) τ
canonicalModalTransferNoLerayEqualsUniform K A M u τ
  with Support.latticeModeDecEq (Lattice.left τ) (Lattice.right τ)
... | yes left≡right =
  trans
    (sym (Algebra.addZeroRight K
      (orderedModalTransferNoLeray K A (coefficient u) τ)))
    (cong (Scalar._+_ S
      (orderedModalTransferNoLeray K A (coefficient u) τ))
      (sym
        (orderedModalTransferNoLerayZeroFromDiagonal K A M u
          (Lattice.triadSwap τ) (swapPreservesDiagonalInputs τ left≡right))))
  where S = Algebra.orderedScalar K
... | no _ = refl

canonicalModalTransferWithoutLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  canonicalModalTransfer K A (coefficient u) τ ≡
  canonicalModalTransferNoLeray K A (coefficient u) τ
canonicalModalTransferWithoutLeray K A M u τ
  with Support.latticeModeDecEq (Lattice.left τ) (Lattice.right τ)
... | yes _ = orderedModalTransferWithoutLeray K A M u τ
... | no _ = cong₂ (Scalar._+_ (Algebra.orderedScalar K))
  (orderedModalTransferWithoutLeray K A M u τ)
  (orderedModalTransferWithoutLeray K A M u (Lattice.triadSwap τ))

triadCycleTwice : Lattice.LatticeTriad → Lattice.LatticeTriad
triadCycleTwice τ = Lattice.triadCycle (Lattice.triadCycle τ)

record PhysicalModalTransferTriple
    (K : Algebra.ExactOrderedCommutativeRing)
    (A : FiniteComplexFourierAuthority K)
    (u : Lattice.LatticeMode3 → Vec3C A)
    (τ : Lattice.LatticeTriad) : Set where
  field
    transferP transferQ transferR : Scalar.Scalar (Algebra.orderedScalar K)

open PhysicalModalTransferTriple public

physicalModalTransferTriple :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  PhysicalModalTransferTriple K A u τ
physicalModalTransferTriple K A u τ = record
  { transferP = canonicalModalTransfer K A u (Lattice.triadCycle τ)
  ; transferQ = canonicalModalTransfer K A u (triadCycleTwice τ)
  ; transferR = canonicalModalTransfer K A u τ
  }

modalTransferPWithoutLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  transferP (physicalModalTransferTriple K A (coefficient u) τ) ≡
  canonicalModalTransferNoLeray K A (coefficient u) (Lattice.triadCycle τ)
modalTransferPWithoutLeray K A M u τ =
  canonicalModalTransferWithoutLeray K A M u (Lattice.triadCycle τ)

modalTransferQWithoutLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  transferQ (physicalModalTransferTriple K A (coefficient u) τ) ≡
  canonicalModalTransferNoLeray K A (coefficient u) (triadCycleTwice τ)
modalTransferQWithoutLeray K A M u τ =
  canonicalModalTransferWithoutLeray K A M u (triadCycleTwice τ)

modalTransferRWithoutLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  transferR (physicalModalTransferTriple K A (coefficient u) τ) ≡
  canonicalModalTransferNoLeray K A (coefficient u) τ
modalTransferRWithoutLeray K A M u τ =
  canonicalModalTransferWithoutLeray K A M u τ

-- The exact concrete left-hand side of the pending triad-cancellation
-- theorem.  The companion no-Leray form is obtained solely by the three
-- projector-removal identities above; no conservation statement enters here.
modalTransferSum :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Scalar.Scalar (Algebra.orderedScalar K)
modalTransferSum K A u τ =
  Scalar._+_ S
    (Scalar._+_ S (transferP triple) (transferQ triple))
    (transferR triple)
  where
  S = Algebra.orderedScalar K
  triple = physicalModalTransferTriple K A u τ

modalTransferSumNoLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Scalar.Scalar (Algebra.orderedScalar K)
modalTransferSumNoLeray K A u τ =
  Scalar._+_ S
    (Scalar._+_ S
      (canonicalModalTransferNoLeray K A u (Lattice.triadCycle τ))
      (canonicalModalTransferNoLeray K A u (triadCycleTwice τ)))
    (canonicalModalTransferNoLeray K A u τ)
  where
  S = Algebra.orderedScalar K

uniformModalTransferSumNoLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Scalar.Scalar (Algebra.orderedScalar K)
uniformModalTransferSumNoLeray K A u τ = Scalar._+_ S
  (Scalar._+_ S
    (uniformModalTransferNoLeray K A u (Lattice.triadCycle τ))
    (uniformModalTransferNoLeray K A u (triadCycleTwice τ)))
  (uniformModalTransferNoLeray K A u τ)
  where S = Algebra.orderedScalar K

modalTransferSumNoLerayEqualsUniform :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  modalTransferSumNoLeray K A (coefficient u) τ ≡
  uniformModalTransferSumNoLeray K A (coefficient u) τ
modalTransferSumNoLerayEqualsUniform K A M u τ =
  cong₂ (Scalar._+_ S)
    (cong₂ (Scalar._+_ S)
      (canonicalModalTransferNoLerayEqualsUniform K A M u (Lattice.triadCycle τ))
      (canonicalModalTransferNoLerayEqualsUniform K A M u (triadCycleTwice τ)))
    (canonicalModalTransferNoLerayEqualsUniform K A M u τ)
  where S = Algebra.orderedScalar K

-- The six complex occurrences that remain after the three Leray removals.
-- Negation is kept inside every occurrence so that applying `realPart` is a
-- purely additive calculation; no claim is made that this complex sum itself
-- vanishes.
sixTermComplexNormalForm :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Complex A
sixTermComplexNormalForm K A u τ = _+ᶜ_ A
  (_+ᶜ_ A
    (_+ᶜ_ A
      (FiniteComplexFourierAuthority.-ᶜ_ A
        (orderedModalComplexTerm K A u (Lattice.triadCycle τ)))
      (FiniteComplexFourierAuthority.-ᶜ_ A (orderedModalComplexTerm K A u
        (Lattice.triadSwap (Lattice.triadCycle τ)))))
    (_+ᶜ_ A
      (FiniteComplexFourierAuthority.-ᶜ_ A
        (orderedModalComplexTerm K A u (triadCycleTwice τ)))
      (FiniteComplexFourierAuthority.-ᶜ_ A (orderedModalComplexTerm K A u
        (Lattice.triadSwap (triadCycleTwice τ))))))
  (_+ᶜ_ A
    (FiniteComplexFourierAuthority.-ᶜ_ A (orderedModalComplexTerm K A u τ))
    (FiniteComplexFourierAuthority.-ᶜ_ A
      (orderedModalComplexTerm K A u (Lattice.triadSwap τ))))

realPartSixTermComplexNormalForm :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  realPart A (sixTermComplexNormalForm K A u τ) ≡
  uniformModalTransferSumNoLeray K A u τ
realPartSixTermComplexNormalForm K A u τ =
  trans
    (realPartAdd A leftPairs thirdPair)
    (cong₂ (Scalar._+_ S)
      (trans
        (realPartAdd A firstPair secondPair)
        (cong₂ (Scalar._+_ S)
          (trans
            (realPartAdd A first firstSwap)
            (cong₂ (Scalar._+_ S) (realPartNeg A firstTerm)
              (realPartNeg A firstSwapTerm)))
          (trans
            (realPartAdd A second secondSwap)
            (cong₂ (Scalar._+_ S) (realPartNeg A secondTerm)
              (realPartNeg A secondSwapTerm)))))
      (trans
        (realPartAdd A third thirdSwap)
        (cong₂ (Scalar._+_ S) (realPartNeg A thirdTerm)
          (realPartNeg A thirdSwapTerm))))
  where
  S = Algebra.orderedScalar K
  c₁ = Lattice.triadCycle τ
  c₂ = triadCycleTwice τ
  c₃ = τ
  firstTerm = orderedModalComplexTerm K A u c₁
  firstSwapTerm = orderedModalComplexTerm K A u (Lattice.triadSwap c₁)
  secondTerm = orderedModalComplexTerm K A u c₂
  secondSwapTerm = orderedModalComplexTerm K A u (Lattice.triadSwap c₂)
  thirdTerm = orderedModalComplexTerm K A u c₃
  thirdSwapTerm = orderedModalComplexTerm K A u (Lattice.triadSwap c₃)
  first = FiniteComplexFourierAuthority.-ᶜ_ A firstTerm
  firstSwap = FiniteComplexFourierAuthority.-ᶜ_ A firstSwapTerm
  second = FiniteComplexFourierAuthority.-ᶜ_ A secondTerm
  secondSwap = FiniteComplexFourierAuthority.-ᶜ_ A secondSwapTerm
  third = FiniteComplexFourierAuthority.-ᶜ_ A thirdTerm
  thirdSwap = FiniteComplexFourierAuthority.-ᶜ_ A thirdSwapTerm
  firstPair = _+ᶜ_ A first firstSwap
  secondPair = _+ᶜ_ A second secondSwap
  thirdPair = _+ᶜ_ A third thirdSwap
  leftPairs = _+ᶜ_ A firstPair secondPair

threeTransferSumWithoutLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  modalTransferSum K A (coefficient u) τ ≡
  modalTransferSumNoLeray K A (coefficient u) τ
threeTransferSumWithoutLeray K A M u τ =
  cong₂ (Scalar._+_ S)
    (cong₂ (Scalar._+_ S)
      (modalTransferPWithoutLeray K A M u τ)
      (modalTransferQWithoutLeray K A M u τ))
    (modalTransferRWithoutLeray K A M u τ)
  where
  S = Algebra.orderedScalar K

threeTransferSumRealNormalForm :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  modalTransferSum K A (coefficient u) τ ≡
  realPart A (sixTermComplexNormalForm K A (coefficient u) τ)
threeTransferSumRealNormalForm K A M u τ =
  trans
    (threeTransferSumWithoutLeray K A M u τ)
    (trans
      (modalTransferSumNoLerayEqualsUniform K A M u τ)
      (sym (realPartSixTermComplexNormalForm K A (coefficient u) τ)))

-- This is the exact remaining local Fourier calculation, decomposed into
-- atomic facts rather than hidden behind a triad-conservation field.  The
-- six equations identify the real parts of the concrete complex occurrences
-- with the six scalar atoms used by `FiniteTriadCancellationAlgebra`; the
-- relation record contains only zero-sum-wavevector and incompressibility
-- consequences.  A future concrete C³/Leray implementation must prove these
-- local facts from bilinearity and reality, not assume their final sum.
record SixTermRealPartAtomBridge
    (K : Algebra.ExactOrderedCommutativeRing)
    (A : FiniteComplexFourierAuthority K) (M : Nat)
    (u : FiniteFourierNSState K A M) (τ : Lattice.LatticeTriad) : Set₁ where
  field
    pA qA rA pB qB rB pC qC rC : Scalar.Scalar (Algebra.orderedScalar K)
    pairAB pairAC pairBC : Scalar.Scalar (Algebra.orderedScalar K)

    relations : Cancel.SixTermTriadRelations K
      pA qA rA pB qB rB pC qC rC

    firstOccurrence :
      Scalar.neg (Algebra.orderedScalar K) (realPart A
        (orderedModalComplexTerm K A (coefficient u) (Lattice.triadCycle τ))) ≡
      Scalar._*_ (Algebra.orderedScalar K) qA pairBC
    secondOccurrence :
      Scalar.neg (Algebra.orderedScalar K) (realPart A
        (orderedModalComplexTerm K A (coefficient u)
          (Lattice.triadSwap (Lattice.triadCycle τ)))) ≡
      Scalar._*_ (Algebra.orderedScalar K) pB pairAC
    thirdOccurrence :
      Scalar.neg (Algebra.orderedScalar K) (realPart A
        (orderedModalComplexTerm K A (coefficient u) (triadCycleTwice τ))) ≡
      Scalar._*_ (Algebra.orderedScalar K) rB pairAC
    fourthOccurrence :
      Scalar.neg (Algebra.orderedScalar K) (realPart A
        (orderedModalComplexTerm K A (coefficient u)
          (Lattice.triadSwap (triadCycleTwice τ)))) ≡
      Scalar._*_ (Algebra.orderedScalar K) qC pairAB
    fifthOccurrence :
      Scalar.neg (Algebra.orderedScalar K)
        (realPart A (orderedModalComplexTerm K A (coefficient u) τ)) ≡
      Scalar._*_ (Algebra.orderedScalar K) pC pairAB
    sixthOccurrence :
      Scalar.neg (Algebra.orderedScalar K) (realPart A
        (orderedModalComplexTerm K A (coefficient u) (Lattice.triadSwap τ))) ≡
      Scalar._*_ (Algebra.orderedScalar K) rA pairBC

open SixTermRealPartAtomBridge public

sixTermComplexNormalFormRealPartZero :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  SixTermRealPartAtomBridge K A M u τ →
  realPart A (sixTermComplexNormalForm K A (coefficient u) τ) ≡
  Scalar.zero (Algebra.orderedScalar K)
sixTermComplexNormalFormRealPartZero K A M u τ B =
  trans
    (realPartSixTermComplexNormalForm K A (coefficient u) τ)
    (trans atomsToNumerator
      (Cancel.sixTermConvectionCancellation K
        (pA B) (qA B) (rA B) (pB B) (qB B) (rB B) (pC B) (qC B) (rC B)
        (pairAB B) (pairAC B) (pairBC B) (relations B)))
  where
  S = Algebra.orderedScalar K
  a₁ = Scalar.neg S (realPart A
    (orderedModalComplexTerm K A (coefficient u) (Lattice.triadCycle τ)))
  a₂ = Scalar.neg S (realPart A
    (orderedModalComplexTerm K A (coefficient u)
      (Lattice.triadSwap (Lattice.triadCycle τ))))
  a₃ = Scalar.neg S (realPart A
    (orderedModalComplexTerm K A (coefficient u) (triadCycleTwice τ)))
  a₄ = Scalar.neg S (realPart A
    (orderedModalComplexTerm K A (coefficient u)
      (Lattice.triadSwap (triadCycleTwice τ))))
  a₅ = Scalar.neg S (realPart A (orderedModalComplexTerm K A (coefficient u) τ))
  a₆ = Scalar.neg S (realPart A
    (orderedModalComplexTerm K A (coefficient u) (Lattice.triadSwap τ)))
  atomsToNumerator :
    uniformModalTransferSumNoLeray K A (coefficient u) τ ≡
    Cancel.sixTermConvectionNumerator K
      (pA B) (qA B) (rA B) (pB B) (qB B) (rB B) (pC B) (qC B) (rC B)
      (pairAB B) (pairAC B) (pairBC B)
  atomsToNumerator = trans
    (Algebra.addAssociative K
      (Scalar._+_ S a₁ a₂) (Scalar._+_ S a₃ a₄) (Scalar._+_ S a₅ a₆))
    (cong₂ (Scalar._+_ S)
      (cong₂ (Scalar._+_ S) (firstOccurrence B) (secondOccurrence B))
      (cong₂ (Scalar._+_ S)
        (cong₂ (Scalar._+_ S) (thirdOccurrence B) (fourthOccurrence B))
        (cong₂ (Scalar._+_ S) (fifthOccurrence B) (sixthOccurrence B))))

-- This is the live Navier--Stokes theorem.  The triple above is now a
-- concrete diagonal-aware Fourier/Leray expression; the record has no
-- fallback field from which conservation could be assumed.
record PhysicalModalTriadTransferConservation
    (K : Algebra.ExactOrderedCommutativeRing)
    (A : FiniteComplexFourierAuthority K) (M : Nat)
    (u : FiniteFourierNSState K A M) : Set₁ where
  field
    conserves : (τ : Lattice.LatticeTriad) →
      Lattice.zeroSum? τ ≡ true →
      Scalar._+_ (Algebra.orderedScalar K)
        (Scalar._+_ (Algebra.orderedScalar K)
          (transferP (physicalModalTransferTriple K A (coefficient u) τ))
          (transferQ (physicalModalTransferTriple K A (coefficient u) τ)))
        (transferR (physicalModalTransferTriple K A (coefficient u) τ)) ≡
      Scalar.zero (Algebra.orderedScalar K)

open PhysicalModalTriadTransferConservation public

physicalModalTriadTransferConservationFromAtoms :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) →
  ((τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
    SixTermRealPartAtomBridge K A M u τ) →
  PhysicalModalTriadTransferConservation K A M u
physicalModalTriadTransferConservationFromAtoms K A M u atoms = record
  { conserves = λ τ zeroSum →
      trans
        (threeTransferSumRealNormalForm K A M u τ)
        (sixTermComplexNormalFormRealPartZero K A M u τ (atoms τ zeroSum))
  }

modalTriadTransferFromPhysicalConservation :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) →
  PhysicalModalTriadTransferConservation K A M u →
  (τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
  ModalTriadTransfer (Algebra.orderedScalar K) τ
modalTriadTransferFromPhysicalConservation K A M u C τ zeroSum = record
  { transferLeft = transferP triple
  ; transferRight = transferQ triple
  ; transferOut = transferR triple
  ; conservation = conserves C τ zeroSum
  }
  where
  triple = physicalModalTransferTriple K A (coefficient u) τ

formalWeightedEnergyDerivative :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M →
  FiniteFourierNSState K A M →
  Scalar.Scalar (Algebra.orderedScalar K)
formalWeightedEnergyDerivative K A M z u =
  Energy.sumScalarList (Algebra.orderedScalar K)
    (terms (Sector.cutoffModes M))
  where
  terms : List Lattice.LatticeMode3 → List (Scalar.Scalar (Algebra.orderedScalar K))
  terms [] = []
  terms (k ∷ ks) =
    Scalar._*_ (Algebra.orderedScalar K) (Energy.weight z k)
      (realPart A (innerC A (coefficient u k) (velocityDot u k))) ∷
    terms ks

formalWeightedViscousDissipation :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M →
  FiniteFourierNSState K A M →
  Scalar.Scalar (Algebra.orderedScalar K)
formalWeightedViscousDissipation K A M z u =
  Energy.sumScalarList (Algebra.orderedScalar K)
    (terms (Sector.cutoffModes M))
  where
  S = Algebra.orderedScalar K
  terms : List Lattice.LatticeMode3 → List (Scalar.Scalar S)
  terms [] = []
  terms (k ∷ ks) =
    Scalar._*_ S (viscosity u)
      (Scalar._*_ S (Energy.weight z k)
        (Scalar._*_ S (modeSquaredNorm u k)
          (normSq A (coefficient u k)))) ∷
    terms ks

finiteComplexFourierDynamicsClosed : Bool
finiteComplexFourierDynamicsClosed = false
