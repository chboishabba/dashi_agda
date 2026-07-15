module DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber as Exact
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Algebra
import DASHI.Physics.Closure.NSTriadKNExactRingSolverBridge as RingBridge

------------------------------------------------------------------------
-- Diagonal Fourier-multiplier energy: exact finite algebraic surface.
--
-- This module deliberately separates the Fourier/PDE identity from the
-- auxiliary pair-Laplacian.  A diagonal multiplier produces a triad factor
-- linear in the multiplier differences.  The quadratic edge contrast enters
-- only after a separate Young/Cauchy estimate and therefore carries a flux
-- remainder.
------------------------------------------------------------------------

sub : (S : Scalar.ExactOrderedScalar) →
  Scalar.Scalar S → Scalar.Scalar S → Scalar.Scalar S
sub S a b = Scalar._+_ S a (Scalar.neg S b)

square : (S : Scalar.ExactOrderedScalar) → Scalar.Scalar S → Scalar.Scalar S
square S x = Scalar._*_ S x x

sumScalarList :
  (S : Scalar.ExactOrderedScalar) → List (Scalar.Scalar S) → Scalar.Scalar S
sumScalarList S [] = Scalar.zero S
sumScalarList S (x ∷ xs) = Scalar._+_ S x (sumScalarList S xs)

record AdmissibleFourierMultiplier
    (S : Scalar.ExactOrderedScalar) (M : Nat) : Set₁ where
  field
    weight : Lattice.LatticeMode3 → Scalar.Scalar S
    nonnegative :
      (k : Lattice.LatticeMode3) → Scalar.Nonnegative S (weight k)
    realityEven :
      (k : Lattice.LatticeMode3) → weight (Lattice.modeNeg k) ≡ weight k

open AdmissibleFourierMultiplier public

-- The three modal transfers are intentionally distinct from the earlier
-- one-output orbit coefficient Gamma.  The latter is one component of this
-- vector after choosing an output; this carrier is the object needed by a
-- weighted energy identity.
record ModalTriadTransfer
    (S : Scalar.ExactOrderedScalar) (τ : Lattice.LatticeTriad) : Set where
  field
    transferLeft : Scalar.Scalar S
    transferRight : Scalar.Scalar S
    transferOut : Scalar.Scalar S

    conservation :
      Scalar._+_ S
        (Scalar._+_ S transferLeft transferRight)
        transferOut ≡ Scalar.zero S

open ModalTriadTransfer public

TriadTransferField :
  (S : Scalar.ExactOrderedScalar) → Set
TriadTransferField S = (τ : Lattice.LatticeTriad) → ModalTriadTransfer S τ

weightedTriadContribution :
  (S : Scalar.ExactOrderedScalar) → (M : Nat) →
  AdmissibleFourierMultiplier S M → TriadTransferField S →
  (τ : Lattice.LatticeTriad) → Scalar.Scalar S
weightedTriadContribution S M z T τ =
  Scalar._+_ S
    (Scalar._*_ S (weight z (Lattice.left τ)) (transferLeft (T τ)))
    (Scalar._+_ S
      (Scalar._*_ S (weight z (Lattice.right τ)) (transferRight (T τ)))
      (Scalar._*_ S (weight z (Lattice.out τ)) (transferOut (T τ))))

weightedTriadDifferenceForm :
  (S : Scalar.ExactOrderedScalar) → (M : Nat) →
  AdmissibleFourierMultiplier S M → TriadTransferField S →
  (τ : Lattice.LatticeTriad) → Scalar.Scalar S
weightedTriadDifferenceForm S M z T τ =
  Scalar.third S
    (Scalar._+_ S
      (Scalar._*_ S
        (sub S (weight z (Lattice.left τ)) (weight z (Lattice.right τ)))
        (sub S (transferLeft (T τ)) (transferRight (T τ))))
      (Scalar._+_ S
        (Scalar._*_ S
          (sub S (weight z (Lattice.left τ)) (weight z (Lattice.out τ)))
          (sub S (transferLeft (T τ)) (transferOut (T τ))))
        (Scalar._*_ S
          (sub S (weight z (Lattice.right τ)) (weight z (Lattice.out τ)))
          (sub S (transferRight (T τ)) (transferOut (T τ))))))

weightedTriadContributions :
  (S : Scalar.ExactOrderedScalar) → (M : Nat) →
  AdmissibleFourierMultiplier S M → TriadTransferField S →
  List Lattice.LatticeTriad → List (Scalar.Scalar S)
weightedTriadContributions S M z T [] = []
weightedTriadContributions S M z T (τ ∷ τs) =
  weightedTriadContribution S M z T τ ∷
  weightedTriadContributions S M z T τs

-- The first purely algebraic use of triad conservation.  It contains no
-- Fourier, Leray, or time-differentiation content: a zero-sum transfer triple
-- has only two independent components.
transferOutFromConservation :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (Tₚ T_q Tᵣ : Scalar.Scalar (Algebra.orderedScalar K)) →
  Scalar._+_ (Algebra.orderedScalar K)
    (Scalar._+_ (Algebra.orderedScalar K) Tₚ T_q) Tᵣ ≡
  Scalar.zero (Algebra.orderedScalar K) →
  Tᵣ ≡ Scalar.neg (Algebra.orderedScalar K)
    (Scalar._+_ (Algebra.orderedScalar K) Tₚ T_q)
transferOutFromConservation K Tₚ T_q Tᵣ conservation =
  trans step₁ (trans step₂ (trans step₃ (trans step₄ step₅)))
  where
  S = Algebra.orderedScalar K
  sumT = Scalar._+_ S Tₚ T_q
  negSumT = Scalar.neg S sumT
  step₁ : Tᵣ ≡ Scalar._+_ S (Scalar.zero S) Tᵣ
  step₁ = sym (Algebra.addZeroLeft K Tᵣ)
  step₂ : Scalar._+_ S (Scalar.zero S) Tᵣ ≡
          Scalar._+_ S (Scalar._+_ S negSumT sumT) Tᵣ
  step₂ = cong (λ x → Scalar._+_ S x Tᵣ)
    (sym (Algebra.addInverseLeft K sumT))
  step₃ : Scalar._+_ S (Scalar._+_ S negSumT sumT) Tᵣ ≡
          Scalar._+_ S negSumT (Scalar._+_ S sumT Tᵣ)
  step₃ = Algebra.addAssociative K negSumT sumT Tᵣ
  step₄ : Scalar._+_ S negSumT (Scalar._+_ S sumT Tᵣ) ≡
          Scalar._+_ S negSumT (Scalar.zero S)
  step₄ = cong (Scalar._+_ S negSumT) conservation
  step₅ : Scalar._+_ S negSumT (Scalar.zero S) ≡ negSumT
  step₅ = Algebra.addZeroRight K negSumT

modalTransferOutElimination :
  (K : Algebra.ExactOrderedCommutativeRing) →
  {τ : Lattice.LatticeTriad} →
  (T : ModalTriadTransfer (Algebra.orderedScalar K) τ) →
  transferOut T ≡
  Scalar.neg (Algebra.orderedScalar K)
    (Scalar._+_ (Algebra.orderedScalar K)
      (transferLeft T) (transferRight T))
modalTransferOutElimination K T =
  transferOutFromConservation K
    (transferLeft T) (transferRight T) (transferOut T) (conservation T)

weightedTransferScalar :
  (K : Algebra.ExactOrderedCommutativeRing) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K)
weightedTransferScalar K zₚ z_q zᵣ Tₚ T_q Tᵣ =
  Scalar._+_ S (Scalar._*_ S zₚ Tₚ)
    (Scalar._+_ S (Scalar._*_ S z_q T_q) (Scalar._*_ S zᵣ Tᵣ))
  where S = Algebra.orderedScalar K

symmetricTransferNumerator :
  (K : Algebra.ExactOrderedCommutativeRing) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K)
symmetricTransferNumerator K zₚ z_q zᵣ Tₚ T_q Tᵣ =
  Scalar._+_ S
    (Scalar._*_ S (sub S zₚ z_q) (sub S Tₚ T_q))
    (Scalar._+_ S
      (Scalar._*_ S (sub S zₚ zᵣ) (sub S Tₚ Tᵣ))
      (Scalar._*_ S (sub S z_q zᵣ) (sub S T_q Tᵣ)))
  where S = Algebra.orderedScalar K

-- The multiplier-difference formula is intentionally represented below by
-- `WeightedTriadDifferenceIdentity`.  Its proof needs an exact `1/3`
-- normalisation authority in addition to the ring laws used for the finite
-- six-term cancellation.  It is kept fail-closed rather than smuggling that
-- analytic scalar assumption into this finite algebra module.

------------------------------------------------------------------------
-- Finite weighted energy.
--
-- `half` is kept in this authority rather than added to ExactOrderedScalar:
-- the Gram lane never needs it.  The concrete real/complex Fourier instance
-- must prove `halfOfDouble`; no Nat-valued or diagnostic substitute is used.
------------------------------------------------------------------------

record FiniteWeightedEnergyAuthority
    (K : Algebra.ExactOrderedCommutativeRing) : Set₁ where
  field
    half : Scalar.Scalar (Algebra.orderedScalar K) →
           Scalar.Scalar (Algebra.orderedScalar K)
    halfOfDouble :
      (x : Scalar.Scalar (Algebra.orderedScalar K)) →
      half (Scalar._+_ (Algebra.orderedScalar K) x x) ≡ x

open FiniteWeightedEnergyAuthority public

weightedFourierEnergy :
  (K : Algebra.ExactOrderedCommutativeRing) →
  FiniteWeightedEnergyAuthority K →
  (z : AdmissibleFourierMultiplier (Algebra.orderedScalar K) 0) →
  (modeNormSq : Lattice.LatticeMode3 → Scalar.Scalar (Algebra.orderedScalar K)) →
  List Lattice.LatticeMode3 → Scalar.Scalar (Algebra.orderedScalar K)
weightedFourierEnergy K E z modeNormSq modes =
  half E
    (sumScalarList (Algebra.orderedScalar K)
      (mapEnergy modes))
  where
  mapEnergy : List Lattice.LatticeMode3 →
              List (Scalar.Scalar (Algebra.orderedScalar K))
  mapEnergy [] = []
  mapEnergy (k ∷ ks) =
    Scalar._*_ (Algebra.orderedScalar K) (weight z k) (modeNormSq k) ∷
    mapEnergy ks

------------------------------------------------------------------------
-- Exact theorem targets, fail-closed until the finite complex Fourier ODE
-- and a normalised ordered-field model are connected.
------------------------------------------------------------------------

record WeightedTriadDifferenceIdentity
    (K : Algebra.ExactOrderedCommutativeRing) : Set₁ where
  field
    thirdNormalizesTriple :
      (x : Scalar.Scalar (Algebra.orderedScalar K)) →
      Scalar.third (Algebra.orderedScalar K)
        (Scalar._+_ (Algebra.orderedScalar K)
          (Scalar._+_ (Algebra.orderedScalar K) x x) x) ≡ x

    weightedTriadContributionDifferenceForm :
      (M : Nat) →
      (z : AdmissibleFourierMultiplier (Algebra.orderedScalar K) M) →
      (T : TriadTransferField (Algebra.orderedScalar K)) →
      (τ : Lattice.LatticeTriad) →
      weightedTriadContribution (Algebra.orderedScalar K) M z T τ ≡
      weightedTriadDifferenceForm (Algebra.orderedScalar K) M z T τ

-- This is the exact PDE input still needed to turn the finite definitions
-- above into an energy identity.  It is deliberately not inhabited by the
-- pair-incidence/Gram construction.
record FiniteWeightedFourierEnergyDynamics
    (K : Algebra.ExactOrderedCommutativeRing) (M : Nat)
    (z : AdmissibleFourierMultiplier (Algebra.orderedScalar K) M)
    (T : TriadTransferField (Algebra.orderedScalar K))
    (triads : List Lattice.LatticeTriad) : Set₁ where
  field
    multiplierEnergyDerivative : Scalar.Scalar (Algebra.orderedScalar K)
    weightedViscousDissipation : Scalar.Scalar (Algebra.orderedScalar K)
    cutoffBoundaryRemainder : Scalar.Scalar (Algebra.orderedScalar K)

    finiteWeightedFourierEnergyIdentity :
      Scalar._+_ (Algebra.orderedScalar K)
        multiplierEnergyDerivative weightedViscousDissipation ≡
      Scalar._+_ (Algebra.orderedScalar K)
        (sumScalarList (Algebra.orderedScalar K)
          (weightedTriadContributions (Algebra.orderedScalar K) M z T triads))
        cutoffBoundaryRemainder

-- A Young/Cauchy estimate, when supplied by a genuine ordered-field and
-- absolute-value authority, must control the *linear* form by the quadratic
-- Gram contrast plus this independently named flux term.  It must never
-- identify the two expressions definitionally.
record Stage3GramEnergyControl
    (S : Scalar.ExactOrderedScalar) : Set₁ where
  field
    _≤_ : Scalar.Scalar S → Scalar.Scalar S → Set
    absoluteWeightedError : Scalar.Scalar S
    gramContrast : Scalar.Scalar S
    transferFluxRemainder : Scalar.Scalar S

    weightedErrorBound :
      absoluteWeightedError ≤
      Scalar._+_ S gramContrast transferFluxRemainder

    -- This is intentionally a named downstream analytic obligation, not an
    -- empty marker.  The intended bound is supplied by the selected profile
    -- norms/Schur estimate after the Fourier flux has been identified.
    TransferFluxRemainderControlled : Set

weightedFourierEnergyIdentityClosed : Bool
weightedFourierEnergyIdentityClosed = false
