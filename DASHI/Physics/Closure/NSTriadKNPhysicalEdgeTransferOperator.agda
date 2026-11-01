module DASHI.Physics.Closure.NSTriadKNPhysicalEdgeTransferOperator where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy

------------------------------------------------------------------------
-- Physical weighted Fourier error as an edge-transfer bilinear form.
--
-- This is deliberately distinct from the diagnostic positive Gram forms
-- Lneg and Labs.  A diagonal Fourier multiplier has a triad contribution
-- linear in its edge differences, so its exact controller is bilinear.
------------------------------------------------------------------------

sub : (S : Scalar.ExactOrderedScalar) →
  Scalar.Scalar S → Scalar.Scalar S → Scalar.Scalar S
sub S a b = Scalar._+_ S a (Scalar.neg S b)

record TriadEdgeField (S : Scalar.ExactOrderedScalar) : Set where
  constructor mkTriadEdgeField
  field
    left-right : Scalar.Scalar S
    left-out   : Scalar.Scalar S
    right-out  : Scalar.Scalar S

open TriadEdgeField public

edgePairing :
  (S : Scalar.ExactOrderedScalar) →
  TriadEdgeField S → TriadEdgeField S → Scalar.Scalar S
edgePairing S x y =
  Scalar._+_ S
    (Scalar._*_ S (left-right x) (left-right y))
    (Scalar._+_ S
      (Scalar._*_ S (left-out x) (left-out y))
      (Scalar._*_ S (right-out x) (right-out y)))

-- The finite incidence-difference operator B, evaluated on one labelled
-- zero-sum triad.  Its three coordinates retain occurrences, including the
-- diagonal multigraph occurrence when two input modes coincide.
multiplierEdgeDifference :
  (S : Scalar.ExactOrderedScalar) → (M : Nat) →
  Energy.AdmissibleFourierMultiplier S M → Energy.ZeroSumTriad →
  TriadEdgeField S
multiplierEdgeDifference S M z σ =
  mkTriadEdgeField
    (sub S (Energy.weight z (Lattice.left τ))
      (Energy.weight z (Lattice.right τ)))
    (sub S (Energy.weight z (Lattice.left τ))
      (Energy.weight z (Lattice.out τ)))
    (sub S (Energy.weight z (Lattice.right τ))
      (Energy.weight z (Lattice.out τ)))
  where
  τ = Energy.triad σ

-- The physical transfer field T(u), expressed in the same oriented edge
-- coordinates.  This is not a nonnegative coefficient and is not folded
-- into a pair-incidence Gram matrix.
modalTransferEdgeDifference :
  (S : Scalar.ExactOrderedScalar) →
  Energy.ZeroSumTriadTransferField S → Energy.ZeroSumTriad →
  TriadEdgeField S
modalTransferEdgeDifference S T σ =
  mkTriadEdgeField
    (sub S (Energy.transferLeft transfer) (Energy.transferRight transfer))
    (sub S (Energy.transferLeft transfer) (Energy.transferOut transfer))
    (sub S (Energy.transferRight transfer) (Energy.transferOut transfer))
  where
  transfer = T σ

physicalWeightedErrorTriad :
  (S : Scalar.ExactOrderedScalar) → (M : Nat) →
  Energy.AdmissibleFourierMultiplier S M → Energy.ZeroSumTriadTransferField S →
  Energy.ZeroSumTriad → Scalar.Scalar S
physicalWeightedErrorTriad = Energy.weightedZeroSumTriadDifferenceForm

physicalWeightedErrorBilinearTriad :
  (S : Scalar.ExactOrderedScalar) → (M : Nat) →
  (z : Energy.AdmissibleFourierMultiplier S M) →
  (T : Energy.ZeroSumTriadTransferField S) → (σ : Energy.ZeroSumTriad) →
  physicalWeightedErrorTriad S M z T σ ≡
  Scalar.third S
    (edgePairing S (multiplierEdgeDifference S M z σ)
      (modalTransferEdgeDifference S T σ))
physicalWeightedErrorBilinearTriad S M z T σ = refl

physicalWeightedError :
  (S : Scalar.ExactOrderedScalar) → (M : Nat) →
  Energy.AdmissibleFourierMultiplier S M → Energy.ZeroSumTriadTransferField S →
  List Energy.ZeroSumTriad → Scalar.Scalar S
physicalWeightedError S M z T [] = Scalar.zero S
physicalWeightedError S M z T (σ ∷ σs) =
  Scalar._+_ S (physicalWeightedErrorTriad S M z T σ)
    (physicalWeightedError S M z T σs)

edgeTransferBilinearForm :
  (S : Scalar.ExactOrderedScalar) → (M : Nat) →
  Energy.AdmissibleFourierMultiplier S M → Energy.ZeroSumTriadTransferField S →
  List Energy.ZeroSumTriad → Scalar.Scalar S
edgeTransferBilinearForm S M z T [] = Scalar.zero S
edgeTransferBilinearForm S M z T (σ ∷ σs) =
  Scalar._+_ S
    (Scalar.third S
      (edgePairing S (multiplierEdgeDifference S M z σ)
        (modalTransferEdgeDifference S T σ)))
    (edgeTransferBilinearForm S M z T σs)

physicalWeightedErrorBilinearIdentity :
  (S : Scalar.ExactOrderedScalar) → (M : Nat) →
  (z : Energy.AdmissibleFourierMultiplier S M) →
  (T : Energy.ZeroSumTriadTransferField S) →
  (triads : List Energy.ZeroSumTriad) →
  physicalWeightedError S M z T triads ≡
  edgeTransferBilinearForm S M z T triads
physicalWeightedErrorBilinearIdentity S M z T [] = refl
physicalWeightedErrorBilinearIdentity S M z T (σ ∷ σs) =
  cong₂ (Scalar._+_ S)
    (physicalWeightedErrorBilinearTriad S M z T σ)
    (physicalWeightedErrorBilinearIdentity S M z T σs)
