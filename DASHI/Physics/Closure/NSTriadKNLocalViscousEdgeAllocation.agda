module DASHI.Physics.Closure.NSTriadKNLocalViscousEdgeAllocation where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalEdgeTransferOperator as Edge
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy

------------------------------------------------------------------------
-- Local viscous allocation for the bilinear Fourier error.
--
-- A mode participates in an R-dependent number of cutoff triads.  Hence a
-- fixed per-occurrence weight cannot give a cutoff-uniform overlap bound.
-- The authoritative object below requires degree-normalised occurrence
-- weights and records the resulting finite overlap theorem explicitly.
------------------------------------------------------------------------

data EdgeSlot : Set where
  left-right left-out right-out : EdgeSlot

record EdgeOccurrence : Set where
  constructor mkEdgeOccurrence
  field
    triad : Energy.ZeroSumTriad
    slot  : EdgeSlot

open EdgeOccurrence public

edgeOccurrencesFor : Energy.ZeroSumTriad → List EdgeOccurrence
edgeOccurrencesFor σ =
  mkEdgeOccurrence σ left-right ∷
  mkEdgeOccurrence σ left-out ∷
  mkEdgeOccurrence σ right-out ∷ []

expandEdgeOccurrences : List Energy.ZeroSumTriad → List EdgeOccurrence
expandEdgeOccurrences [] = []
expandEdgeOccurrences (σ ∷ σs) =
  edgeOccurrencesFor σ ++ expandEdgeOccurrences σs
  where
  infixr 5 _++_
  _++_ : {A : Set} → List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

edgeSource : EdgeOccurrence → Lattice.LatticeMode3
edgeSource (mkEdgeOccurrence σ left-right) = Lattice.left (Energy.triad σ)
edgeSource (mkEdgeOccurrence σ left-out) = Lattice.left (Energy.triad σ)
edgeSource (mkEdgeOccurrence σ right-out) = Lattice.right (Energy.triad σ)

edgeTarget : EdgeOccurrence → Lattice.LatticeMode3
edgeTarget (mkEdgeOccurrence σ left-right) = Lattice.right (Energy.triad σ)
edgeTarget (mkEdgeOccurrence σ left-out) = Lattice.out (Energy.triad σ)
edgeTarget (mkEdgeOccurrence σ right-out) = Lattice.out (Energy.triad σ)

edgeMultiplierDifference :
  (S : Scalar.ExactOrderedScalar) → (M : Nat) →
  Energy.AdmissibleFourierMultiplier S M → EdgeOccurrence → Scalar.Scalar S
edgeMultiplierDifference S M z (mkEdgeOccurrence σ left-right) =
  Edge.left-right (Edge.multiplierEdgeDifference S M z σ)
edgeMultiplierDifference S M z (mkEdgeOccurrence σ left-out) =
  Edge.left-out (Edge.multiplierEdgeDifference S M z σ)
edgeMultiplierDifference S M z (mkEdgeOccurrence σ right-out) =
  Edge.right-out (Edge.multiplierEdgeDifference S M z σ)

edgeTransferDifference :
  (S : Scalar.ExactOrderedScalar) →
  Energy.ZeroSumTriadTransferField S → EdgeOccurrence → Scalar.Scalar S
edgeTransferDifference S T (mkEdgeOccurrence σ left-right) =
  Edge.left-right (Edge.modalTransferEdgeDifference S T σ)
edgeTransferDifference S T (mkEdgeOccurrence σ left-out) =
  Edge.left-out (Edge.modalTransferEdgeDifference S T σ)
edgeTransferDifference S T (mkEdgeOccurrence σ right-out) =
  Edge.right-out (Edge.modalTransferEdgeDifference S T σ)

-- `third one` is the Python-style three-slot convention inside one triad.
-- It is not a global overlap weight: using it alone would count a mode once
-- for every incident triad and its overlap grows with the cutoff.
uniformThreeSlotWeight : (S : Scalar.ExactOrderedScalar) → Scalar.Scalar S
uniformThreeSlotWeight S = Scalar.third S (Scalar.one S)

localDissipationTerms :
  (S : Scalar.ExactOrderedScalar) →
  (EdgeOccurrence → Scalar.Scalar S) →
  List EdgeOccurrence → List (Scalar.Scalar S)
localDissipationTerms S d [] = []
localDissipationTerms S d (e ∷ es) = d e ∷ localDissipationTerms S d es

record LocalViscousEdgeAllocation
    (S : Scalar.ExactOrderedScalar) (M : Nat)
    (z : Energy.AdmissibleFourierMultiplier S M)
    (triads : List Energy.ZeroSumTriad) : Set₁ where
  field
    viscosity : Scalar.Scalar S

    -- This is the actual modal summand of the chosen weighted dissipation.
    -- The Fourier dynamics module must later instantiate it by
    -- nu * |k|^2 * z_k * |u_k|^2.
    modalViscousDensity : Lattice.LatticeMode3 → Scalar.Scalar S

    -- Degree-normalised edge shares.  A concrete finite cutoff construction
    -- should use reciprocal incidence degrees (or an equivalent partition of
    -- unity), not the uniformThreeSlotWeight above.
    degreeNormalisedWeight : EdgeOccurrence → Scalar.Scalar S
    localDissipation : EdgeOccurrence → Scalar.Scalar S
    totalDissipation : Scalar.Scalar S
    overlapConstant : Scalar.Scalar S

    localDissipationFormula :
      (e : EdgeOccurrence) →
      localDissipation e ≡
        Scalar._*_ S (degreeNormalisedWeight e)
          (Scalar._+_ S
            (modalViscousDensity (edgeSource e))
            (modalViscousDensity (edgeTarget e)))

    boundedOverlap :
      Scalar._≤_ S
        (Energy.sumScalarList S
          (localDissipationTerms S localDissipation
            (expandEdgeOccurrences triads)))
        (Scalar._*_ S overlapConstant totalDissipation)

open LocalViscousEdgeAllocation public

-- This is deliberately false until the exact cutoff incidence degrees and
-- reciprocal scalar authority are constructed.  In particular, no
-- cutoff-uniform Cmult is asserted merely from finiteness of the carrier.
localViscousEdgeAllocationClosed : Bool
localViscousEdgeAllocationClosed = false
