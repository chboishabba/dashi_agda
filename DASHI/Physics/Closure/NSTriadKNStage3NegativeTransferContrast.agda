module DASHI.Physics.Closure.NSTriadKNStage3NegativeTransferContrast where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.List.Base using (List)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber as Exact
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNAdmissibleFourierShellData as Fourier
import DASHI.Physics.Closure.NSTriadKNExactPairIncidenceGramAssembly as PairGram
import DASHI.Physics.Closure.NSTriadKNExactRetainedPairIncidences as Incidence
import DASHI.Physics.Closure.NSTriadKNPhysicalGramOperatorAssembly as Gram
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffModeSupport as Support
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as PhysicalSector

------------------------------------------------------------------------
-- Stage-3 negative-transfer contrast.
--
-- This is deliberately a scalar-observable construction.  Its vectors are
-- profile/error coordinates z on the finite mode carrier, not the vector
-- Fourier coefficients u-hat.  The coefficient map is to be instantiated
-- by m^-_tau(u) / 3 on each of the three incidences of tau.
--
-- Hence, for b_(tau,ab) = e_a - e_b, the intended concrete instance is
--
--   B(u;z) = sum_tau m^-_tau(u)/3
--              [ (z_p-z_q)^2 + (z_p-z_r)^2 + (z_q-z_r)^2 ].
--
-- The theorem below proves the exact Gram identity for any finite concrete
-- instance of that data.  It makes no claim that this auxiliary contrast is
-- the signed Fourier convection term.
------------------------------------------------------------------------

record NegativeTransferContrastData
    {S : Exact.ExactScalarOperations} {A : Set}
    (H : Gram.FiniteShellInnerProductSpace S) : Set₁ where
  constructor mkNegativeTransferContrastData
  field
    retainedPairIncidences : List A
    negativeEdgeCoefficient :
      A → Exact.ExactScalarOperations.Carrier S
    pairIncidenceVector : A → Gram.Vector H

open NegativeTransferContrastData public

-- This constructor binds the generic exact finite edge fold to the physical
-- output-shell/cutoff carrier.  The caller must still establish that the
-- supplied coefficient is m^-_tau(u)/3 and that the supplied vector is the
-- corresponding basis difference; those are Fourier/vector-space theorems,
-- not list-normalization facts.
physicalCutoffNegativeTransferContrastData :
  {S : Exact.ExactScalarOperations} →
  (N R : Nat) →
  (sector : PhysicalSector.ExactOutputRetainedSectorLaw N R) →
  (H : Gram.FiniteShellInnerProductSpace S) →
  (negativeEdgeCoefficient :
    Incidence.PairIncidence → Exact.ExactScalarOperations.Carrier S) →
  (pairIncidenceVector : Incidence.PairIncidence → Gram.Vector H) →
  NegativeTransferContrastData {A = Incidence.PairIncidence} H
physicalCutoffNegativeTransferContrastData N R sector H coefficient vector =
  mkNegativeTransferContrastData
    (Incidence.physicalCutoffRetainedPairIncidences N R sector)
    coefficient
    vector

-- The physical coefficient specialization.  The incidence coefficient is
-- definitionally the triad negative coefficient (which already contains the
-- 1/3 edge allocation) evaluated at `triad r`.  This removes any independent
-- coherence/weight input from the physical cutoff contrast.
physicalCutoffNegativeTransferContrastFromFourierData :
  (S : Scalar.ExactOrderedScalar) →
  (C : Fourier.ComplexFourierInterface S) →
  (N R : Nat) →
  (sector : PhysicalSector.ExactOutputRetainedSectorLaw N R) →
  {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (H : Gram.FiniteShellInnerProductSpace (Scalar.exactScalarOperations S)) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (pairIncidenceVector : Incidence.PairIncidence → Gram.Vector H) →
  NegativeTransferContrastData {A = Incidence.PairIncidence} H
physicalCutoffNegativeTransferContrastFromFourierData
  S C N R sector H u vector =
  physicalCutoffNegativeTransferContrastData N R sector H
    (PairGram.pairIncidenceNegativeCoefficient u)
    vector

-- The coordinate carrier is indexed by actual membership in the retained
-- cutoff list.  This indexed variant is therefore the canonical physical
-- constructor: its basis-difference vectors have total source/target
-- coordinates on the same deduplicated support.
physicalIndexedCutoffNegativeTransferContrastFromFourierData :
  (S : Scalar.ExactOrderedScalar) →
  (C : Fourier.ComplexFourierInterface S) →
  (N R : Nat) →
  (sector : PhysicalSector.ExactOutputRetainedSectorLaw N R) →
  {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (H : Gram.FiniteShellInnerProductSpace (Scalar.exactScalarOperations S)) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (pairIncidenceVector :
    Support.PhysicalCutoffIncidence N R sector → Gram.Vector H) →
  NegativeTransferContrastData
    {A = Support.PhysicalCutoffIncidence N R sector} H
physicalIndexedCutoffNegativeTransferContrastFromFourierData
  S C N R sector H u vector =
  mkNegativeTransferContrastData
    (Support.physicalCutoffIndexedIncidences N R sector)
    (λ r → PairGram.pairIncidenceNegativeCoefficient u (proj₁ r))
    vector

ShellObservable :
  {S : Exact.ExactScalarOperations} →
  (H : Gram.FiniteShellInnerProductSpace S) → Set
ShellObservable H = Gram.Vector H

edgeContrastTerm :
  {S : Exact.ExactScalarOperations} →
  (H : Gram.FiniteShellInnerProductSpace S) →
  {A : Set} → NegativeTransferContrastData {A = A} H →
  A → ShellObservable H →
  Exact.ExactScalarOperations.Carrier S
edgeContrastTerm {S = S} H assembly r z =
  Exact.ExactScalarOperations._*_ S
    (negativeEdgeCoefficient assembly r)
    (Exact.ExactScalarOperations._*_ S
      (Gram.inner H (pairIncidenceVector assembly r) z)
      (Gram.inner H (pairIncidenceVector assembly r) z))

-- The negative-transfer contrast is the exact finite edge expansion.  In
-- the canonical basis-vector instance each summand is m^-_tau / 3 times
-- (z_source - z_target)^2.
negativeTransferContrast :
  {S : Exact.ExactScalarOperations} →
  {H : Gram.FiniteShellInnerProductSpace S} {A : Set} →
  NegativeTransferContrastData {A = A} H → ShellObservable H →
  Exact.ExactScalarOperations.Carrier S
negativeTransferContrast {S = S} assembly z =
  Exact.weightedListSum {S = S}
    (λ r → edgeContrastTerm _ assembly r z)
    (retainedPairIncidences assembly)

physicalLNeg :
  {S : Exact.ExactScalarOperations} →
  {H : Gram.FiniteShellInnerProductSpace S} {A : Set} →
  NegativeTransferContrastData {A = A} H → ShellObservable H → ShellObservable H
physicalLNeg {H = H} assembly z =
  Gram.rankOneSum H
    (negativeEdgeCoefficient assembly)
    (pairIncidenceVector assembly)
    (retainedPairIncidences assembly) z

-- This is the exact finite-sum proof requested for the auxiliary Gram
-- surrogate.  It is an equality, not merely a domination statement.
negativeTransferContrastGramIdentity :
  {S : Exact.ExactScalarOperations} →
  {H : Gram.FiniteShellInnerProductSpace S} {A : Set} →
  (assembly : NegativeTransferContrastData {A = A} H) →
  (z : ShellObservable H) →
  negativeTransferContrast assembly z ≡ Gram.inner H z (physicalLNeg assembly z)
negativeTransferContrastGramIdentity {H = H} assembly z =
  sym (Gram.rankOneSumQuadraticFormula H
    (negativeEdgeCoefficient assembly)
    (pairIncidenceVector assembly)
    (retainedPairIncidences assembly) z)

------------------------------------------------------------------------
-- PDE-facing bridge, intentionally fail-closed.
--
-- A Fourier reconstruction must provide a triadwise Stage-3 form and prove
-- that its contrast factor Psi_tau(z) is bounded by the three-edge variance.
-- The Gram equality above is already proved; this record is the separate
-- physical theorem that may eventually use it.
------------------------------------------------------------------------

record Stage3BadTransferDomination
    {S : Exact.ExactScalarOperations} {A : Set}
    (H : Gram.FiniteShellInnerProductSpace S)
    (assembly : NegativeTransferContrastData {A = A} H) : Set₁ where
  field
    _≤q_ : Exact.ExactScalarOperations.Carrier S →
           Exact.ExactScalarOperations.Carrier S → Set
    stage3BadTransfer : ShellObservable H → Exact.ExactScalarOperations.Carrier S
    stage3BadTransferDominatedByNegativeGram :
      (z : ShellObservable H) →
      stage3BadTransfer z ≤q negativeTransferContrast assembly z

open Stage3BadTransferDomination public

stage3BadTransferDominationClosed : Bool
stage3BadTransferDominationClosed = false
