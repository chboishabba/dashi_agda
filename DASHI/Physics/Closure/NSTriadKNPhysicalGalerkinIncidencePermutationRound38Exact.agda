module DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Close a substantially sharper finite F4 theorem than an abstract orbit
-- receipt.  The literal physical cutoff enumeration contains *ordered*
-- convolution incidences.  Round 37 already proved exact three-leg energy
-- cancellation for every incidence using the symmetrised ordered-pair
-- coefficient.  Round 38 proves that all three reindexings needed to compare
-- that packet cancellation with the raw ordered Galerkin incidence fold are
-- exact list permutations:
--
--   tau |-> pEnergyLeg tau,
--   tau |-> qEnergyLeg tau,
--   tau |-> swapTriad tau.
--
-- Therefore, over the complete duplicate-free physical enumeration,
--
--   sum threeLegPower
--     = 3 sum orderedPairPower
--     = 6 sum orderedPower.
--
-- The left side is already zero term by term, so rational cancellation gives
--
--   sum orderedPower = 0.
--
-- This handles stabilizers automatically: no orbit cardinality or free-action
-- assumption is used.  What remains for the full F4 same-object theorem is
-- only the identification of the actual Galerkin convection/energy pairing
-- with this literal ordered physical-incidence fold, including the repository
-- Fourier normalization.  The nonlinear cancellation of that incidence fold
-- itself is closed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base as Int
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
import Data.List.Relation.Unary.Unique.Propositional as Unique
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (Σ; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalSymmetryEnumerationClosure as SymmetryEnumeration
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as KFree
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitFibreRound38Exact as Orbit38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3EnergyCancellation as Energy
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalTriadEnergyRound37Exact as TriadPower

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Exact involutions and injections on proof-bearing physical incidences.
------------------------------------------------------------------------

pEnergyLegInvolutiveExact : ∀ tau →
  Orbit.pEnergyLeg (Orbit.pEnergyLeg tau) ≡ tau
pEnergyLegInvolutiveExact tau =
  KFree.physicalIncidenceExtPQ
    (Orbit.pEnergyLeg (Orbit.pEnergyLeg tau)) tau
    (Symmetry.sameP (Orbit38.pEnergyLegInvolutiveOnLattice tau))
    (Symmetry.sameQ (Orbit38.pEnergyLegInvolutiveOnLattice tau))

qEnergyLegInvolutiveExact : ∀ tau →
  Orbit.qEnergyLeg (Orbit.qEnergyLeg tau) ≡ tau
qEnergyLegInvolutiveExact tau =
  KFree.physicalIncidenceExtPQ
    (Orbit.qEnergyLeg (Orbit.qEnergyLeg tau)) tau
    (Symmetry.sameP (Orbit38.qEnergyLegInvolutiveOnLattice tau))
    (Symmetry.sameQ (Orbit38.qEnergyLegInvolutiveOnLattice tau))

swapTriadInvolutiveExact : ∀ tau →
  Symmetry.swapTriad (Symmetry.swapTriad tau) ≡ tau
swapTriadInvolutiveExact tau =
  KFree.physicalIncidenceExtPQ
    (Symmetry.swapTriad (Symmetry.swapTriad tau)) tau
    (Symmetry.sameP (Symmetry.swapTriadInvolutiveOnLattice tau))
    (Symmetry.sameQ (Symmetry.swapTriadInvolutiveOnLattice tau))

pEnergyLegInjective : ∀ {left right} →
  Orbit.pEnergyLeg left ≡ Orbit.pEnergyLeg right → left ≡ right
pEnergyLegInjective {left} {right} equality =
  trans
    (sym (pEnergyLegInvolutiveExact left))
    (trans
      (cong Orbit.pEnergyLeg equality)
      (pEnergyLegInvolutiveExact right))

qEnergyLegInjective : ∀ {left right} →
  Orbit.qEnergyLeg left ≡ Orbit.qEnergyLeg right → left ≡ right
qEnergyLegInjective {left} {right} equality =
  trans
    (sym (qEnergyLegInvolutiveExact left))
    (trans
      (cong Orbit.qEnergyLeg equality)
      (qEnergyLegInvolutiveExact right))

swapTriadInjective : ∀ {left right} →
  Symmetry.swapTriad left ≡ Symmetry.swapTriad right → left ≡ right
swapTriadInjective {left} {right} equality =
  trans
    (sym (swapTriadInvolutiveExact left))
    (trans
      (cong Symmetry.swapTriad equality)
      (swapTriadInvolutiveExact right))

------------------------------------------------------------------------
-- Exact membership closure, not merely existence of a same-label witness.
------------------------------------------------------------------------

representativeExact :
  ∀ {cutoff tau} →
  (hit : Physical.PhysicalTriadEnumerationHit cutoff tau) →
  Physical.representative hit ≡ tau
representativeExact hit =
  KFree.physicalIncidenceExtPQ
    (Physical.representative hit) _
    (Physical.sameP hit)
    (Physical.sameQ hit)

pEnergyLegMember : ∀ {cutoff tau} →
  tau ∈ Physical.physicalTriadEnumeration cutoff →
  Orbit.pEnergyLeg tau ∈ Physical.physicalTriadEnumeration cutoff
pEnergyLegMember {cutoff} {tau} member =
  let
    bounded =
      Physical.physicalTriadEnumerationCutoffSound
        (KFree.stdMemberToCube member)
    hit =
      Physical.physicalTriadEnumerationComplete
        (Orbit38.pEnergyLegPreservesCutoff bounded)
    exact = representativeExact hit
  in
  KFree.cubeMemberToStd
    (subst
      (λ selected → selected Cube.∈ Physical.physicalTriadEnumeration cutoff)
      exact
      (Physical.representativeListed hit))

qEnergyLegMember : ∀ {cutoff tau} →
  tau ∈ Physical.physicalTriadEnumeration cutoff →
  Orbit.qEnergyLeg tau ∈ Physical.physicalTriadEnumeration cutoff
qEnergyLegMember {cutoff} {tau} member =
  let
    bounded =
      Physical.physicalTriadEnumerationCutoffSound
        (KFree.stdMemberToCube member)
    hit =
      Physical.physicalTriadEnumerationComplete
        (Orbit38.qEnergyLegPreservesCutoff bounded)
    exact = representativeExact hit
  in
  KFree.cubeMemberToStd
    (subst
      (λ selected → selected Cube.∈ Physical.physicalTriadEnumeration cutoff)
      exact
      (Physical.representativeListed hit))

swapTriadMember : ∀ {cutoff tau} →
  tau ∈ Physical.physicalTriadEnumeration cutoff →
  Symmetry.swapTriad tau ∈ Physical.physicalTriadEnumeration cutoff
swapTriadMember {cutoff} {tau} member =
  let
    bounded =
      Physical.physicalTriadEnumerationCutoffSound
        (KFree.stdMemberToCube member)
    hit = SymmetryEnumeration.swapEnumerationClosure bounded
    exact = representativeExact hit
  in
  KFree.cubeMemberToStd
    (subst
      (λ selected → selected Cube.∈ Physical.physicalTriadEnumeration cutoff)
      exact
      (Physical.representativeListed hit))

------------------------------------------------------------------------
-- Map-image membership equivalences and exact list permutations.
------------------------------------------------------------------------

mappedPEnergyLegForward : ∀ {cutoff tau} →
  tau ∈ map Orbit.pEnergyLeg (Physical.physicalTriadEnumeration cutoff) →
  tau ∈ Physical.physicalTriadEnumeration cutoff
mappedPEnergyLegForward member with ∈-map⁻ Orbit.pEnergyLeg member
... | source , sourceMember , sourceMaps =
  subst
    (λ chosen → chosen ∈ Physical.physicalTriadEnumeration _)
    sourceMaps
    (pEnergyLegMember sourceMember)

mappedPEnergyLegBackward : ∀ {cutoff tau} →
  tau ∈ Physical.physicalTriadEnumeration cutoff →
  tau ∈ map Orbit.pEnergyLeg (Physical.physicalTriadEnumeration cutoff)
mappedPEnergyLegBackward {tau = tau} member =
  subst
    (λ chosen → chosen ∈ map Orbit.pEnergyLeg
      (Physical.physicalTriadEnumeration _))
    (pEnergyLegInvolutiveExact tau)
    (∈-map⁺ Orbit.pEnergyLeg (pEnergyLegMember member))

mappedQEnergyLegForward : ∀ {cutoff tau} →
  tau ∈ map Orbit.qEnergyLeg (Physical.physicalTriadEnumeration cutoff) →
  tau ∈ Physical.physicalTriadEnumeration cutoff
mappedQEnergyLegForward member with ∈-map⁻ Orbit.qEnergyLeg member
... | source , sourceMember , sourceMaps =
  subst
    (λ chosen → chosen ∈ Physical.physicalTriadEnumeration _)
    sourceMaps
    (qEnergyLegMember sourceMember)

mappedQEnergyLegBackward : ∀ {cutoff tau} →
  tau ∈ Physical.physicalTriadEnumeration cutoff →
  tau ∈ map Orbit.qEnergyLeg (Physical.physicalTriadEnumeration cutoff)
mappedQEnergyLegBackward {tau = tau} member =
  subst
    (λ chosen → chosen ∈ map Orbit.qEnergyLeg
      (Physical.physicalTriadEnumeration _))
    (qEnergyLegInvolutiveExact tau)
    (∈-map⁺ Orbit.qEnergyLeg (qEnergyLegMember member))

mappedSwapForward : ∀ {cutoff tau} →
  tau ∈ map Symmetry.swapTriad (Physical.physicalTriadEnumeration cutoff) →
  tau ∈ Physical.physicalTriadEnumeration cutoff
mappedSwapForward member with ∈-map⁻ Symmetry.swapTriad member
... | source , sourceMember , sourceMaps =
  subst
    (λ chosen → chosen ∈ Physical.physicalTriadEnumeration _)
    sourceMaps
    (swapTriadMember sourceMember)

mappedSwapBackward : ∀ {cutoff tau} →
  tau ∈ Physical.physicalTriadEnumeration cutoff →
  tau ∈ map Symmetry.swapTriad (Physical.physicalTriadEnumeration cutoff)
mappedSwapBackward {tau = tau} member =
  subst
    (λ chosen → chosen ∈ map Symmetry.swapTriad
      (Physical.physicalTriadEnumeration _))
    (swapTriadInvolutiveExact tau)
    (∈-map⁺ Symmetry.swapTriad (swapTriadMember member))

physicalEnumerationUnique :
  (cutoff : Nat) →
  Unique.Unique (Physical.physicalTriadEnumeration cutoff)
physicalEnumerationUnique cutoff =
  KFree.cubeNoDuplicatesToUnique
    (Physical.physicalTriadEnumerationNoDuplicates cutoff)

pEnergyLegEnumerationPermutation :
  (cutoff : Nat) →
  map Orbit.pEnergyLeg (Physical.physicalTriadEnumeration cutoff)
    Perm.↭ Physical.physicalTriadEnumeration cutoff
pEnergyLegEnumerationPermutation cutoff =
  KFree.uniqueMembershipEquivalenceToPermutation
    (UniqueP.map⁺ pEnergyLegInjective (physicalEnumerationUnique cutoff))
    (physicalEnumerationUnique cutoff)
    mappedPEnergyLegForward
    mappedPEnergyLegBackward

qEnergyLegEnumerationPermutation :
  (cutoff : Nat) →
  map Orbit.qEnergyLeg (Physical.physicalTriadEnumeration cutoff)
    Perm.↭ Physical.physicalTriadEnumeration cutoff
qEnergyLegEnumerationPermutation cutoff =
  KFree.uniqueMembershipEquivalenceToPermutation
    (UniqueP.map⁺ qEnergyLegInjective (physicalEnumerationUnique cutoff))
    (physicalEnumerationUnique cutoff)
    mappedQEnergyLegForward
    mappedQEnergyLegBackward

swapTriadEnumerationPermutation :
  (cutoff : Nat) →
  map Symmetry.swapTriad (Physical.physicalTriadEnumeration cutoff)
    Perm.↭ Physical.physicalTriadEnumeration cutoff
swapTriadEnumerationPermutation cutoff =
  KFree.uniqueMembershipEquivalenceToPermutation
    (UniqueP.map⁺ swapTriadInjective (physicalEnumerationUnique cutoff))
    (physicalEnumerationUnique cutoff)
    mappedSwapForward
    mappedSwapBackward

------------------------------------------------------------------------
-- Rational fold invariance under the proof-relevant permutations.
------------------------------------------------------------------------

foldPower :
  (Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
foldPower value [] = 0ℚ
foldPower value (tau ∷ rest) = value tau + foldPower value rest

foldMap :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  (reindex : Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence) →
  (items : List Physical.PhysicalTriadIncidence) →
  foldPower value (map reindex items)
  ≡ foldPower (λ tau → value (reindex tau)) items
foldMap value reindex [] = refl
foldMap value reindex (tau ∷ rest) =
  cong (value (reindex tau) +_) (foldMap value reindex rest)

foldPermutationInvariant :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  ∀ {left right} → left Perm.↭ right →
  foldPower value left ≡ foldPower value right
foldPermutationInvariant value Perm.refl = refl
foldPermutationInvariant value (Perm.prep x permutation) =
  cong (value x +_) (foldPermutationInvariant value permutation)
foldPermutationInvariant value (Perm.swap x y permutation) =
  trans
    (cong
      (λ tail → value x + (value y + tail))
      (foldPermutationInvariant value permutation))
    (solve
      ( value x
      ∷ value y
      ∷ foldPower value _
      ∷ []))
foldPermutationInvariant value (Perm.trans first second) =
  trans
    (foldPermutationInvariant value first)
    (foldPermutationInvariant value second)

------------------------------------------------------------------------
-- Ordered, ordered-pair and three-leg powers on the exact rational carrier.
------------------------------------------------------------------------

orderedPower :
  C3.IntegerEmbedding F →
  (I : C3.ModeInverseSquare F _) →
  (Physical.PhysicalTriadIncidence) →
  (DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  ℚ
orderedPower E I tau velocity =
  C3.real (Audit.orderedSignedTransferAt E I tau velocity)

orderedPairPower :
  C3.IntegerEmbedding F →
  (I : C3.ModeInverseSquare F _) →
  Physical.PhysicalTriadIncidence →
  (DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  ℚ
orderedPairPower E I tau velocity =
  C3.real (Audit.orderedPairSignedTransferAt E I tau velocity)

orderedPairPowerIsOrderedPlusSwap :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (tau : Physical.PhysicalTriadIncidence) →
  (velocity : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  orderedPairPower E I tau velocity
  ≡ orderedPower E I tau velocity
    + orderedPower E I (Symmetry.swapTriad tau) velocity
orderedPairPowerIsOrderedPlusSwap E I tau velocity =
  cong C3.real
    (Energy.orderedPairCoefficientIsOrderedSum E I tau velocity)

threeLegPowerIsPairOrbitSum :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (tau : Physical.PhysicalTriadIncidence) →
  (velocity : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  TriadPower.literalThreeLegPower E I tau velocity
  ≡ orderedPairPower E I tau velocity
    + orderedPairPower E I (Orbit.pEnergyLeg tau) velocity
    + orderedPairPower E I (Orbit.qEnergyLeg tau) velocity
threeLegPowerIsPairOrbitSum E I tau velocity = refl

orderedFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
orderedFold E I velocity = foldPower (λ tau → orderedPower E I tau velocity)

pairFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
pairFold E I velocity = foldPower (λ tau → orderedPairPower E I tau velocity)

pPairFold qPairFold swapOrderedFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
pPairFold E I velocity =
  foldPower (λ tau → orderedPairPower E I (Orbit.pEnergyLeg tau) velocity)
qPairFold E I velocity =
  foldPower (λ tau → orderedPairPower E I (Orbit.qEnergyLeg tau) velocity)
swapOrderedFold E I velocity =
  foldPower (λ tau → orderedPower E I (Symmetry.swapTriad tau) velocity)

pairFoldPEnergyInvariant :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (velocity : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  pPairFold E I velocity (Physical.physicalTriadEnumeration cutoff)
  ≡ pairFold E I velocity (Physical.physicalTriadEnumeration cutoff)
pairFoldPEnergyInvariant E I velocity cutoff =
  trans
    (sym (foldMap
      (λ tau → orderedPairPower E I tau velocity)
      Orbit.pEnergyLeg
      (Physical.physicalTriadEnumeration cutoff)))
    (foldPermutationInvariant
      (λ tau → orderedPairPower E I tau velocity)
      (pEnergyLegEnumerationPermutation cutoff))

pairFoldQEnergyInvariant :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (velocity : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  qPairFold E I velocity (Physical.physicalTriadEnumeration cutoff)
  ≡ pairFold E I velocity (Physical.physicalTriadEnumeration cutoff)
pairFoldQEnergyInvariant E I velocity cutoff =
  trans
    (sym (foldMap
      (λ tau → orderedPairPower E I tau velocity)
      Orbit.qEnergyLeg
      (Physical.physicalTriadEnumeration cutoff)))
    (foldPermutationInvariant
      (λ tau → orderedPairPower E I tau velocity)
      (qEnergyLegEnumerationPermutation cutoff))

orderedFoldSwapInvariant :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (velocity : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  swapOrderedFold E I velocity (Physical.physicalTriadEnumeration cutoff)
  ≡ orderedFold E I velocity (Physical.physicalTriadEnumeration cutoff)
orderedFoldSwapInvariant E I velocity cutoff =
  trans
    (sym (foldMap
      (λ tau → orderedPower E I tau velocity)
      Symmetry.swapTriad
      (Physical.physicalTriadEnumeration cutoff)))
    (foldPermutationInvariant
      (λ tau → orderedPower E I tau velocity)
      (swapTriadEnumerationPermutation cutoff))

pairFoldDecomposition :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (velocity : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  pairFold E I velocity items
  ≡ orderedFold E I velocity items + swapOrderedFold E I velocity items
pairFoldDecomposition E I velocity [] = solve []
pairFoldDecomposition E I velocity (tau ∷ rest) =
  trans
    (cong
      (_+ pairFold E I velocity rest)
      (orderedPairPowerIsOrderedPlusSwap E I tau velocity))
    (trans
      (cong
        (λ tail →
          (orderedPower E I tau velocity
            + orderedPower E I (Symmetry.swapTriad tau) velocity)
          + tail)
        (pairFoldDecomposition E I velocity rest))
      (solve
        ( orderedPower E I tau velocity
        ∷ orderedPower E I (Symmetry.swapTriad tau) velocity
        ∷ orderedFold E I velocity rest
        ∷ swapOrderedFold E I velocity rest
        ∷ [])))

pairFoldIsDoubleOrderedOnEnumeration :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (velocity : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  pairFold E I velocity (Physical.physicalTriadEnumeration cutoff)
  ≡ orderedFold E I velocity (Physical.physicalTriadEnumeration cutoff)
    + orderedFold E I velocity (Physical.physicalTriadEnumeration cutoff)
pairFoldIsDoubleOrderedOnEnumeration E I velocity cutoff =
  trans
    (pairFoldDecomposition E I velocity
      (Physical.physicalTriadEnumeration cutoff))
    (cong
      (orderedFold E I velocity (Physical.physicalTriadEnumeration cutoff) +_)
      (orderedFoldSwapInvariant E I velocity cutoff))

threeLegFoldDecomposition :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (velocity : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  TriadPower.sumLiteralTriadPower E I velocity items
  ≡ pairFold E I velocity items
    + pPairFold E I velocity items
    + qPairFold E I velocity items
threeLegFoldDecomposition E I velocity [] = solve []
threeLegFoldDecomposition E I velocity (tau ∷ rest) =
  trans
    (cong
      (_+ TriadPower.sumLiteralTriadPower E I velocity rest)
      (threeLegPowerIsPairOrbitSum E I tau velocity))
    (trans
      (cong
        (λ tail →
          (orderedPairPower E I tau velocity
            + orderedPairPower E I (Orbit.pEnergyLeg tau) velocity
            + orderedPairPower E I (Orbit.qEnergyLeg tau) velocity)
          + tail)
        (threeLegFoldDecomposition E I velocity rest))
      (solve
        ( orderedPairPower E I tau velocity
        ∷ orderedPairPower E I (Orbit.pEnergyLeg tau) velocity
        ∷ orderedPairPower E I (Orbit.qEnergyLeg tau) velocity
        ∷ pairFold E I velocity rest
        ∷ pPairFold E I velocity rest
        ∷ qPairFold E I velocity rest
        ∷ [])))

sixFold : ℚ → ℚ
sixFold value = value + value + value + value + value + value

literalThreeLegFoldIsSixOrderedFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (velocity : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  TriadPower.sumLiteralTriadPower E I velocity
    (Physical.physicalTriadEnumeration cutoff)
  ≡ sixFold
      (orderedFold E I velocity (Physical.physicalTriadEnumeration cutoff))
literalThreeLegFoldIsSixOrderedFold E I velocity cutoff =
  let
    enumeration = Physical.physicalTriadEnumeration cutoff
    pairTotal = pairFold E I velocity enumeration
    orderedTotal = orderedFold E I velocity enumeration

    decomposition :
      TriadPower.sumLiteralTriadPower E I velocity enumeration
      ≡ pairTotal
        + pPairFold E I velocity enumeration
        + qPairFold E I velocity enumeration
    decomposition = threeLegFoldDecomposition E I velocity enumeration

    allPairTotals :
      pairTotal
        + pPairFold E I velocity enumeration
        + qPairFold E I velocity enumeration
      ≡ pairTotal + pairTotal + pairTotal
    allPairTotals =
      cong
        (λ pairP → pairTotal + pairP
          + qPairFold E I velocity enumeration)
        (pairFoldPEnergyInvariant E I velocity cutoff)
      `transLocal`
      cong
        (λ pairQ → pairTotal + pairTotal + pairQ)
        (pairFoldQEnergyInvariant E I velocity cutoff)
      where
      infixr 2 _`transLocal`_
      _`transLocal`_ = trans

    pairTwice : pairTotal ≡ orderedTotal + orderedTotal
    pairTwice = pairFoldIsDoubleOrderedOnEnumeration E I velocity cutoff
  in
  trans decomposition
    (trans allPairTotals
      (trans
        (cong
          (λ selectedPair → selectedPair + selectedPair + selectedPair)
          pairTwice)
        (solve (orderedTotal ∷ []))))

oneSixth : ℚ
oneSixth = Int.+ 1 / 6

sixFoldZeroForcesZero : ∀ value →
  sixFold value ≡ 0ℚ → value ≡ 0ℚ
sixFoldZeroForcesZero value sixZero =
  let
    scaled = cong (oneSixth *_) sixZero
    leftMeaning : oneSixth * sixFold value ≡ value
    leftMeaning = solve (value ∷ [])
    rightMeaning : oneSixth * 0ℚ ≡ 0ℚ
    rightMeaning = solve []
  in
  trans (sym leftMeaning) (trans scaled rightMeaning)

literalOrderedGalerkinIncidencePowerZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (cutoff : Nat) →
  (velocity : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  orderedFold E I velocity (Physical.physicalTriadEnumeration cutoff)
  ≡ 0ℚ
literalOrderedGalerkinIncidencePowerZero
    E I cutoff velocity reality divergenceFree =
  sixFoldZeroForcesZero
    (orderedFold E I velocity (Physical.physicalTriadEnumeration cutoff))
    (trans
      (sym (literalThreeLegFoldIsSixOrderedFold E I velocity cutoff))
      (TriadPower.literalCutoffTriadPowerSumZero
        E I cutoff velocity reality divergenceFree))

physicalGalerkinIncidencePermutationCancellationClosed : Bool
physicalGalerkinIncidencePermutationCancellationClosed = true

literalConvectionPairingEqualsOrderedIncidenceFoldConstructed : Bool
literalConvectionPairingEqualsOrderedIncidenceFoldConstructed = false

physicalGalerkinIncidencePermutationCancellationClosedIsTrue :
  physicalGalerkinIncidencePermutationCancellationClosed ≡ true
physicalGalerkinIncidencePermutationCancellationClosedIsTrue = refl
