module DASHI.Physics.Closure.NSTriadKNF4GlobalOutputFiberPartitionRound39Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Close the remaining finite F4 combinatorics on the literal physical cutoff.
-- Every enumerated triad has exactly one output k in `Cube.cutoffModes N`.
-- The output fibres are individually duplicate-free and fibres at distinct
-- outputs are disjoint. Therefore concatenating all literal output fibres is
-- an exact K-free permutation of the complete physical triad enumeration.
--
-- Combining that permutation with Round 39's per-output same-object theorem
-- gives
--
--   sum_{k in cutoffModes N} Re<u_k, P_NL_k>
--     = sum_{tau in physicalTriadEnumeration N} OrderedPower(tau)
--     = 0
--
-- under the existing reality and divergence-free conditions.
--
-- This closes the finite nonlinear energy-cancellation theorem on the actual
-- projected Galerkin coefficient. The canonical literal cutoff list is used
-- directly, so no opaque system mode-list equality is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberConjugationRound35Exact as Fibre
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as KFree
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Equation
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as Round38
import DASHI.Physics.Closure.NSTriadKNF4ProjectedOutputPairingRound39Exact as OutputPairing

F : C3.RealField _
F = Rational.rationalRealField

concatOutputFibers :
  Nat → List Z3.FourierMode → List Physical.PhysicalTriadIncidence
concatOutputFibers cutoff [] = []
concatOutputFibers cutoff (output ∷ rest) =
  Cube._++_
    (Output.physicalOutputFiber cutoff output)
    (concatOutputFibers cutoff rest)

concatFiberMemberOriginal :
  ∀ {cutoff outputs tau} →
  tau Cube.∈ concatOutputFibers cutoff outputs →
  tau Cube.∈ Physical.physicalTriadEnumeration cutoff
concatFiberMemberOriginal {outputs = []} ()
concatFiberMemberOriginal {cutoff} {output ∷ rest} member
  with Cube.memberAppendCases member
... | inj₁ inHead = Fibre.filterOutputMemberOriginal inHead
... | inj₂ inRest = concatFiberMemberOriginal inRest

concatFiberMemberOutputListed :
  ∀ {cutoff outputs tau} →
  tau Cube.∈ concatOutputFibers cutoff outputs →
  Physical.k tau Cube.∈ outputs
concatFiberMemberOutputListed {outputs = []} ()
concatFiberMemberOutputListed {cutoff} {output ∷ rest} member
  with Cube.memberAppendCases member
... | inj₁ inHead =
  Cube.here (Output.physicalOutputFiberSound inHead)
... | inj₂ inRest =
  Cube.there (concatFiberMemberOutputListed inRest)

outputMemberGivesConcatFiberMember :
  ∀ {cutoff outputs tau} →
  tau Cube.∈ Physical.physicalTriadEnumeration cutoff →
  Physical.k tau Cube.∈ outputs →
  tau Cube.∈ concatOutputFibers cutoff outputs
outputMemberGivesConcatFiberMember {outputs = []} listed ()
outputMemberGivesConcatFiberMember {cutoff} {output ∷ rest} listed outputMember
  with outputMember
... | Cube.here outputEqual =
  Cube.memberAppendLeft
    (Output.physicalOutputFiberComplete listed outputEqual)
... | Cube.there tail =
  Cube.memberAppendRight
    (outputMemberGivesConcatFiberMember listed tail)

allPhysicalTriadsAppearInLiteralOutputPartition :
  ∀ {cutoff tau} →
  tau Cube.∈ Physical.physicalTriadEnumeration cutoff →
  tau Cube.∈ concatOutputFibers cutoff (Cube.cutoffModes cutoff)
allPhysicalTriadsAppearInLiteralOutputPartition {cutoff} {tau} listed =
  outputMemberGivesConcatFiberMember listed
    (Physical.kBounded (Physical.physicalTriadEnumerationCutoffSound listed))

concatOutputFibersNoDuplicates :
  ∀ cutoff outputs →
  Cube.NoDuplicates outputs →
  Cube.NoDuplicates (concatOutputFibers cutoff outputs)
concatOutputFibersNoDuplicates cutoff [] Cube.unique[] = Cube.unique[]
concatOutputFibersNoDuplicates cutoff (output ∷ rest)
    (Cube.unique∷ outputFresh restUnique) =
  Cube.noDuplicatesAppend
    (KFree.filterOutputNoDuplicates output
      (Physical.physicalTriadEnumeration cutoff)
      (Physical.physicalTriadEnumerationNoDuplicates cutoff))
    (concatOutputFibersNoDuplicates cutoff rest restUnique)
    disjoint
  where
  disjoint :
    Cube.Disjoint
      (Output.physicalOutputFiber cutoff output)
      (concatOutputFibers cutoff rest)
  disjoint {tau} leftMember rightMember =
    let
      leftOutput : Physical.k tau ≡ output
      leftOutput = Output.physicalOutputFiberSound leftMember

      rightOutputMember : Physical.k tau Cube.∈ rest
      rightOutputMember = concatFiberMemberOutputListed rightMember

      outputInRest : output Cube.∈ rest
      outputInRest =
        subst (λ selected → selected Cube.∈ rest)
          leftOutput rightOutputMember
    in
    outputFresh outputInRest

literalOutputPartitionNoDuplicates : ∀ cutoff →
  Cube.NoDuplicates
    (concatOutputFibers cutoff (Cube.cutoffModes cutoff))
literalOutputPartitionNoDuplicates cutoff =
  concatOutputFibersNoDuplicates cutoff (Cube.cutoffModes cutoff)
    (Cube.cutoffModeEnumerationNoDuplicates cutoff)

literalOutputPartitionPermutation :
  (cutoff : Nat) →
  concatOutputFibers cutoff (Cube.cutoffModes cutoff)
    Perm.↭ Physical.physicalTriadEnumeration cutoff
literalOutputPartitionPermutation cutoff =
  KFree.uniqueMembershipEquivalenceToPermutation
    (KFree.cubeNoDuplicatesToUnique
      (literalOutputPartitionNoDuplicates cutoff))
    (Round38.physicalEnumerationUnique cutoff)
    (λ member →
      KFree.cubeMemberToStd
        (concatFiberMemberOriginal (KFree.stdMemberToCube member)))
    (λ member →
      KFree.cubeMemberToStd
        (allPhysicalTriadsAppearInLiteralOutputPartition
          (KFree.stdMemberToCube member)))

foldAppend :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  ∀ left right →
  Round38.foldPower value (Cube._++_ left right)
  ≡ Round38.foldPower value left + Round38.foldPower value right
foldAppend value [] right = refl
foldAppend value (tau ∷ rest) right =
  trans
    (cong (value tau +_) (foldAppend value rest right))
    (solve
      (value tau ∷ Round38.foldPower value rest ∷ Round38.foldPower value right ∷ []))

sumProjectedPairings :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  List Z3.FourierMode → ℚ
sumProjectedPairings system [] = 0ℚ
sumProjectedPairings system (output ∷ rest) =
  OutputPairing.realHermitianPower
    (Equation.velocity system output)
    (Equation.projectedNonlinearity system output)
  + sumProjectedPairings system rest

literalCutoffProjectedEnergyPairing :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I → ℚ
literalCutoffProjectedEnergyPairing system =
  sumProjectedPairings system (Cube.cutoffModes (Equation.cutoff system))

sumProjectedPairingsEqualsConcatFiberFold :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (outputs : List Z3.FourierMode) →
  sumProjectedPairings system outputs
  ≡ Round38.foldPower
      (λ tau → Round38.orderedPower E I tau (Equation.velocity system))
      (concatOutputFibers (Equation.cutoff system) outputs)
sumProjectedPairingsEqualsConcatFiberFold system [] = refl
sumProjectedPairingsEqualsConcatFiberFold {E} {I} system (output ∷ rest) =
  let
    value = λ tau → Round38.orderedPower E I tau (Equation.velocity system)
    headMeaning = OutputPairing.projectedOutputEnergyPairingEqualsOrderedFiberFold
      system output
    tailMeaning = sumProjectedPairingsEqualsConcatFiberFold system rest
  in
  trans
    (cong₂ _+_ headMeaning tailMeaning)
    (sym
      (foldAppend value
        (Output.physicalOutputFiber (Equation.cutoff system) output)
        (concatOutputFibers (Equation.cutoff system) rest)))

literalConvectionPairingEqualsOrderedIncidenceFold :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  literalCutoffProjectedEnergyPairing system
  ≡ Round38.orderedFold E I (Equation.velocity system)
      (Physical.physicalTriadEnumeration (Equation.cutoff system))
literalConvectionPairingEqualsOrderedIncidenceFold {E} {I} system =
  trans
    (sumProjectedPairingsEqualsConcatFiberFold
      system (Cube.cutoffModes (Equation.cutoff system)))
    (Round38.foldPermutationInvariant
      (λ tau → Round38.orderedPower E I tau (Equation.velocity system))
      (literalOutputPartitionPermutation (Equation.cutoff system)))

literalProjectedGalerkinConvectionEnergyZero :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  Audit.RealityCondition (Equation.velocity system) →
  Audit.DivergenceFreeCondition E (Equation.velocity system) →
  literalCutoffProjectedEnergyPairing system ≡ 0ℚ
literalProjectedGalerkinConvectionEnergyZero {E} {I}
    system reality divergenceFree =
  trans
    (literalConvectionPairingEqualsOrderedIncidenceFold system)
    (Round38.literalOrderedGalerkinIncidencePowerZero
      E I (Equation.cutoff system) (Equation.velocity system)
      reality divergenceFree)

f4GlobalOutputFiberPartitionClosed : Bool
f4GlobalOutputFiberPartitionClosed = true

literalConvectionPairingEqualsOrderedIncidenceFoldConstructed : Bool
literalConvectionPairingEqualsOrderedIncidenceFoldConstructed = true

f4GlobalOutputFiberPartitionClosedIsTrue :
  f4GlobalOutputFiberPartitionClosed ≡ true
f4GlobalOutputFiberPartitionClosedIsTrue = refl

literalConvectionPairingEqualsOrderedIncidenceFoldConstructedIsTrue :
  literalConvectionPairingEqualsOrderedIncidenceFoldConstructed ≡ true
literalConvectionPairingEqualsOrderedIncidenceFoldConstructedIsTrue = refl
