module DASHI.Moonshine.Monster3BZeroZetaSquaredC3SeparationExact where

------------------------------------------------------------------------
-- Zero / phase0 / zeta / zetaSquared: EXISTING OWNER CROSSWALK.
--
-- Existing source-proof owners (no copied finite Fourier or cyclotomic algebra):
--   Algebra.TriadicDepthOneCharacters: phase0 = root-of-unity 1,
--     phase1 = zeta, phase2 = zetaSquared.
--   Moonshine.C3CyclotomicAmplitudeAlgebraExact: 1 + zeta + zeta² = 0.
--   Moonshine.MonsterC3CyclotomicEvaluationExact: Monster 3B C3 dimensions,
--     source-valued residual 53 and regular-cycle cancellation.
--   Moonshine.Monster3BBalancedRegularFibreExact: distinction between
--     balanced evaluation zero, empty representation and neutral invariant.
--   Cognition.PhaseEnrichedTrit: a visible neutral trit can conceal distinct
--     internal cyclic phases. No quantum/physical mechanism is inferred.
--   Core.ZeroValueFibreNontrivialityExact: no factoring hidden future
--     behaviours through the observed-zero quotient.
--   Moonshine.Monster3BZetaSuzukiDiagonalNormCutsetExact:
--     four conditional 12+78 central fingerprints and quotient-phase gate.
--
-- New theorem-boundary: the ZERO trivial-character multiplicity in ALL FOUR
-- 90-dimensional candidates is not a ZERO phase eigenvalue and not a ZERO
-- generator trace. Contrasted with 65610 copies of the nonempty balanced
-- REGULAR C3 representation, whose nonidentity trace vanishes.
--
-- Original mathematics: J.-P. Serre (1977), A. Terras (1999);
-- Monster 3B: Barraclough and Wilson (2007).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Algebra.TriadicDepthOneCharacters as Phase
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as Cyclo
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as LA
import DASHI.Moonshine.MonsterC3CyclotomicEvaluationExact as Eval
import DASHI.Moonshine.Monster3BBalancedRegularFibreExact as Regular
import DASHI.Cognition.PhaseEnrichedTrit as Hidden
import DASHI.Core.ZeroValueFibreNontrivialityExact as ZeroFibre
import DASHI.Moonshine.Monster3BZetaSuzukiDiagonalNormCutsetExact as Diagonal

characterPhaseToCyclotomic :
  Phase.C3Phase → Cyclo.Cyclotomic3
characterPhaseToCyclotomic Phase.phase0 = Cyclo.one
characterPhaseToCyclotomic Phase.phase1 = Cyclo.zeta
characterPhaseToCyclotomic Phase.phase2 = Cyclo.zetaSquared

phaseExponentZeroIsUnity :
  characterPhaseToCyclotomic Phase.phase0 ≡ Cyclo.one
phaseExponentZeroIsUnity = refl

phaseOneIsZeta :
  characterPhaseToCyclotomic Phase.phase1 ≡ Cyclo.zeta
phaseOneIsZeta = refl

phaseTwoIsZetaSquared :
  characterPhaseToCyclotomic Phase.phase2 ≡ Cyclo.zetaSquared
phaseTwoIsZetaSquared = refl

-- Do not confuse the scalar zero (not a phase) with the exponent-zero
-- C3 character (its VALUE is one). The tagged sum is the type-safe seam.
data ZeroOrRootOfUnity : Set where
  scalarZero : ZeroOrRootOfUnity
  nonzeroPhase : Phase.C3Phase → ZeroOrRootOfUnity

exponentZeroCannotBeScalarZero :
  nonzeroPhase Phase.phase0 ≡ scalarZero → ⊥
exponentZeroCannotBeScalarZero ()

zetaCannotBeScalarZero :
  nonzeroPhase Phase.phase1 ≡ scalarZero → ⊥
zetaCannotBeScalarZero ()

zetaSquaredCannotBeScalarZero :
  nonzeroPhase Phase.phase2 ≡ scalarZero → ⊥
zetaSquaredCannotBeScalarZero ()

-- Existing finite algebraic cancellation, not a declaration of no states.
nonemptyThreePhaseCycleHasZeroEvaluation :
  LA.add Cyclo.one (LA.add Cyclo.zeta Cyclo.zetaSquared)
    ≡ Cyclo.zero
nonemptyThreePhaseCycleHasZeroEvaluation = LA.zetaSumZero

-- The hidden-phase trit example exhibits two different phases over the SAME
-- visible neutral observation. These are NOT Monster phase projectors.
firstHiddenNeutralIsZero =
  Hidden.balancedOppositionObservesZero

secondHiddenNeutralIsZero =
  Hidden.phaseShiftedBalancedObservesZero

hiddenPhasesOverOneZeroRemainDistinct :
  Hidden.phase Hidden.balancedOpposition
  ≡ Hidden.phase Hidden.phaseShiftedBalancedOpposition → ⊥
hiddenPhasesOverOneZeroRemainDistinct ()

------------------------------------------------------------------------
-- Four source-CANDIDATE (not actual-selected) 12+78 eigenspace triples.
-- Coordinates are multiplicities of (root1, zeta, zetaSquared).
------------------------------------------------------------------------

record PhaseMultiplicityTriple : Set where
  constructor phaseMultiplicityTriple
  field
    rootOneMultiplicity : Nat
    rootZetaMultiplicity : Nat
    rootZetaSquaredMultiplicity : Nat
open PhaseMultiplicityTriple public

data SuzukiNinetyCandidate : Set where
  directZeta dualZeta directZetaSquared dualZetaSquared :
    SuzukiNinetyCandidate

candidatePhaseTriple : SuzukiNinetyCandidate → PhaseMultiplicityTriple
candidatePhaseTriple directZeta = phaseMultiplicityTriple 0 12 78
candidatePhaseTriple dualZeta = phaseMultiplicityTriple 0 90 0
candidatePhaseTriple directZetaSquared = phaseMultiplicityTriple 0 78 12
candidatePhaseTriple dualZetaSquared = phaseMultiplicityTriple 0 0 90

allFourTrivialCharacterMultiplicitiesVanish :
  (candidate : SuzukiNinetyCandidate) →
  rootOneMultiplicity (candidatePhaseTriple candidate) ≡ 0
allFourTrivialCharacterMultiplicitiesVanish directZeta = refl
allFourTrivialCharacterMultiplicitiesVanish dualZeta = refl
allFourTrivialCharacterMultiplicitiesVanish directZetaSquared = refl
allFourTrivialCharacterMultiplicitiesVanish dualZetaSquared = refl

allFourPhaseDimensionsAreNinety :
  (candidate : SuzukiNinetyCandidate) →
  rootOneMultiplicity (candidatePhaseTriple candidate)
  + rootZetaMultiplicity (candidatePhaseTriple candidate)
  + rootZetaSquaredMultiplicity (candidatePhaseTriple candidate)
  ≡ 90
allFourPhaseDimensionsAreNinety directZeta = refl
allFourPhaseDimensionsAreNinety dualZeta = refl
allFourPhaseDimensionsAreNinety directZetaSquared = refl
allFourPhaseDimensionsAreNinety dualZetaSquared = refl

-- Distinguish zero fixed-phase multiplicity from an empty 90-space.
candidateZeroFixedStillHasNinetyDimensions :
  (candidate : SuzukiNinetyCandidate) →
  (rootOneMultiplicity (candidatePhaseTriple candidate) ≡ 0)
  × (rootOneMultiplicity (candidatePhaseTriple candidate)
      + rootZetaMultiplicity (candidatePhaseTriple candidate)
      + rootZetaSquaredMultiplicity (candidatePhaseTriple candidate)
      ≡ 90)
candidateZeroFixedStillHasNinetyDimensions candidate =
  allFourTrivialCharacterMultiplicitiesVanish candidate ,
  allFourPhaseDimensionsAreNinety candidate

-- The full Monster 3B W is instead REGULAR+53 and has all three
-- eigenspaces nonempty. The 196830 balanced part evaluates to zero
-- at nonidentity central elements, without being an empty module.
monsterFixedPhaseIs65663 =
  Regular.monster3BFixedMultiplicityIs65663

monsterZetaPhaseIs65610 =
  Regular.monster3BZetaMultiplicityIs65610

monsterZetaSquaredPhaseIs65610 =
  Regular.monster3BZetaSquaredMultiplicityIs65610

monsterRegularBulkDimension : 3 * 65610 ≡ 196830
monsterRegularBulkDimension = refl

monsterGeneratorCharacterSurvivesAs53 =
  Eval.monster3BGeneratorEvaluation

-- The central quotiented 90-module vs W regular-bulk observations require
-- distinct uses of 'zero'; no same-object Monster action is identified here.
-- In particular a trit-neutral zero is not a Riemann-zeta zero, and a
-- trace-zero projective character is not an absence of quantum states.
