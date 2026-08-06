module DASHI.Mathematics.CrossPollination.MillenniumProblemStructuralRelevanceGateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang--Mills Theory", Clay Mathematics Institute problem
-- description.  No DOI assigned.
--
-- Charles L. Fefferman,
-- "Existence and Smoothness of the Navier--Stokes Equation", Clay
-- Mathematics Institute problem description.  No DOI assigned.
--
-- Pierre Deligne,
-- "The Hodge Conjecture", Clay Mathematics Institute problem description.
-- No DOI assigned.
--
-- Andrew Wiles,
-- "The Birch and Swinnerton-Dyer Conjecture", Clay Mathematics Institute
-- problem description.  No DOI assigned.
--
-- Enrico Bombieri,
-- "Problems of the Millennium: The Riemann Hypothesis", Clay Mathematics
-- Institute problem description.  No DOI assigned.
--
-- Stephen Cook,
-- "The P versus NP Problem", Clay Mathematics Institute problem description.
-- No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Encode a finite relevance table for the structural threads implemented in
-- this tranche.  The table distinguishes direct foundational infrastructure,
-- indirect/example-level relevance and absence of a claimed route.  It also
-- prevents the frequent name collision between Frobenius's theorem on real
-- associative division algebras and arithmetic/geometric Frobenius maps.
--
-- This table is an audit and dependency classifier.  It proves no Millennium
-- problem and does not infer an analytic, arithmetic or complexity estimate
-- from the presence of shared algebraic language.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

data MillenniumProblem : Set where
  yangMillsMassGap : MillenniumProblem
  navierStokesRegularity : MillenniumProblem
  hodgeConjecture : MillenniumProblem
  birchSwinnertonDyer : MillenniumProblem
  riemannHypothesis : MillenniumProblem
  pVersusNP : MillenniumProblem
  poincareConjectureHistorical : MillenniumProblem

data StructuralThread : Set where
  cayleyDicksonCompositionAlgebra : StructuralThread
  realDivisionAlgebraClassification : StructuralThread
  kleinGroupActionInvariants : StructuralThread
  noetherVariationalConservation : StructuralThread
  noetherianFiniteGeneration : StructuralThread
  hopfFibrationAndLinking : StructuralThread
  arithmeticFrobenius : StructuralThread
  criticalPdeScaling : StructuralThread
  reflectionPositiveSpectralGap : StructuralThread
  algebraicCycleCohomology : StructuralThread
  orbitClosureComplexity : StructuralThread

data RelevanceLevel : Set where
  foundational directSpecialCase indirect absent : RelevanceLevel

relevance : MillenniumProblem → StructuralThread → RelevanceLevel
relevance yangMillsMassGap cayleyDicksonCompositionAlgebra = directSpecialCase
relevance yangMillsMassGap realDivisionAlgebraClassification = indirect
relevance yangMillsMassGap kleinGroupActionInvariants = foundational
relevance yangMillsMassGap noetherVariationalConservation = foundational
relevance yangMillsMassGap noetherianFiniteGeneration = indirect
relevance yangMillsMassGap hopfFibrationAndLinking = directSpecialCase
relevance yangMillsMassGap arithmeticFrobenius = absent
relevance yangMillsMassGap criticalPdeScaling = indirect
relevance yangMillsMassGap reflectionPositiveSpectralGap = foundational
relevance yangMillsMassGap algebraicCycleCohomology = indirect
relevance yangMillsMassGap orbitClosureComplexity = absent

relevance navierStokesRegularity cayleyDicksonCompositionAlgebra = indirect
relevance navierStokesRegularity realDivisionAlgebraClassification = indirect
relevance navierStokesRegularity kleinGroupActionInvariants = foundational
relevance navierStokesRegularity noetherVariationalConservation = directSpecialCase
relevance navierStokesRegularity noetherianFiniteGeneration = absent
relevance navierStokesRegularity hopfFibrationAndLinking = directSpecialCase
relevance navierStokesRegularity arithmeticFrobenius = absent
relevance navierStokesRegularity criticalPdeScaling = foundational
relevance navierStokesRegularity reflectionPositiveSpectralGap = absent
relevance navierStokesRegularity algebraicCycleCohomology = absent
relevance navierStokesRegularity orbitClosureComplexity = absent

relevance hodgeConjecture cayleyDicksonCompositionAlgebra = indirect
relevance hodgeConjecture realDivisionAlgebraClassification = indirect
relevance hodgeConjecture kleinGroupActionInvariants = directSpecialCase
relevance hodgeConjecture noetherVariationalConservation = absent
relevance hodgeConjecture noetherianFiniteGeneration = foundational
relevance hodgeConjecture hopfFibrationAndLinking = indirect
relevance hodgeConjecture arithmeticFrobenius = directSpecialCase
relevance hodgeConjecture criticalPdeScaling = absent
relevance hodgeConjecture reflectionPositiveSpectralGap = absent
relevance hodgeConjecture algebraicCycleCohomology = foundational
relevance hodgeConjecture orbitClosureComplexity = indirect

relevance birchSwinnertonDyer cayleyDicksonCompositionAlgebra = indirect
relevance birchSwinnertonDyer realDivisionAlgebraClassification = indirect
relevance birchSwinnertonDyer kleinGroupActionInvariants = directSpecialCase
relevance birchSwinnertonDyer noetherVariationalConservation = absent
relevance birchSwinnertonDyer noetherianFiniteGeneration = foundational
relevance birchSwinnertonDyer hopfFibrationAndLinking = indirect
relevance birchSwinnertonDyer arithmeticFrobenius = foundational
relevance birchSwinnertonDyer criticalPdeScaling = absent
relevance birchSwinnertonDyer reflectionPositiveSpectralGap = absent
relevance birchSwinnertonDyer algebraicCycleCohomology = directSpecialCase
relevance birchSwinnertonDyer orbitClosureComplexity = indirect

relevance riemannHypothesis cayleyDicksonCompositionAlgebra = absent
relevance riemannHypothesis realDivisionAlgebraClassification = absent
relevance riemannHypothesis kleinGroupActionInvariants = indirect
relevance riemannHypothesis noetherVariationalConservation = indirect
relevance riemannHypothesis noetherianFiniteGeneration = indirect
relevance riemannHypothesis hopfFibrationAndLinking = indirect
relevance riemannHypothesis arithmeticFrobenius = directSpecialCase
relevance riemannHypothesis criticalPdeScaling = absent
relevance riemannHypothesis reflectionPositiveSpectralGap = directSpecialCase
relevance riemannHypothesis algebraicCycleCohomology = indirect
relevance riemannHypothesis orbitClosureComplexity = indirect

relevance pVersusNP cayleyDicksonCompositionAlgebra = absent
relevance pVersusNP realDivisionAlgebraClassification = absent
relevance pVersusNP kleinGroupActionInvariants = directSpecialCase
relevance pVersusNP noetherVariationalConservation = absent
relevance pVersusNP noetherianFiniteGeneration = directSpecialCase
relevance pVersusNP hopfFibrationAndLinking = absent
relevance pVersusNP arithmeticFrobenius = indirect
relevance pVersusNP criticalPdeScaling = absent
relevance pVersusNP reflectionPositiveSpectralGap = absent
relevance pVersusNP algebraicCycleCohomology = indirect
relevance pVersusNP orbitClosureComplexity = foundational

relevance poincareConjectureHistorical cayleyDicksonCompositionAlgebra = directSpecialCase
relevance poincareConjectureHistorical realDivisionAlgebraClassification = indirect
relevance poincareConjectureHistorical kleinGroupActionInvariants = foundational
relevance poincareConjectureHistorical noetherVariationalConservation = indirect
relevance poincareConjectureHistorical noetherianFiniteGeneration = absent
relevance poincareConjectureHistorical hopfFibrationAndLinking = foundational
relevance poincareConjectureHistorical arithmeticFrobenius = absent
relevance poincareConjectureHistorical criticalPdeScaling = directSpecialCase
relevance poincareConjectureHistorical reflectionPositiveSpectralGap = absent
relevance poincareConjectureHistorical algebraicCycleCohomology = indirect
relevance poincareConjectureHistorical orbitClosureComplexity = absent

data FrobeniusMeaning : Set where
  frobeniusRealDivisionTheorem : FrobeniusMeaning
  frobeniusArithmeticEndomorphism : FrobeniusMeaning

frobeniusMeaningsAreDistinct :
  frobeniusRealDivisionTheorem ≡ frobeniusArithmeticEndomorphism → ⊥
frobeniusMeaningsAreDistinct ()

yangMillsSymmetryAndGapAreBothFoundational :
  relevance yangMillsMassGap kleinGroupActionInvariants ≡ foundational
  × relevance yangMillsMassGap reflectionPositiveSpectralGap ≡ foundational
yangMillsSymmetryAndGapAreBothFoundational = refl , refl

navierStokesScalingIsFoundationalButCompositionIsIndirect :
  relevance navierStokesRegularity criticalPdeScaling ≡ foundational
  × relevance navierStokesRegularity cayleyDicksonCompositionAlgebra ≡ indirect
navierStokesScalingIsFoundationalButCompositionIsIndirect = refl , refl

bsdUsesArithmeticNotRealDivisionFrobenius :
  relevance birchSwinnertonDyer arithmeticFrobenius ≡ foundational
  × relevance birchSwinnertonDyer realDivisionAlgebraClassification ≡ indirect
bsdUsesArithmeticNotRealDivisionFrobenius = refl , refl

pVsNPOrbitClosureThreadIsFoundational :
  relevance pVersusNP orbitClosureComplexity ≡ foundational
pVsNPOrbitClosureThreadIsFoundational = refl
