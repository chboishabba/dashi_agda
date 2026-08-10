module DASHI.Physics.Closure.NSTriadKNLuoStrainGramCutoffInvariantRound35Validation where

------------------------------------------------------------------------
-- Round Thirty-Five cumulative Navier--Stokes validation root.
--
-- The root imports Round 34 first, then the new concrete mathematics:
-- polarized/cross-fibre strain Gram identities, finite interference
-- decomposition, fixed-cutoff support tangency, exact inverse-square/Leray
-- reality laws, the literal ordered nonlinear reality theorem, the labelled
-- conjugation bijection of physical output fibres, HH-bad shell-budget
-- gluing, the Com Gram reduction with a real six-three overlap candidate,
-- the permutation x reality factorization of the canonical triad action, the
-- vector-field commuting square, and the dual resource/scale no-go ledger.
------------------------------------------------------------------------

import DASHI.Physics.Closure.NSTriadKNLuoFourierStrainHHBadRound34Validation

import DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainGramRound35Exact as StrainGram
import DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainInterferenceRound35Exact as StrainInterference
import DASHI.Physics.Closure.NSTriadKNFixedCutoffSupportInvariantRound35Exact as CutoffInvariant
import DASHI.Physics.Closure.NSTriadKNModeInverseSquareRealityRound35Exact as InverseReality
import DASHI.Physics.Closure.NSTriadKNComplex3RealityLawsRound35Exact as RealityLaws
import DASHI.Physics.Closure.NSTriadKNOrderedInteractionRealityRound35Exact as InteractionReality
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberConjugationRound35Exact as FiberReality
import DASHI.Physics.Closure.NSTriadKNHHBadFiniteShellBudgetGluingRound35Exact as HHBadBudget
import DASHI.Physics.Closure.NSTriadKNComGramInterferenceRound35Exact as ComGram
import DASHI.Physics.Closure.NSTriadKNTriadS3RealityActionRound35Exact as TriadAction
import DASHI.Physics.Closure.NSTriadKNVectorFieldIndexedGluingRound35Exact as VectorGluing
import DASHI.Physics.Closure.NSTriadKNDualResourceScaleLedgerRound35Exact as DualLedger
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as LuoHHBad

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

strainGramRegression :
  StrainGram.periodicFourierStrainGramClosed ≡ true
strainGramRegression =
  StrainGram.periodicFourierStrainGramClosedIsTrue

crossFibreFormulaRegression :
  StrainGram.crossFibreStrainInterferenceFormulaClosed ≡ true
crossFibreFormulaRegression =
  StrainGram.crossFibreStrainInterferenceFormulaClosedIsTrue

physicalHHGoodStillOpenRegression :
  StrainGram.physicalHHGoodCrossFibreEstimateConstructed ≡ false
physicalHHGoodStillOpenRegression =
  StrainGram.physicalHHGoodCrossFibreEstimateConstructedIsFalse

finiteStrainInterferenceRegression :
  StrainInterference.periodicFiniteStrainInterferenceDecompositionClosed ≡ true
finiteStrainInterferenceRegression =
  StrainInterference.periodicFiniteStrainInterferenceDecompositionClosedIsTrue

physicalInterferenceDecayStillOpenRegression :
  StrainInterference.physicalCrossFibreInterferenceDecayConstructed ≡ false
physicalInterferenceDecayStillOpenRegression =
  StrainInterference.physicalCrossFibreInterferenceDecayConstructedIsFalse

fixedCutoffTangencyRegression :
  CutoffInvariant.fixedCutoffSupportTangencyClosed ≡ true
fixedCutoffTangencyRegression =
  CutoffInvariant.fixedCutoffSupportTangencyClosedIsTrue

fixedCutoffCompatibilityStillOpenRegression :
  CutoffInvariant.fixedCutoffSameObjectCompatibilityInvariantConstructed ≡ false
fixedCutoffCompatibilityStillOpenRegression =
  CutoffInvariant.fixedCutoffSameObjectCompatibilityInvariantConstructedIsFalse

inverseSquareRealityRegression :
  InverseReality.modeInverseSquareRealityClosed ≡ true
inverseSquareRealityRegression =
  InverseReality.modeInverseSquareRealityClosedIsTrue

lerayRealityRegression :
  RealityLaws.complex3RealityLawsConstructed ≡ true
lerayRealityRegression =
  RealityLaws.complex3RealityLawsConstructedIsTrue

orderedInteractionRealityRegression :
  InteractionReality.orderedInteractionRealityClosed ≡ true
orderedInteractionRealityRegression =
  InteractionReality.orderedInteractionRealityClosedIsTrue

summedNonlinearityRealityStillOpenRegression :
  InteractionReality.summedProjectedNonlinearityRealityConstructed ≡ false
summedNonlinearityRealityStillOpenRegression =
  InteractionReality.summedProjectedNonlinearityRealityConstructedIsFalse

outputFiberConjugationRegression :
  FiberReality.physicalOutputFiberConjugationBijectionClosed ≡ true
outputFiberConjugationRegression =
  FiberReality.physicalOutputFiberConjugationBijectionClosedIsTrue

outputFiberPermutationStillOpenRegression :
  FiberReality.outputFiberConjugationListPermutationConstructed ≡ false
outputFiberPermutationStillOpenRegression =
  FiberReality.outputFiberConjugationListPermutationConstructedIsFalse

hhBadBudgetGluingRegression :
  HHBadBudget.hhBadFiniteShellBudgetGluingClosed ≡ true
hhBadBudgetGluingRegression =
  HHBadBudget.hhBadFiniteShellBudgetGluingClosedIsTrue

physicalHHBadBudgetStillOpenRegression :
  HHBadBudget.physicalHHBadShellBudgetProduced ≡ false
physicalHHBadBudgetStillOpenRegression =
  HHBadBudget.physicalHHBadShellBudgetProducedIsFalse

comGramReductionRegression :
  ComGram.comGramInterferenceReductionClosed ≡ true
comGramReductionRegression =
  ComGram.comGramInterferenceReductionClosedIsTrue

sixThreeGramCandidateRegression :
  ComGram.sixThreeGramCandidateClosed ≡ true
sixThreeGramCandidateRegression =
  ComGram.sixThreeGramCandidateClosedIsTrue

physicalComGramStillOpenRegression :
  ComGram.physicalComPairProductGramRealizationConstructed ≡ false
physicalComGramStillOpenRegression =
  ComGram.physicalComPairProductGramRealizationConstructedIsFalse

triadActionFactorizationRegression :
  TriadAction.triadPermutationRealityFactorizationClosed ≡ true
triadActionFactorizationRegression =
  TriadAction.triadPermutationRealityFactorizationClosedIsTrue

vectorFieldGluingRegression :
  VectorGluing.vectorFieldIndexedGluingClosed ≡ true
vectorFieldGluingRegression =
  VectorGluing.vectorFieldIndexedGluingClosedIsTrue

physicalBishopSquareStillOpenRegression :
  VectorGluing.physicalBishopVectorFieldIndexedGluingConstructed ≡ false
physicalBishopSquareStillOpenRegression =
  VectorGluing.physicalBishopVectorFieldIndexedGluingConstructedIsFalse

dualLedgerRegression :
  DualLedger.dualResourceScaleLedgerClosed ≡ true
dualLedgerRegression =
  DualLedger.dualResourceScaleLedgerClosedIsTrue

missingInverseScaleNoGoRegression :
  DualLedger.hhBadMissingInverseScaleFailsClosed ≡ true
missingInverseScaleNoGoRegression =
  DualLedger.hhBadMissingInverseScaleFailsClosedIsTrue

-- Round 34 already typed the physical bad gain as a subsection of one
-- localized dissipation cell.  Preserve that exact interface rather than
-- duplicating it under a new name in Round 35.
hhBadDissipationSectionInterface :
  ∀ {eta viscosity shell}
    (cell : LuoHHBad.LuoCriticalDissipationCell eta viscosity shell) → Set
hhBadDissipationSectionInterface cell =
  LuoHHBad.HHBadGainBelowCriticalDissipation cell
