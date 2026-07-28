module DASHI.Physics.YangMills.BalabanClayT4WardBoxCertificateClosureExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Evaluator
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Canonical Ward normal form plus generated 240-box certificate family.
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
--
-- L. D. Faddeev and V. N. Popov, "Feynman Diagrams for the Yang-Mills Field",
-- Physics Letters B 25 (1967), 29--30.
-- DOI: 10.1016/0370-2693(67)90067-6.
--
-- L. F. Abbott, "The Background Field Method Beyond One Loop",
-- Nuclear Physics B 185 (1981), 189--203.
-- DOI: 10.1016/0550-3213(81)90371-0.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
------------------------------------------------------------------------

data WardGenerator : Set where
  gaugePairGenerator measurePairGenerator : WardGenerator

data WardSign : Set where
  positive negative : WardSign

record SignedWardAtom : Set where
  constructor signedWardAtom
  field
    sign : WardSign
    generator : WardGenerator

open SignedWardAtom public

positiveCount : List SignedWardAtom → Nat
positiveCount [] = zero
positiveCount (signedWardAtom positive generator ∷ atoms) =
  suc (positiveCount atoms)
positiveCount (signedWardAtom negative generator ∷ atoms) =
  positiveCount atoms

negativeCount : List SignedWardAtom → Nat
negativeCount [] = zero
negativeCount (signedWardAtom positive generator ∷ atoms) =
  negativeCount atoms
negativeCount (signedWardAtom negative generator ∷ atoms) =
  suc (negativeCount atoms)

record WardBalance (atoms : List SignedWardAtom) : Set where
  field
    positiveEqualsNegative : positiveCount atoms ≡ negativeCount atoms

open WardBalance public

canonicalWardAtoms : List SignedWardAtom
canonicalWardAtoms =
  signedWardAtom positive gaugePairGenerator ∷
  signedWardAtom negative gaugePairGenerator ∷
  signedWardAtom positive measurePairGenerator ∷
  signedWardAtom negative measurePairGenerator ∷ []

canonicalWardPositiveCount : positiveCount canonicalWardAtoms ≡ 2
canonicalWardPositiveCount = refl

canonicalWardNegativeCount : negativeCount canonicalWardAtoms ≡ 2
canonicalWardNegativeCount = refl

canonicalWardBalance : WardBalance canonicalWardAtoms
canonicalWardBalance = record { positiveEqualsNegative = refl }

record LiteralWardReduction
    (expressions : Evaluator.LiteralDiagramExpressions) : Set₁ where
  field
    wardProofs : Evaluator.LiteralWardExpressionProofs expressions
    gaugeBubbleMapsToPositiveGaugeGenerator : Set
    ghostLoopMapsToNegativeGaugeGenerator : Set
    gaugeTadpoleMapsToPositiveMeasureGenerator : Set
    haarLoopMapsToNegativeMeasureGenerator : Set
    shiftedMomentumIdentitiesNormalized : Set
    colorJacobiIdentitiesNormalized : Set
    longitudinalContractionNormalFormExact : ∀ axis → Set
    normalFormIsCanonicalWardAtoms : ∀ axis → Set
    canonicalBalanceImplementsExactCancellation : ∀ axis → Set

open LiteralWardReduction public

record GeneratedBoxCertificateSource : Set₁ where
  field
    generatorName : String
    generatorVersion : String
    symbolicExpressionHash : String
    gridHash : String
    arithmeticCodecHash : String
    deterministicOutput : Set
    everyNumberDescendsFromRecursiveEvaluation : Set
    noOpaquePerBoxConstants : Set

open GeneratedBoxCertificateSource public

record Generated240BoxCertificateFamily
    (expressions : Evaluator.LiteralDiagramExpressions)
    (ward : Evaluator.LiteralWardExpressionProofs expressions)
    (integrand : Evaluator.LiteralScalarIntegrandExpression expressions ward) : Set₁ where
  field
    intervalArithmetic : Evaluator.RationalIntervalArithmetic
    boxEnvironment : Grid.GridCell4 → Evaluator.BoxTrigEnvironment
    source : GeneratedBoxCertificateSource

    evaluator : Grid.RationalBoxEvaluator
    evaluatorUsesLiteralRegularIntegrand : Set
    evaluatorUsesExactlyGeneratedGrid : Set
    denominatorProofBeforeDivision : Set
    quadratureRuleUniformlyDeclared : Set

    regularBoxCountExact : Set
    regularBoxCountUsesGridTheorem :
      Grid.regularGridCellCount ≡ Grid.regularGridCellCount

open Generated240BoxCertificateFamily public

record LiteralOneLoopCertificateClosure : Set₁ where
  field
    expressions : Evaluator.LiteralDiagramExpressions
    wardProofs : Evaluator.LiteralWardExpressionProofs expressions
    wardReduction : LiteralWardReduction expressions
    scalarIntegrand : Evaluator.LiteralScalarIntegrandExpression expressions wardProofs
    boxes : Generated240BoxCertificateFamily expressions wardProofs scalarIntegrand

    massCoefficientZeroFromWardNormalForm : Set
    longitudinalCoefficientZeroFromWardNormalForm : Set
    transverseScalarFactorizationFromNormalForm : Set
    regularIntegralCertifiedBy240Boxes : Set

open LiteralOneLoopCertificateClosure public

wardNormalFormArithmeticLevel : ProofLevel
wardNormalFormArithmeticLevel = machineChecked

literalWardReductionInputsLevel : ProofLevel
literalWardReductionInputsLevel = conditional

generated240BoxFamilyDefinitionLevel : ProofLevel
generated240BoxFamilyDefinitionLevel = machineChecked

generated240BoxReceiptInputsLevel : ProofLevel
generated240BoxReceiptInputsLevel = conditional
