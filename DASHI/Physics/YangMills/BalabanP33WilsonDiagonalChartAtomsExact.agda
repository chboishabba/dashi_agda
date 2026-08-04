module DASHI.Physics.YangMills.BalabanP33WilsonDiagonalChartAtomsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- DASHI CONTRIBUTION
--
-- Isolate the four diagonal link-chart terms in the literal Wilson plaquette
-- Hessian.  For a link second variation D_j, quaternion associativity and
-- scalar cyclicity put every named placement into the uniform normal form
--
--   -q0(D_j S_j P_j),
--
-- where P_j is the ordered background prefix and S_j the ordered suffix.
-- This is the precise scalar functional to which the second derivative of the
-- exponential chart must be applied.  Together with the twelve cross-pair
-- factorisations, all sixteen Wilson atoms now have explicit noncommutative
-- normal forms; the remaining diagonal work is solely the quantitative bound
-- on the chart second derivative itself.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using (-R_)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (Quaternion; oneQ; _*q_; q0; quaternionOneRight)
import DASHI.Physics.YangMills.BalabanP33QuaternionScalarCyclicityExact as Cyclic
import DASHI.Physics.YangMills.BalabanP33QuaternionProductSecondVariationExact as Product
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement
import DASHI.Physics.YangMills.BalabanP33WilsonPlacementQuaternionAtomIdentificationExact as Identification
import DASHI.Physics.YangMills.BalabanP33WilsonRightInsertedCrossAtomsExact as Inserted

wilsonDiagonalChartFunctional :
  Quaternion → Quaternion → Quaternion → ℝ
wilsonDiagonalChartFunctional prefix suffix second =
  -R (q0 ((second *q suffix) *q prefix))

diagonalCyclicNormalForm : ∀ prefix second suffix →
  -R (q0 (prefix *q (second *q suffix)))
  ≡ wilsonDiagonalChartFunctional prefix suffix second
diagonalCyclicNormalForm prefix second suffix =
  cong -R_ (Cyclic.scalarPartTwoFactorCyclic prefix (second *q suffix))

secondAt0NormalForm :
  ∀ first second third fourth →
  -R (q0
    (Identification.placementQuaternionAtom
      (Inserted.asQuaternionFactorJet first)
      (Inserted.asQuaternionFactorJet second)
      (Inserted.asQuaternionFactorJet third)
      (Inserted.asQuaternionFactorJet fourth)
      Placement.secondAt0))
  ≡ -R (q0
      (Product.factorSecond (Inserted.asQuaternionFactorJet first)
        *q Product.orderedValueProduct
          (Identification.threeFactors
            (Inserted.asQuaternionFactorJet second)
            (Inserted.asQuaternionFactorJet third)
            (Inserted.asQuaternionFactorJet fourth))))
secondAt0NormalForm first second third fourth = refl

secondAt1NormalForm :
  ∀ first second third fourth →
  -R (q0
    (Identification.placementQuaternionAtom
      (Inserted.asQuaternionFactorJet first)
      (Inserted.asQuaternionFactorJet second)
      (Inserted.asQuaternionFactorJet third)
      (Inserted.asQuaternionFactorJet fourth)
      Placement.secondAt1))
  ≡ wilsonDiagonalChartFunctional
      (Inserted.background first)
      (Inserted.suffix23 third fourth)
      (Inserted.secondVariation second)
secondAt1NormalForm first second third fourth =
  diagonalCyclicNormalForm
    (Inserted.background first)
    (Inserted.secondVariation second)
    (Inserted.suffix23 third fourth)

secondAt2NormalForm :
  ∀ first second third fourth →
  -R (q0
    (Identification.placementQuaternionAtom
      (Inserted.asQuaternionFactorJet first)
      (Inserted.asQuaternionFactorJet second)
      (Inserted.asQuaternionFactorJet third)
      (Inserted.asQuaternionFactorJet fourth)
      Placement.secondAt2))
  ≡ wilsonDiagonalChartFunctional
      (Inserted.background first *q Inserted.background second)
      (Inserted.suffix3 fourth)
      (Inserted.secondVariation third)
secondAt2NormalForm first second third fourth =
  trans
    (cong (λ selected → -R (q0 selected))
      (Inserted.twoBackgroundsBeforeInsertion
        (Inserted.background first) (Inserted.background second)
        (Inserted.secondVariation third) (Inserted.suffix3 fourth)))
    (diagonalCyclicNormalForm
      (Inserted.background first *q Inserted.background second)
      (Inserted.secondVariation third)
      (Inserted.suffix3 fourth))

secondAt3NormalForm :
  ∀ first second third fourth →
  -R (q0
    (Identification.placementQuaternionAtom
      (Inserted.asQuaternionFactorJet first)
      (Inserted.asQuaternionFactorJet second)
      (Inserted.asQuaternionFactorJet third)
      (Inserted.asQuaternionFactorJet fourth)
      Placement.secondAt3))
  ≡ wilsonDiagonalChartFunctional
      ((Inserted.background first *q Inserted.background second)
        *q Inserted.background third)
      oneQ
      (Inserted.secondVariation fourth)
secondAt3NormalForm first second third fourth =
  trans
    (cong (λ selected → -R (q0 selected))
      (Inserted.threeBackgroundsBeforeInsertion
        (Inserted.background first) (Inserted.background second)
        (Inserted.background third)
        (Inserted.secondVariation fourth) oneQ))
    (diagonalCyclicNormalForm
      ((Inserted.background first *q Inserted.background second)
        *q Inserted.background third)
      (Inserted.secondVariation fourth) oneQ)

wilsonDiagonalChart0Level : ProofLevel
wilsonDiagonalChart0Level = machineChecked
wilsonDiagonalChart1Level : ProofLevel
wilsonDiagonalChart1Level = machineChecked
wilsonDiagonalChart2Level : ProofLevel
wilsonDiagonalChart2Level = machineChecked
wilsonDiagonalChart3Level : ProofLevel
wilsonDiagonalChart3Level = machineChecked

wilsonAllFourDiagonalChartNormalFormsLevel : ProofLevel
wilsonAllFourDiagonalChartNormalFormsLevel = machineChecked
