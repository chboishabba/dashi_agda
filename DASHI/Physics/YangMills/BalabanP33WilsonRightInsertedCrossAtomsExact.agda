module DASHI.Physics.YangMills.BalabanP33WilsonRightInsertedCrossAtomsExact where

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
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Specialise the sixteen quaternion product atoms to the right-trivialised
-- first-link derivative convention
--
--   U'_j = U_j J_j,
--
-- where J_j is a concrete pure-imaginary su(2) insertion (for an exponential
-- chart, J_j is the corresponding dexp value).  For each of the six unordered
-- link pairs 01, 02, 03, 12, 13 and 23, quaternion associativity rewrites the
-- generated cross term into
--
--   P J_i M J_j S.
--
-- The general Wilson pairing theorem then proves the exact factorisation
--
--   -q0(P J_i M J_j S)
--     = <J_i, Im(M J_j S P)>.
--
-- The reverse differentiation-order constructor has the same quadratic atom,
-- giving the required multiplicity two.  This identifies and factorises all
-- twelve first/first placements of the nonzero-background Wilson plaquette
-- Hessian.  Only the four diagonal chart-second-derivative atoms remain outside
-- this module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using (-R_)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (Quaternion; oneQ; _*q_; q0; quaternionMultiplyAssociative)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; lieQuaternion)
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  (su2Dot)
import DASHI.Physics.YangMills.BalabanP33QuaternionProductSecondVariationExact as Product
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement
import DASHI.Physics.YangMills.BalabanP33WilsonPlacementQuaternionAtomIdentificationExact as Identification
import DASHI.Physics.YangMills.BalabanP33WilsonTransportedInnerProductExact as Pairing

record RightInsertedLinkJet : Set where
  constructor rightInsertedJet
  field
    background : Quaternion
    insertion : SU2LieAlgebra
    secondVariation : Quaternion

open RightInsertedLinkJet public

asQuaternionFactorJet : RightInsertedLinkJet → Product.QuaternionFactorJet
asQuaternionFactorJet link =
  Product.factorJet
    (background link)
    (background link *q lieQuaternion (insertion link))
    (secondVariation link)

rightInsertionPairNormalize : ∀ prefix insertionLeft middle insertionRight suffix →
  (prefix *q insertionLeft) *q ((middle *q insertionRight) *q suffix)
  ≡ (((prefix *q insertionLeft) *q middle) *q insertionRight) *q suffix
rightInsertionPairNormalize prefix insertionLeft middle insertionRight suffix =
  trans
    (sym
      (quaternionMultiplyAssociative
        (prefix *q insertionLeft)
        (middle *q insertionRight) suffix))
    (cong (_*q suffix)
      (sym
        (quaternionMultiplyAssociative
          (prefix *q insertionLeft) middle insertionRight)))

twoBackgroundsBeforeInsertion : ∀ first second insertionValue suffix →
  first *q ((second *q insertionValue) *q suffix)
  ≡ (((first *q second) *q insertionValue) *q suffix)
twoBackgroundsBeforeInsertion first second insertionValue suffix =
  trans
    (sym
      (quaternionMultiplyAssociative
        first (second *q insertionValue) suffix))
    (cong (_*q suffix)
      (sym
        (quaternionMultiplyAssociative first second insertionValue)))

threeBackgroundsBeforeInsertion :
  ∀ first second third insertionValue suffix →
  first *q (second *q ((third *q insertionValue) *q suffix))
  ≡ (((((first *q second) *q third) *q insertionValue) *q suffix))
threeBackgroundsBeforeInsertion first second third insertionValue suffix =
  trans
    (cong (first *q_)
      (twoBackgroundsBeforeInsertion
        second third insertionValue suffix))
    (trans
      (twoBackgroundsBeforeInsertion
        first (second *q third) insertionValue suffix)
      (cong
        (λ selected → (selected *q insertionValue) *q suffix)
        (sym (quaternionMultiplyAssociative first second third))))

suffix3 : RightInsertedLinkJet → Quaternion
suffix3 fourth = background fourth *q oneQ

suffix23 : RightInsertedLinkJet → RightInsertedLinkJet → Quaternion
suffix23 third fourth = background third *q suffix3 fourth

crossAtomFactorisation :
  ∀ prefix left middle right suffix →
  -R (q0
    ((((prefix *q lieQuaternion left) *q middle)
      *q lieQuaternion right) *q suffix))
  ≡ su2Dot left
      (Pairing.orderedWilsonCrossAtomOperator
        prefix middle suffix right)
crossAtomFactorisation = Pairing.orderedWilsonCrossAtomFactorisation

cross01Factorisation :
  ∀ first second third fourth →
  -R (q0
    (Identification.placementQuaternionAtom
      (asQuaternionFactorJet first)
      (asQuaternionFactorJet second)
      (asQuaternionFactorJet third)
      (asQuaternionFactorJet fourth)
      (Placement.firstFirst Placement.ordered01)))
  ≡ su2Dot (insertion first)
      (Pairing.orderedWilsonCrossAtomOperator
        (background first) (background second)
        (suffix23 third fourth) (insertion second))
cross01Factorisation first second third fourth =
  trans
    (cong (λ selected → -R (q0 selected))
      (rightInsertionPairNormalize
        (background first) (lieQuaternion (insertion first))
        (background second) (lieQuaternion (insertion second))
        (suffix23 third fourth)))
    (crossAtomFactorisation
      (background first) (insertion first)
      (background second) (insertion second)
      (suffix23 third fourth))

cross02Factorisation :
  ∀ first second third fourth →
  -R (q0
    (Identification.placementQuaternionAtom
      (asQuaternionFactorJet first)
      (asQuaternionFactorJet second)
      (asQuaternionFactorJet third)
      (asQuaternionFactorJet fourth)
      (Placement.firstFirst Placement.ordered02)))
  ≡ su2Dot (insertion first)
      (Pairing.orderedWilsonCrossAtomOperator
        (background first) (background second *q background third)
        (suffix3 fourth) (insertion third))
cross02Factorisation first second third fourth =
  trans
    (cong
      (λ selected → -R (q0
        ((background first *q lieQuaternion (insertion first)) *q selected)))
      (twoBackgroundsBeforeInsertion
        (background second) (background third)
        (lieQuaternion (insertion third)) (suffix3 fourth)))
    (trans
      (cong (λ selected → -R (q0 selected))
        (rightInsertionPairNormalize
          (background first) (lieQuaternion (insertion first))
          (background second *q background third)
          (lieQuaternion (insertion third)) (suffix3 fourth)))
      (crossAtomFactorisation
        (background first) (insertion first)
        (background second *q background third)
        (insertion third) (suffix3 fourth)))

cross03Factorisation :
  ∀ first second third fourth →
  -R (q0
    (Identification.placementQuaternionAtom
      (asQuaternionFactorJet first)
      (asQuaternionFactorJet second)
      (asQuaternionFactorJet third)
      (asQuaternionFactorJet fourth)
      (Placement.firstFirst Placement.ordered03)))
  ≡ su2Dot (insertion first)
      (Pairing.orderedWilsonCrossAtomOperator
        (background first)
        ((background second *q background third) *q background fourth)
        oneQ (insertion fourth))
cross03Factorisation first second third fourth =
  trans
    (cong
      (λ selected → -R (q0
        ((background first *q lieQuaternion (insertion first)) *q selected)))
      (threeBackgroundsBeforeInsertion
        (background second) (background third) (background fourth)
        (lieQuaternion (insertion fourth)) oneQ))
    (trans
      (cong (λ selected → -R (q0 selected))
        (rightInsertionPairNormalize
          (background first) (lieQuaternion (insertion first))
          ((background second *q background third) *q background fourth)
          (lieQuaternion (insertion fourth)) oneQ))
      (crossAtomFactorisation
        (background first) (insertion first)
        ((background second *q background third) *q background fourth)
        (insertion fourth) oneQ))

cross12Factorisation :
  ∀ first second third fourth →
  -R (q0
    (Identification.placementQuaternionAtom
      (asQuaternionFactorJet first)
      (asQuaternionFactorJet second)
      (asQuaternionFactorJet third)
      (asQuaternionFactorJet fourth)
      (Placement.firstFirst Placement.ordered12)))
  ≡ su2Dot (insertion second)
      (Pairing.orderedWilsonCrossAtomOperator
        (background first *q background second)
        (background third) (suffix3 fourth) (insertion third))
cross12Factorisation first second third fourth =
  trans
    (cong (λ selected → -R (q0 selected))
      (twoBackgroundsBeforeInsertion
        (background first) (background second)
        (lieQuaternion (insertion second))
        ((background third *q lieQuaternion (insertion third))
          *q suffix3 fourth)))
    (trans
      (cong (λ selected → -R (q0 selected))
        (rightInsertionPairNormalize
          (background first *q background second)
          (lieQuaternion (insertion second))
          (background third) (lieQuaternion (insertion third))
          (suffix3 fourth)))
      (crossAtomFactorisation
        (background first *q background second) (insertion second)
        (background third) (insertion third) (suffix3 fourth)))

cross13Factorisation :
  ∀ first second third fourth →
  -R (q0
    (Identification.placementQuaternionAtom
      (asQuaternionFactorJet first)
      (asQuaternionFactorJet second)
      (asQuaternionFactorJet third)
      (asQuaternionFactorJet fourth)
      (Placement.firstFirst Placement.ordered13)))
  ≡ su2Dot (insertion second)
      (Pairing.orderedWilsonCrossAtomOperator
        (background first *q background second)
        (background third *q background fourth)
        oneQ (insertion fourth))
cross13Factorisation first second third fourth =
  trans
    (cong (λ selected → -R (q0 selected))
      (twoBackgroundsBeforeInsertion
        (background first) (background second)
        (lieQuaternion (insertion second))
        (background third *q
          ((background fourth *q lieQuaternion (insertion fourth))
            *q oneQ))))
    (trans
      (cong
        (λ selected → -R (q0
          (((background first *q background second)
            *q lieQuaternion (insertion second)) *q selected)))
        (twoBackgroundsBeforeInsertion
          (background third) (background fourth)
          (lieQuaternion (insertion fourth)) oneQ))
      (trans
        (cong (λ selected → -R (q0 selected))
          (rightInsertionPairNormalize
            (background first *q background second)
            (lieQuaternion (insertion second))
            (background third *q background fourth)
            (lieQuaternion (insertion fourth)) oneQ))
        (crossAtomFactorisation
          (background first *q background second) (insertion second)
          (background third *q background fourth)
          (insertion fourth) oneQ)))

cross23Factorisation :
  ∀ first second third fourth →
  -R (q0
    (Identification.placementQuaternionAtom
      (asQuaternionFactorJet first)
      (asQuaternionFactorJet second)
      (asQuaternionFactorJet third)
      (asQuaternionFactorJet fourth)
      (Placement.firstFirst Placement.ordered23)))
  ≡ su2Dot (insertion third)
      (Pairing.orderedWilsonCrossAtomOperator
        (background first *q (background second *q background third))
        (background fourth) oneQ (insertion fourth))
cross23Factorisation first second third fourth =
  trans
    (cong
      (λ selected → -R (q0 (background first *q selected)))
      (twoBackgroundsBeforeInsertion
        (background second) (background third)
        (lieQuaternion (insertion third))
        ((background fourth *q lieQuaternion (insertion fourth))
          *q oneQ)))
    (trans
      (cong (λ selected → -R (q0 selected))
        (twoBackgroundsBeforeInsertion
          (background first) (background second *q background third)
          (lieQuaternion (insertion third))
          ((background fourth *q lieQuaternion (insertion fourth))
            *q oneQ)))
      (trans
        (cong (λ selected → -R (q0 selected))
          (rightInsertionPairNormalize
            (background first *q (background second *q background third))
            (lieQuaternion (insertion third))
            (background fourth) (lieQuaternion (insertion fourth)) oneQ))
        (crossAtomFactorisation
          (background first *q (background second *q background third))
          (insertion third)
          (background fourth) (insertion fourth) oneQ)))

rightInsertedWilsonCross01Level : ProofLevel
rightInsertedWilsonCross01Level = machineChecked
rightInsertedWilsonCross02Level : ProofLevel
rightInsertedWilsonCross02Level = machineChecked
rightInsertedWilsonCross03Level : ProofLevel
rightInsertedWilsonCross03Level = machineChecked
rightInsertedWilsonCross12Level : ProofLevel
rightInsertedWilsonCross12Level = machineChecked
rightInsertedWilsonCross13Level : ProofLevel
rightInsertedWilsonCross13Level = machineChecked
rightInsertedWilsonCross23Level : ProofLevel
rightInsertedWilsonCross23Level = machineChecked

rightInsertedWilsonAllTwelveCrossPlacementsLevel : ProofLevel
rightInsertedWilsonAllTwelveCrossPlacementsLevel = machineChecked
