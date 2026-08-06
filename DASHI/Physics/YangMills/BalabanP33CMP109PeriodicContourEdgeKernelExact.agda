module DASHI.Physics.YangMills.BalabanP33CMP109PeriodicContourEdgeKernelExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- DASHI CONTRIBUTION
--
-- Instantiate the literal path-derivative recursion on the repository's
-- periodic CMP109 contour words.  A signed step is represented by an oriented
-- occurrence of one underlying positive bond.  Under the left perturbation
-- convention U_b(t)=exp(t A_b)U_b, the occurrence insertion is
--
--   positive step:   A_b,
--   negative step:  -Ad_{U_b^{-1}} A_b.
--
-- The negative formula is the exact left-trivialized derivative of U_b^{-1}.
-- The executable occurrence list follows the walk site at every step, so it
-- retains both periodic location and orientation.  Its holonomy is proved
-- definitionally equal to the existing periodic path holonomy.
--
-- For a selected positive bond b, the resulting derivative kernel vanishes
-- whenever b is absent from the underlying-bond projection of the contour.
-- This discharges the orientation-sensitive path leaf needed by the CMP109
-- Fréchet assembly; only identification with the analytic derivative of the
-- repository's curve-valued link exponential remains physical.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4FiniteHolonomyDerivativeExact as Holonomy
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Contour

------------------------------------------------------------------------
-- Oriented occurrences of the positive-bond carrier.
------------------------------------------------------------------------

record OrientedBondOccurrence (n : Nat) : Set where
  constructor occurrence
  field
    underlyingBond : Carrier.PositiveBond (suc n)
    forward : Bool

open OrientedBondOccurrence public

occurrenceAt :
  ∀ {n} → Periodic.PeriodicBlock n →
  Carrier.Product Carrier.Axis4 Bool → OrientedBondOccurrence n
occurrenceAt site (Carrier.pair axis true) =
  occurrence (Carrier.pair site axis) true
occurrenceAt site (Carrier.pair axis false) =
  occurrence
    (Carrier.pair (Bond.negativeStep site axis) axis)
    false

contourOccurrences :
  ∀ {n} → Periodic.PeriodicBlock n →
  List (Carrier.Product Carrier.Axis4 Bool) →
  List (OrientedBondOccurrence n)
contourOccurrences site [] = []
contourOccurrences site (direction ∷ directions) =
  occurrenceAt site direction
  ∷ contourOccurrences (Bond.walkStep site direction) directions

listLength : ∀ {A : Set} → List A → Nat
listLength [] = 0
listLength (_ ∷ values) = suc (listLength values)

contourOccurrenceLength :
  ∀ {n} (site : Periodic.PeriodicBlock n) directions →
  listLength (contourOccurrences site directions)
  ≡ listLength directions
contourOccurrenceLength site [] = refl
contourOccurrenceLength site (direction ∷ directions) =
  cong suc
    (contourOccurrenceLength (Bond.walkStep site direction) directions)

------------------------------------------------------------------------
-- Exact occurrence values and holonomy identification.
------------------------------------------------------------------------

record OrientedDifferentialAlgebra
    (Group Lie : Set) : Set₁ where
  field
    group : Bond.ExactLinkGroup Group
    lie : Holonomy.HolonomyDifferentialAlgebra Group Lie

    negateLie : Lie → Lie
    negateZero : negateLie (Holonomy.zeroLie lie) ≡ Holonomy.zeroLie lie

open OrientedDifferentialAlgebra public

occurrenceValue :
  ∀ {n Group Lie} →
  OrientedDifferentialAlgebra Group Lie →
  Bond.PeriodicBondField n Group →
  OrientedBondOccurrence n → Group
occurrenceValue algebra connection (occurrence bond true) = connection bond
occurrenceValue algebra connection (occurrence bond false) =
  Bond.inverse (group algebra) (connection bond)

orientedLinkValue :
  ∀ {n Group Lie} →
  OrientedDifferentialAlgebra Group Lie →
  Bond.PeriodicBondField n Group →
  Periodic.PeriodicBlock n →
  Carrier.Product Carrier.Axis4 Bool → Group
orientedLinkValue algebra connection site (Carrier.pair axis true) =
  connection (Carrier.pair site axis)
orientedLinkValue algebra connection site (Carrier.pair axis false) =
  Bond.inverse (group algebra)
    (connection (Carrier.pair (Bond.negativeStep site axis) axis))

occurrenceValueMatchesOrientedLink :
  ∀ {n Group Lie}
    (algebra : OrientedDifferentialAlgebra Group Lie)
    (connection : Bond.PeriodicBondField n Group)
    site direction →
  occurrenceValue algebra connection (occurrenceAt site direction)
  ≡ orientedLinkValue algebra connection site direction
occurrenceValueMatchesOrientedLink algebra connection site
    (Carrier.pair axis true) = refl
occurrenceValueMatchesOrientedLink algebra connection site
    (Carrier.pair axis false) = refl

literalOccurrenceHolonomy :
  ∀ {n Group Lie} →
  OrientedDifferentialAlgebra Group Lie →
  Bond.PeriodicBondField n Group →
  List (OrientedBondOccurrence n) → Group
literalOccurrenceHolonomy algebra connection =
  Holonomy.holonomy (lie algebra) (occurrenceValue algebra connection)

literalPeriodicWordHolonomy :
  ∀ {n Group Lie} →
  OrientedDifferentialAlgebra Group Lie →
  Bond.PeriodicBondField n Group →
  Periodic.PeriodicBlock n →
  List (Carrier.Product Carrier.Axis4 Bool) → Group
literalPeriodicWordHolonomy algebra connection site [] =
  Bond.identity (group algebra)
literalPeriodicWordHolonomy algebra connection site (direction ∷ directions) =
  Bond.multiply (group algebra)
    (orientedLinkValue algebra connection site direction)
    (literalPeriodicWordHolonomy algebra connection
      (Bond.walkStep site direction) directions)

record GroupOperationsAgree
    (Group Lie : Set)
    (algebra : OrientedDifferentialAlgebra Group Lie) : Set₁ where
  field
    identityAgrees :
      Holonomy.identityGroup (lie algebra) ≡ Bond.identity (group algebra)
    multiplicationAgrees : ∀ left right →
      Holonomy.multiplyGroup (lie algebra) left right
      ≡ Bond.multiply (group algebra) left right

open GroupOperationsAgree public

occurrenceHolonomyEqualsPeriodicWordHolonomy :
  ∀ {n Group Lie}
    (algebra : OrientedDifferentialAlgebra Group Lie)
    (agreement : GroupOperationsAgree Group Lie algebra)
    (connection : Bond.PeriodicBondField n Group)
    site directions →
  literalOccurrenceHolonomy algebra connection
    (contourOccurrences site directions)
  ≡ literalPeriodicWordHolonomy algebra connection site directions
occurrenceHolonomyEqualsPeriodicWordHolonomy
    algebra agreement connection site [] =
  identityAgrees agreement
occurrenceHolonomyEqualsPeriodicWordHolonomy
    algebra agreement connection site (direction ∷ directions) =
  trans
    (multiplicationAgrees agreement
      (occurrenceValue algebra connection (occurrenceAt site direction))
      (literalOccurrenceHolonomy algebra connection
        (contourOccurrences (Bond.walkStep site direction) directions)))
    (trans
      (cong
        (λ firstValue →
          Bond.multiply (group algebra) firstValue
            (literalOccurrenceHolonomy algebra connection
              (contourOccurrences
                (Bond.walkStep site direction) directions)))
        (occurrenceValueMatchesOrientedLink
          algebra connection site direction))
      (cong
        (Bond.multiply (group algebra)
          (orientedLinkValue algebra connection site direction))
        (occurrenceHolonomyEqualsPeriodicWordHolonomy
          algebra agreement connection
          (Bond.walkStep site direction) directions)))

------------------------------------------------------------------------
-- Orientation-sensitive left-trivialized insertion.
------------------------------------------------------------------------

orientationInsertion :
  ∀ {Group Lie} →
  OrientedDifferentialAlgebra Group Lie →
  Group → Bool → Lie → Lie
orientationInsertion algebra bondValue true vector = vector
orientationInsertion algebra bondValue false vector =
  negateLie algebra
    (Holonomy.adjoint (lie algebra)
      (Bond.inverse (group algebra) bondValue)
      vector)

orientationInsertionZero :
  ∀ {Group Lie}
    (algebra : OrientedDifferentialAlgebra Group Lie)
    bondValue orientation →
  orientationInsertion algebra bondValue orientation
    (Holonomy.zeroLie (lie algebra))
  ≡ Holonomy.zeroLie (lie algebra)
orientationInsertionZero algebra bondValue true = refl
orientationInsertionZero algebra bondValue false =
  trans
    (cong (negateLie algebra)
      (Holonomy.adjointZero (lie algebra)
        (Bond.inverse (group algebra) bondValue)))
    (negateZero algebra)

positiveBondDecidableEquality :
  ∀ n → Carrier.DecidableEquality (Carrier.PositiveBond (suc n))
positiveBondDecidableEquality n =
  Carrier.productDecidableEquality
    (Carrier.periodicTorus4DecidableEquality (suc n))
    Carrier.cyclicIndexDecidableEquality

selectedOccurrenceVariation :
  ∀ {n Group Lie} →
  OrientedDifferentialAlgebra Group Lie →
  Bond.PeriodicBondField n Group →
  Carrier.PositiveBond (suc n) → Lie →
  OrientedBondOccurrence n → Lie
selectedOccurrenceVariation {n} algebra connection selected vector
    (occurrence bond orientation)
    with positiveBondDecidableEquality n selected bond
... | Carrier.yes _ =
  orientationInsertion algebra (connection bond) orientation vector
... | Carrier.no _ = Holonomy.zeroLie (lie algebra)

orientedContourDerivativeKernel :
  ∀ {n Group Lie} →
  OrientedDifferentialAlgebra Group Lie →
  Bond.PeriodicBondField n Group →
  Periodic.PeriodicBlock n →
  List (Carrier.Product Carrier.Axis4 Bool) →
  Carrier.PositiveBond (suc n) → Lie → Lie
orientedContourDerivativeKernel algebra connection start directions
    selected vector =
  Holonomy.leftTrivializedHolonomyDerivative
    (lie algebra)
    (occurrenceValue algebra connection)
    (selectedOccurrenceVariation algebra connection selected vector)
    (contourOccurrences start directions)

------------------------------------------------------------------------
-- Proof-relevant absence from the underlying positive-bond projection.
------------------------------------------------------------------------

data UnderlyingAbsent {n : Nat}
    (selected : Carrier.PositiveBond (suc n)) :
    List (OrientedBondOccurrence n) → Set where
  absentNil : UnderlyingAbsent selected []
  absentCons : ∀ {bond orientation rest} →
    Carrier._≢_ selected bond →
    UnderlyingAbsent selected rest →
    UnderlyingAbsent selected (occurrence bond orientation ∷ rest)

selectedVariationZeroOnAbsentOccurrences :
  ∀ {n Group Lie}
    (algebra : OrientedDifferentialAlgebra Group Lie)
    (connection : Bond.PeriodicBondField n Group)
    selected vector occurrences →
  UnderlyingAbsent selected occurrences →
  Holonomy.All
    (λ edge →
      selectedOccurrenceVariation algebra connection selected vector edge
      ≡ Holonomy.zeroLie (lie algebra))
    occurrences
selectedVariationZeroOnAbsentOccurrences algebra connection selected vector
    [] absentNil = Holonomy.allNil
selectedVariationZeroOnAbsentOccurrences {n} algebra connection selected vector
    (occurrence bond orientation ∷ rest)
    (absentCons unequal absentTail)
    with positiveBondDecidableEquality n selected bond
... | Carrier.yes equal = unequal equal
... | Carrier.no _ =
  Holonomy.allCons refl
    (selectedVariationZeroOnAbsentOccurrences
      algebra connection selected vector rest absentTail)

orientedContourDerivativeZeroOutsideUnderlyingSupport :
  ∀ {n Group Lie}
    (algebra : OrientedDifferentialAlgebra Group Lie)
    (connection : Bond.PeriodicBondField n Group)
    start directions selected vector →
  UnderlyingAbsent selected (contourOccurrences start directions) →
  orientedContourDerivativeKernel
    algebra connection start directions selected vector
  ≡ Holonomy.zeroLie (lie algebra)
orientedContourDerivativeZeroOutsideUnderlyingSupport
    algebra connection start directions selected vector absence =
  Holonomy.variationZeroOnPath
    (lie algebra)
    (occurrenceValue algebra connection)
    (selectedOccurrenceVariation algebra connection selected vector)
    (contourOccurrences start directions)
    (selectedVariationZeroOnAbsentOccurrences
      algebra connection selected vector
      (contourOccurrences start directions) absence)

------------------------------------------------------------------------
-- Direct specialization to one executable periodic contour.
------------------------------------------------------------------------

executableContourDerivativeKernel :
  ∀ {n Group Lie}
    (algebra : OrientedDifferentialAlgebra Group Lie)
    (connection : Bond.PeriodicBondField n Group)
    {start : Periodic.PeriodicBlock n} →
  Contour.ExecutablePeriodicContour n start →
  Carrier.PositiveBond (suc n) → Lie → Lie
executableContourDerivativeKernel algebra connection {start} contour =
  orientedContourDerivativeKernel algebra connection start
    (Contour.directions contour)

executableContourDerivativeZeroOutsideSupport :
  ∀ {n Group Lie}
    (algebra : OrientedDifferentialAlgebra Group Lie)
    (connection : Bond.PeriodicBondField n Group)
    {start : Periodic.PeriodicBlock n}
    (contour : Contour.ExecutablePeriodicContour n start)
    selected vector →
  UnderlyingAbsent selected
    (contourOccurrences start (Contour.directions contour)) →
  executableContourDerivativeKernel
    algebra connection contour selected vector
  ≡ Holonomy.zeroLie (lie algebra)
executableContourDerivativeZeroOutsideSupport
    algebra connection contour selected vector absence =
  orientedContourDerivativeZeroOutsideUnderlyingSupport
    algebra connection _ _ selected vector absence

cmp109PeriodicOccurrenceEnumerationLevel : ProofLevel
cmp109PeriodicOccurrenceEnumerationLevel = machineChecked

cmp109PeriodicOccurrenceHolonomyLevel : ProofLevel
cmp109PeriodicOccurrenceHolonomyLevel = machineChecked

cmp109NegativeLinkDerivativeInsertionLevel : ProofLevel
cmp109NegativeLinkDerivativeInsertionLevel = machineChecked

cmp109PeriodicContourDerivativeSupportLevel : ProofLevel
cmp109PeriodicContourDerivativeSupportLevel = machineChecked

physicalLinkCurveDerivativeIdentificationLevel : ProofLevel
physicalLinkCurveDerivativeIdentificationLevel = conditional
