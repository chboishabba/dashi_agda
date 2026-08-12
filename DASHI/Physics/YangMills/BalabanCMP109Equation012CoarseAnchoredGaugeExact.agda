module DASHI.Physics.YangMills.BalabanCMP109Equation012CoarseAnchoredGaugeExact where

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
-- DASHI CONTRIBUTION
--
-- Close the algebraic equation-(0.12) gauge seam on the literal printed
-- product, rather than routing through an independently supplied block map.
-- The four factors
--
--   U(c_-,x) U([x,x']) U(x',c_+) U(-c)
--
-- carry successive endpoint gauges
--
--   s -> x -> x' -> t -> s.
--
-- Associativity and inverse cancellation telescope every internal gauge and
-- prove that the whole relative product transforms by conjugation at c_-.
-- Consequently, if the fine gauge is identity on embedded coarse sites, the
-- relative product itself is unchanged.  The printed finite Lie average is
-- then unchanged term-by-term, and the final coarse-bond factor is unchanged
-- when both coarse endpoints are anchored.  Hence equation (0.12) itself obeys
--
--   Q(U^g)(c) = Q(U)(c)
--
-- for coarse-anchored gauges.  No commutativity or factor reordering is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedPathFormulaExact as Printed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109GroupAverageAxiomsExact as Average

------------------------------------------------------------------------
-- Group laws used by the literal product cancellation.
------------------------------------------------------------------------

record CMP109GroupLaws
    {Group Lie Scalar : Set}
    (averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar) : Set₁ where
  field
    multiplyAssociative : ∀ left middle right →
      Average.multiply averageAxioms
        (Average.multiply averageAxioms left middle) right
      ≡ Average.multiply averageAxioms left
          (Average.multiply averageAxioms middle right)

    multiplyIdentityLeft : ∀ value →
      Average.multiply averageAxioms
        (Average.identity averageAxioms) value ≡ value

    multiplyIdentityRight : ∀ value →
      Average.multiply averageAxioms value
        (Average.identity averageAxioms) ≡ value

    inverseLeft : ∀ value →
      Average.multiply averageAxioms
        (Average.inverse averageAxioms value) value
      ≡ Average.identity averageAxioms

    inverseRight : ∀ value →
      Average.multiply averageAxioms value
        (Average.inverse averageAxioms value)
      ≡ Average.identity averageAxioms

    inverseIdentity :
      Average.inverse averageAxioms (Average.identity averageAxioms)
      ≡ Average.identity averageAxioms

open CMP109GroupLaws public

cancelAdjacent :
  ∀ {Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    (laws : CMP109GroupLaws averageAxioms)
    left middle right →
  Average.multiply averageAxioms
    (Average.multiply averageAxioms left
      (Average.inverse averageAxioms middle))
    (Average.multiply averageAxioms middle right)
  ≡ Average.multiply averageAxioms left right
cancelAdjacent {averageAxioms = averageAxioms} laws left middle right =
  trans
    (multiplyAssociative laws
      left (Average.inverse averageAxioms middle)
      (Average.multiply averageAxioms middle right))
    (cong
      (Average.multiply averageAxioms left)
      (trans
        (sym
          (multiplyAssociative laws
            (Average.inverse averageAxioms middle) middle right))
        (trans
          (cong
            (λ product → Average.multiply averageAxioms product right)
            (inverseLeft laws middle))
          (multiplyIdentityLeft laws right))))

composeGaugeTransport :
  ∀ {Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    (laws : CMP109GroupLaws averageAxioms)
    source middle target left right →
  Average.multiply averageAxioms
    (Average.multiply averageAxioms source
      (Average.multiply averageAxioms left
        (Average.inverse averageAxioms middle)))
    (Average.multiply averageAxioms middle
      (Average.multiply averageAxioms right
        (Average.inverse averageAxioms target)))
  ≡ Average.multiply averageAxioms source
      (Average.multiply averageAxioms
        (Average.multiply averageAxioms left right)
        (Average.inverse averageAxioms target))
composeGaugeTransport {averageAxioms = averageAxioms}
    laws source middle target left right =
  trans
    (multiplyAssociative laws
      source
      (Average.multiply averageAxioms left
        (Average.inverse averageAxioms middle))
      (Average.multiply averageAxioms middle
        (Average.multiply averageAxioms right
          (Average.inverse averageAxioms target))))
    (trans
      (cong
        (Average.multiply averageAxioms source)
        (cancelAdjacent laws left middle
          (Average.multiply averageAxioms right
            (Average.inverse averageAxioms target))))
      (cong
        (Average.multiply averageAxioms source)
        (sym
          (multiplyAssociative laws left right
            (Average.inverse averageAxioms target)))))

rightFourToLeft :
  ∀ {Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    (laws : CMP109GroupLaws averageAxioms)
    first second third fourth →
  Average.multiply averageAxioms first
    (Average.multiply averageAxioms second
      (Average.multiply averageAxioms third fourth))
  ≡ Average.multiply averageAxioms
      (Average.multiply averageAxioms
        (Average.multiply averageAxioms first second) third)
      fourth
rightFourToLeft {averageAxioms = averageAxioms}
    laws first second third fourth =
  trans
    (sym
      (multiplyAssociative laws first second
        (Average.multiply averageAxioms third fourth)))
    (sym
      (multiplyAssociative laws
        (Average.multiply averageAxioms first second) third fourth))

fourFactorGaugeTelescope :
  ∀ {Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    (laws : CMP109GroupLaws averageAxioms)
    source firstMiddle secondMiddle target
    first second third fourth →
  Average.multiply averageAxioms
    (Average.multiply averageAxioms source
      (Average.multiply averageAxioms first
        (Average.inverse averageAxioms firstMiddle)))
    (Average.multiply averageAxioms
      (Average.multiply averageAxioms firstMiddle
        (Average.multiply averageAxioms second
          (Average.inverse averageAxioms secondMiddle)))
      (Average.multiply averageAxioms
        (Average.multiply averageAxioms secondMiddle
          (Average.multiply averageAxioms third
            (Average.inverse averageAxioms target)))
        (Average.multiply averageAxioms target
          (Average.multiply averageAxioms fourth
            (Average.inverse averageAxioms source)))))
  ≡ Average.multiply averageAxioms source
      (Average.multiply averageAxioms
        (Average.multiply averageAxioms first
          (Average.multiply averageAxioms second
            (Average.multiply averageAxioms third fourth)))
        (Average.inverse averageAxioms source))
fourFactorGaugeTelescope {averageAxioms = averageAxioms}
    laws source firstMiddle secondMiddle target
    first second third fourth =
  let
    f1 = Average.multiply averageAxioms source
      (Average.multiply averageAxioms first
        (Average.inverse averageAxioms firstMiddle))
    f2 = Average.multiply averageAxioms firstMiddle
      (Average.multiply averageAxioms second
        (Average.inverse averageAxioms secondMiddle))
    f3 = Average.multiply averageAxioms secondMiddle
      (Average.multiply averageAxioms third
        (Average.inverse averageAxioms target))
    f4 = Average.multiply averageAxioms target
      (Average.multiply averageAxioms fourth
        (Average.inverse averageAxioms source))

    firstTwo = Average.multiply averageAxioms first second
    firstThree = Average.multiply averageAxioms firstTwo third
    leftFour = Average.multiply averageAxioms firstThree fourth
    rightFour = Average.multiply averageAxioms first
      (Average.multiply averageAxioms second
        (Average.multiply averageAxioms third fourth))

    leftFourToRight : leftFour ≡ rightFour
    leftFourToRight =
      sym (rightFourToLeft laws first second third fourth)
  in
  trans
    (rightFourToLeft laws f1 f2 f3 f4)
    (trans
      (cong
        (λ pair12 →
          Average.multiply averageAxioms
            (Average.multiply averageAxioms pair12 f3) f4)
        (composeGaugeTransport laws
          source firstMiddle secondMiddle first second))
      (trans
        (cong
          (λ triple123 → Average.multiply averageAxioms triple123 f4)
          (composeGaugeTransport laws
            source secondMiddle target firstTwo third))
        (trans
          (composeGaugeTransport laws
            source target source firstThree fourth)
          (cong
            (λ body → Average.multiply averageAxioms source
              (Average.multiply averageAxioms body
                (Average.inverse averageAxioms source)))
            leftFourToRight))))

conjugationByIdentity :
  ∀ {Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    (laws : CMP109GroupLaws averageAxioms)
    value →
  Average.multiply averageAxioms (Average.identity averageAxioms)
    (Average.multiply averageAxioms value
      (Average.inverse averageAxioms (Average.identity averageAxioms)))
  ≡ value
conjugationByIdentity {averageAxioms = averageAxioms} laws value =
  trans
    (cong
      (Average.multiply averageAxioms (Average.identity averageAxioms))
      (trans
        (cong
          (Average.multiply averageAxioms value)
          (inverseIdentity laws))
        (multiplyIdentityRight laws value)))
    (multiplyIdentityLeft laws value)

openBondByIdentity :
  ∀ {Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    (laws : CMP109GroupLaws averageAxioms)
    value →
  Average.multiply averageAxioms (Average.identity averageAxioms)
    (Average.multiply averageAxioms value
      (Average.inverse averageAxioms (Average.identity averageAxioms)))
  ≡ value
openBondByIdentity = conjugationByIdentity

------------------------------------------------------------------------
-- Literal equation-(0.12) gauge-action data.
------------------------------------------------------------------------

record Equation012GaugeActionData
    (Field Gauge CoarseBond FineSite Group Lie Scalar : Set)
    (averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar)
    (printed : Printed.PrintedCMP109Equation012Data
      Field CoarseBond FineSite Group Lie Scalar) : Set₁ where
  field
    gaugeAction : Gauge → Field → Field

    sourceGauge targetGauge : Gauge → CoarseBond → Group
    sourceFineGauge targetFineGauge :
      Gauge → CoarseBond → FineSite → Group

    sourceAveragedContourCovariant : ∀ gauge input coarse fine →
      Printed.sourceAveragedContour printed
        (gaugeAction gauge input) coarse fine
      ≡ Average.multiply averageAxioms (sourceGauge gauge coarse)
          (Average.multiply averageAxioms
            (Printed.sourceAveragedContour printed input coarse fine)
            (Average.inverse averageAxioms
              (sourceFineGauge gauge coarse fine)))

    crossingValueCovariant : ∀ gauge input coarse fine →
      Printed.crossingValue printed (gaugeAction gauge input) coarse fine
      ≡ Average.multiply averageAxioms (sourceFineGauge gauge coarse fine)
          (Average.multiply averageAxioms
            (Printed.crossingValue printed input coarse fine)
            (Average.inverse averageAxioms
              (targetFineGauge gauge coarse fine)))

    targetAveragedContourReverseCovariant : ∀ gauge input coarse fine →
      Printed.targetAveragedContourReverse printed
        (gaugeAction gauge input) coarse fine
      ≡ Average.multiply averageAxioms (targetFineGauge gauge coarse fine)
          (Average.multiply averageAxioms
            (Printed.targetAveragedContourReverse printed input coarse fine)
            (Average.inverse averageAxioms
              (targetGauge gauge coarse)))

    reversedCoarseBondValueCovariant : ∀ gauge input coarse →
      Printed.reversedCoarseBondValue printed
        (gaugeAction gauge input) coarse
      ≡ Average.multiply averageAxioms (targetGauge gauge coarse)
          (Average.multiply averageAxioms
            (Printed.reversedCoarseBondValue printed input coarse)
            (Average.inverse averageAxioms
              (sourceGauge gauge coarse)))

    coarseBondValueCovariant : ∀ gauge input coarse →
      Printed.coarseBondValue printed (gaugeAction gauge input) coarse
      ≡ Average.multiply averageAxioms (sourceGauge gauge coarse)
          (Average.multiply averageAxioms
            (Printed.coarseBondValue printed input coarse)
            (Average.inverse averageAxioms
              (targetGauge gauge coarse)))

open Equation012GaugeActionData public

CoarseAnchoredAt :
  ∀ {Field Gauge CoarseBond FineSite Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    {printed : Printed.PrintedCMP109Equation012Data
      Field CoarseBond FineSite Group Lie Scalar} →
  Equation012GaugeActionData
    Field Gauge CoarseBond FineSite Group Lie Scalar averageAxioms printed →
  Gauge → CoarseBond → Set
CoarseAnchoredAt {averageAxioms = averageAxioms} dataSet gauge coarse =
  (sourceGauge dataSet gauge coarse ≡ Average.identity averageAxioms)
  × (targetGauge dataSet gauge coarse ≡ Average.identity averageAxioms)
  where
    infixr 4 _×_
    record _×_ (A B : Set) : Set where
      constructor _,_
      field first : A
            second : B

------------------------------------------------------------------------
-- Relative-loop covariance and exact coarse-anchored invariance.
------------------------------------------------------------------------

equation012RelativeProductGaugeCovariant :
  ∀ {Field Gauge CoarseBond FineSite Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    (laws : CMP109GroupLaws averageAxioms)
    {printed : Printed.PrintedCMP109Equation012Data
      Field CoarseBond FineSite Group Lie Scalar}
    (dataSet : Equation012GaugeActionData
      Field Gauge CoarseBond FineSite Group Lie Scalar averageAxioms printed)
    gauge input coarse fine →
  Printed.printedEquation012RelativeProduct printed
    (gaugeAction dataSet gauge input) coarse fine
  ≡ Average.multiply averageAxioms (sourceGauge dataSet gauge coarse)
      (Average.multiply averageAxioms
        (Printed.printedEquation012RelativeProduct printed input coarse fine)
        (Average.inverse averageAxioms (sourceGauge dataSet gauge coarse)))
equation012RelativeProductGaugeCovariant
    {averageAxioms = averageAxioms} laws {printed = printed}
    dataSet gauge input coarse fine
  rewrite sourceAveragedContourCovariant dataSet gauge input coarse fine
        | crossingValueCovariant dataSet gauge input coarse fine
        | targetAveragedContourReverseCovariant dataSet gauge input coarse fine
        | reversedCoarseBondValueCovariant dataSet gauge input coarse =
  fourFactorGaugeTelescope laws
    (sourceGauge dataSet gauge coarse)
    (sourceFineGauge dataSet gauge coarse fine)
    (targetFineGauge dataSet gauge coarse fine)
    (targetGauge dataSet gauge coarse)
    (Printed.sourceAveragedContour printed input coarse fine)
    (Printed.crossingValue printed input coarse fine)
    (Printed.targetAveragedContourReverse printed input coarse fine)
    (Printed.reversedCoarseBondValue printed input coarse)

relativeProductFixedBySourceAnchor :
  ∀ {Field Gauge CoarseBond FineSite Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    (laws : CMP109GroupLaws averageAxioms)
    {printed : Printed.PrintedCMP109Equation012Data
      Field CoarseBond FineSite Group Lie Scalar}
    (dataSet : Equation012GaugeActionData
      Field Gauge CoarseBond FineSite Group Lie Scalar averageAxioms printed)
    gauge input coarse fine →
  sourceGauge dataSet gauge coarse ≡ Average.identity averageAxioms →
  Printed.printedEquation012RelativeProduct printed
    (gaugeAction dataSet gauge input) coarse fine
  ≡ Printed.printedEquation012RelativeProduct printed input coarse fine
relativeProductFixedBySourceAnchor
    {averageAxioms = averageAxioms} laws {printed = printed}
    dataSet gauge input coarse fine sourceAnchored =
  trans
    (equation012RelativeProductGaugeCovariant
      laws dataSet gauge input coarse fine)
    (trans
      (cong
        (λ sourceValue →
          Average.multiply averageAxioms sourceValue
            (Average.multiply averageAxioms
              (Printed.printedEquation012RelativeProduct printed input coarse fine)
              (Average.inverse averageAxioms sourceValue)))
        sourceAnchored)
      (conjugationByIdentity laws
        (Printed.printedEquation012RelativeProduct printed input coarse fine)))

sumListCong :
  ∀ {A Scalar : Set}
    zero add (values : List A)
    (left right : A → Scalar) →
  (∀ value → left value ≡ right value) →
  Printed.sumList A Scalar zero add values left
  ≡ Printed.sumList A Scalar zero add values right
sumListCong zero add [] left right pointwise = refl
sumListCong zero add (value ∷ values) left right pointwise =
  trans
    (cong
      (λ selected → add selected
        (Printed.sumList _ _ zero add values left))
      (pointwise value))
    (cong
      (add (right value))
      (sumListCong zero add values left right pointwise))

equation012LieAverageFixedBySourceAnchor :
  ∀ {Field Gauge CoarseBond FineSite Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    (laws : CMP109GroupLaws averageAxioms)
    {printed : Printed.PrintedCMP109Equation012Data
      Field CoarseBond FineSite Group Lie Scalar}
    (dataSet : Equation012GaugeActionData
      Field Gauge CoarseBond FineSite Group Lie Scalar averageAxioms printed)
    gauge input coarse →
  sourceGauge dataSet gauge coarse ≡ Average.identity averageAxioms →
  Printed.printedEquation012LieAverage printed
    (gaugeAction dataSet gauge input) coarse
  ≡ Printed.printedEquation012LieAverage printed input coarse
equation012LieAverageFixedBySourceAnchor
    laws {printed = printed} dataSet gauge input coarse sourceAnchored =
  sumListCong
    (Printed.zeroLie printed)
    (Printed.addLie printed)
    (Printed.blockSites printed coarse)
    (λ fine →
      Printed.scaleLie printed (Printed.blockWeight printed coarse)
        (Printed.antiHermitianLogCoordinate printed
          (Printed.printedEquation012RelativeProduct printed
            (gaugeAction dataSet gauge input) coarse fine)))
    (λ fine →
      Printed.scaleLie printed (Printed.blockWeight printed coarse)
        (Printed.antiHermitianLogCoordinate printed
          (Printed.printedEquation012RelativeProduct printed input coarse fine)))
    (λ fine →
      cong
        (Printed.scaleLie printed (Printed.blockWeight printed coarse))
        (cong
          (Printed.antiHermitianLogCoordinate printed)
          (relativeProductFixedBySourceAnchor
            laws dataSet gauge input coarse fine sourceAnchored)))

coarseBondFixedByAnchors :
  ∀ {Field Gauge CoarseBond FineSite Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    (laws : CMP109GroupLaws averageAxioms)
    {printed : Printed.PrintedCMP109Equation012Data
      Field CoarseBond FineSite Group Lie Scalar}
    (dataSet : Equation012GaugeActionData
      Field Gauge CoarseBond FineSite Group Lie Scalar averageAxioms printed)
    gauge input coarse →
  sourceGauge dataSet gauge coarse ≡ Average.identity averageAxioms →
  targetGauge dataSet gauge coarse ≡ Average.identity averageAxioms →
  Printed.coarseBondValue printed (gaugeAction dataSet gauge input) coarse
  ≡ Printed.coarseBondValue printed input coarse
coarseBondFixedByAnchors
    {averageAxioms = averageAxioms} laws {printed = printed}
    dataSet gauge input coarse sourceAnchored targetAnchored =
  trans
    (coarseBondValueCovariant dataSet gauge input coarse)
    (trans
      (cong
        (λ sourceValue →
          Average.multiply averageAxioms sourceValue
            (Average.multiply averageAxioms
              (Printed.coarseBondValue printed input coarse)
              (Average.inverse averageAxioms
                (targetGauge dataSet gauge coarse))))
        sourceAnchored)
      (trans
        (cong
          (Average.multiply averageAxioms (Average.identity averageAxioms))
          (trans
            (cong
              (Average.multiply averageAxioms
                (Printed.coarseBondValue printed input coarse))
              (trans
                (cong (Average.inverse averageAxioms) targetAnchored)
                (inverseIdentity laws)))
            (multiplyIdentityRight laws
              (Printed.coarseBondValue printed input coarse))))
        (multiplyIdentityLeft laws
          (Printed.coarseBondValue printed input coarse))))

equation012MapFixedByCoarseAnchoredGauge :
  ∀ {Field Gauge CoarseBond FineSite Group Lie Scalar}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    (laws : CMP109GroupLaws averageAxioms)
    {printed : Printed.PrintedCMP109Equation012Data
      Field CoarseBond FineSite Group Lie Scalar}
    (dataSet : Equation012GaugeActionData
      Field Gauge CoarseBond FineSite Group Lie Scalar averageAxioms printed)
    gauge input coarse →
  sourceGauge dataSet gauge coarse ≡ Average.identity averageAxioms →
  targetGauge dataSet gauge coarse ≡ Average.identity averageAxioms →
  Printed.printedEquation012Map printed
    (gaugeAction dataSet gauge input) coarse
  ≡ Printed.printedEquation012Map printed input coarse
equation012MapFixedByCoarseAnchoredGauge
    {averageAxioms = averageAxioms} laws {printed = printed}
    dataSet gauge input coarse sourceAnchored targetAnchored =
  trans
    (cong
      (λ selectedLie →
        Average.multiply averageAxioms
          (Printed.outerExponential printed selectedLie)
          (Printed.coarseBondValue printed
            (gaugeAction dataSet gauge input) coarse))
      (equation012LieAverageFixedBySourceAnchor
        laws dataSet gauge input coarse sourceAnchored))
    (cong
      (Average.multiply averageAxioms
        (Printed.outerExponential printed
          (Printed.printedEquation012LieAverage printed input coarse)))
      (coarseBondFixedByAnchors
        laws dataSet gauge input coarse sourceAnchored targetAnchored))

cmp109Equation012InternalGaugeTelescopeLevel : ProofLevel
cmp109Equation012InternalGaugeTelescopeLevel = machineChecked

cmp109Equation012CoarseAnchoredInvarianceLevel : ProofLevel
cmp109Equation012CoarseAnchoredInvarianceLevel = machineChecked
