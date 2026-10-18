{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact where

------------------------------------------------------------------------
-- B / ROUND444: MAKE THE PREFERRED R429 TERM CARRIER ITSELF TWICE-MARKED.
--
-- R429 already makes the CMP109 four-stage factor layout canonical, but its
-- Term carrier is abstract.  R435 consequently had to ask afterward that every
-- retained term carries the two selected source links and that every retained
-- fibre is nonempty.
--
-- Here the preferred constructor is strengthened at the correct place:
--
--   Term = TwiceMarkedTerm RawTerm CarriesLink leftMark rightMark
--   termsWithCommonY Y = selectedHead Y :: selectedTail Y.
--
-- Hence both source marks and retained-fibre nonemptiness are structural.
-- The remaining B1 content is only the literal source construction of the raw
-- twice-differentiated term together with its canonical R410 path replay and
-- scalarization.  The remaining B3/B4 source coordinates are unchanged.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact as Marked
import DASHI.Physics.YangMills.BalabanCMP109FourStageOperatorFactorRound407Exact as R407
import DASHI.Physics.YangMills.BalabanCMP99MarkedStageDifferenceRound408Exact as R408
import DASHI.Physics.YangMills.BalabanCMP99SingleMarkedFourStageRound409Exact as R409
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedSupportRound434Exact as R434
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFourStageR406Round429Exact as R429
import DASHI.Physics.YangMills.BalabanCMP116CanonicalSelectedBSourceRound435Exact as R435

record CanonicalTwiceMarkedFourStageData
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    : Set₁ where
  field
    leftObservable rightObservable : R318.SourceDirection base
    leftJ rightJ : R318.SourceDirection base
    leftJIsObservableIndexed :
      leftJ ≡ Cumulant.sourceDirectionOf (R318.meaning base) leftObservable
    rightJIsObservableIndexed :
      rightJ ≡ Cumulant.sourceDirectionOf (R318.meaning base) rightObservable

    leftMark rightMark : Support.Link

    RawTerm : Set
    CarriesLink : RawTerm → Support.Link → Set

    DecouplingBoundaryAssignment : Set
    selectedDecouplingBoundary : DecouplingBoundaryAssignment

    Domain Operator : Set
    localizedDomains : List Domain

    selectedHead :
      Domain →
      R434.TwiceMarkedTerm RawTerm CarriesLink leftMark rightMark
    selectedTail :
      Domain →
      List (R434.TwiceMarkedTerm RawTerm CarriesLink leftMark rightMark)

    differentiatedTerm :
      Domain →
      R434.TwiceMarkedTerm RawTerm CarriesLink leftMark rightMark →
      ℝ
    commonYBoundaryIntegrand commonYShell : Domain → ℝ
    selectedBoundaryIntegrand selectedConnectingShell : ℝ

    operatorAlgebra : Marked.MarkedOperatorNormAlgebra Operator ℝ
    operatorOrderToReal : ∀ {lower upper} →
      Marked.LessEqual operatorAlgebra lower upper →
      lower ≤ℝ upper

    canonicalPathReplay :
      Domain →
      R434.TwiceMarkedTerm RawTerm CarriesLink leftMark rightMark →
      R410.CanonicalPathMarkedCMP109Replay Operator ℝ

    replayAlgebraIsOperatorAlgebra :
      ∀ domain term →
      R408.telescopeAlgebra
        (R410.stageDifference (canonicalPathReplay domain term))
      ≡ operatorAlgebra

    -- This is the genuine B1 source/scalar-response theorem on the literal
    -- twice-marked term.  No separate R406/R410 layout weld remains afterward.
    differentiatedTermAbsoluteIsCanonicalProductDifferenceNorm :
      ∀ domain term →
      absℝ (differentiatedTerm domain term)
      ≡
      Marked.operatorNorm operatorAlgebra
        (Marked.difference operatorAlgebra
          (Marked.operatorProduct operatorAlgebra
            (R407.stageOperator
              (R407.before
                (R408.ordinaryPair
                  (R410.stageDifference
                    (canonicalPathReplay domain term)))))
            R407.cmp109DerivativeStages)
          (Marked.operatorProduct operatorAlgebra
            (R407.stageOperator
              (R407.after
                (R408.ordinaryPair
                  (R410.stageDifference
                    (canonicalPathReplay domain term)))))
            R407.cmp109DerivativeStages))

    selectedBoundaryIsCommonYSum :
      selectedBoundaryIntegrand ≡
      Resum.sumℝ commonYBoundaryIntegrand localizedDomains

    commonYBoundaryIsTermSum :
      ∀ domain →
      commonYBoundaryIntegrand domain ≡
      Resum.sumℝ
        (differentiatedTerm domain)
        (selectedHead domain ∷ selectedTail domain)

    differentiatedMajorantsBelowCommonYShell :
      ∀ domain →
      Resum.sumℝ
        (λ term →
          Marked.markedProductMajorant operatorAlgebra
            (R407.ordinaryStageMajorant
              (R408.ordinaryPair
                (R410.stageDifference (canonicalPathReplay domain term))))
            (R409.stageMarkedMajorant
              (R410.stageDifference (canonicalPathReplay domain term))
              (R410.canonicalSingleChangedAgreement
                (canonicalPathReplay domain term)))
            R407.cmp109DerivativeStages)
        (selectedHead domain ∷ selectedTail domain)
      ≤ℝ commonYShell domain

    commonYShellsBelowSelectedConnectingShell :
      Resum.sumℝ commonYShell localizedDomains
      ≤ℝ selectedConnectingShell

    source :
      Source.PublishedCMP116Equation126129RateSplit Domain

    sourceDomainsAreLiteralDomains :
      Source.localizedDomains source ≡ localizedDomains

    sourceFixedYShellIsLiteralCommonYShell :
      ∀ domain →
      Source.fixedYShell source domain ≡ commonYShell domain

open CanonicalTwiceMarkedFourStageData public

-- Legacy compatibility only.  CMP116 (1.29) uses the domain-dependent d_k(Y),
-- so the preferred Goal-1 path must not assume this global equality.
record LegacyGlobalTreeMetricAttachment
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (data :
      CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    : Set₁ where
  field
    sourceTreeDistanceIsGlobalSupportTree :
      ∀ domain →
      Source.sourceTreeDistance (source data) domain ≡ Graph.ymTreeEdgeCount

open LegacyGlobalTreeMetricAttachment public

Term :
  ∀ {Measure TestObservable dataSet extension base} →
  CanonicalTwiceMarkedFourStageData
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} base →
  Set
Term data =
  R434.TwiceMarkedTerm
    (RawTerm data) (CarriesLink data) (leftMark data) (rightMark data)

termsWithCommonY :
  ∀ {Measure TestObservable dataSet extension base}
    (data :
      CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base) →
  Domain data → List (Term data)
termsWithCommonY data domain =
  selectedHead data domain ∷ selectedTail data domain

asR429 :
  ∀ {Measure TestObservable dataSet extension}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension} →
  (data :
    CanonicalTwiceMarkedFourStageData
      {Measure = Measure} {TestObservable = TestObservable}
      {dataSet = dataSet} {extension = extension} base) →
  R429.CanonicalFourStageR406Data base
asR429 data = record
  { R429.CanonicalFourStageR406Data.leftObservable = leftObservable data
  ; R429.CanonicalFourStageR406Data.rightObservable = rightObservable data
  ; R429.CanonicalFourStageR406Data.leftJ = leftJ data
  ; R429.CanonicalFourStageR406Data.rightJ = rightJ data
  ; R429.CanonicalFourStageR406Data.leftJIsObservableIndexed =
      leftJIsObservableIndexed data
  ; R429.CanonicalFourStageR406Data.rightJIsObservableIndexed =
      rightJIsObservableIndexed data
  ; R429.CanonicalFourStageR406Data.DecouplingBoundaryAssignment =
      DecouplingBoundaryAssignment data
  ; R429.CanonicalFourStageR406Data.selectedDecouplingBoundary =
      selectedDecouplingBoundary data
  ; R429.CanonicalFourStageR406Data.Term = Term data
  ; R429.CanonicalFourStageR406Data.Domain = Domain data
  ; R429.CanonicalFourStageR406Data.Operator = Operator data
  ; R429.CanonicalFourStageR406Data.localizedDomains = localizedDomains data
  ; R429.CanonicalFourStageR406Data.termsWithCommonY = termsWithCommonY data
  ; R429.CanonicalFourStageR406Data.differentiatedTerm = differentiatedTerm data
  ; R429.CanonicalFourStageR406Data.commonYBoundaryIntegrand =
      commonYBoundaryIntegrand data
  ; R429.CanonicalFourStageR406Data.commonYShell = commonYShell data
  ; R429.CanonicalFourStageR406Data.selectedBoundaryIntegrand =
      selectedBoundaryIntegrand data
  ; R429.CanonicalFourStageR406Data.selectedConnectingShell =
      selectedConnectingShell data
  ; R429.CanonicalFourStageR406Data.operatorAlgebra = operatorAlgebra data
  ; R429.CanonicalFourStageR406Data.operatorOrderToReal = operatorOrderToReal data
  ; R429.CanonicalFourStageR406Data.canonicalPathReplay = canonicalPathReplay data
  ; R429.CanonicalFourStageR406Data.replayAlgebraIsOperatorAlgebra =
      replayAlgebraIsOperatorAlgebra data
  ; R429.CanonicalFourStageR406Data.differentiatedTermAbsoluteIsCanonicalProductDifferenceNorm =
      differentiatedTermAbsoluteIsCanonicalProductDifferenceNorm data
  ; R429.CanonicalFourStageR406Data.selectedBoundaryIsCommonYSum =
      selectedBoundaryIsCommonYSum data
  ; R429.CanonicalFourStageR406Data.commonYBoundaryIsTermSum =
      commonYBoundaryIsTermSum data
  ; R429.CanonicalFourStageR406Data.differentiatedMajorantsBelowCommonYShell =
      differentiatedMajorantsBelowCommonYShell data
  ; R429.CanonicalFourStageR406Data.commonYShellsBelowSelectedConnectingShell =
      commonYShellsBelowSelectedConnectingShell data
  }

asR435Legacy :
  ∀ {Measure TestObservable dataSet extension}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (data :
      CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base) →
  LegacyGlobalTreeMetricAttachment data →
  R435.CanonicalSelectedBSource (asR429 data)
asR435Legacy data legacy = record
  { R435.CanonicalSelectedBSource.leftMark = leftMark data
  ; R435.CanonicalSelectedBSource.rightMark = rightMark data
  ; R435.CanonicalSelectedBSource.CarriesLink =
      λ term link → CarriesLink data (R434.rawTerm term) link
  ; R435.CanonicalSelectedBSource.everySelectedTermCarriesLeft =
      λ domain term membership → R434.carriesLeft term
  ; R435.CanonicalSelectedBSource.everySelectedTermCarriesRight =
      λ domain term membership → R434.carriesRight term
  ; R435.CanonicalSelectedBSource.selectedHead = selectedHead data
  ; R435.CanonicalSelectedBSource.selectedTail = selectedTail data
  ; R435.CanonicalSelectedBSource.retainedFibreIsHeadTail =
      λ domain → refl
  ; R435.CanonicalSelectedBSource.source = source data
  ; R435.CanonicalSelectedBSource.sourceDomainsAreLiteralDomains =
      sourceDomainsAreLiteralDomains data
  ; R435.CanonicalSelectedBSource.sourceTreeDistanceIsCanonicalSupportTree =
      sourceTreeDistanceIsGlobalSupportTree legacy
  ; R435.CanonicalSelectedBSource.sourceFixedYShellIsLiteralCommonYShell =
      sourceFixedYShellIsLiteralCommonYShell data
  }

selectedHeadBelongs :
  ∀ {Measure TestObservable dataSet extension base}
    (data :
      CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    domain →
  selectedHead data domain ∈ termsWithCommonY data domain
selectedHeadBelongs data domain = here refl

selectedHeadCarriesLeft :
  ∀ {Measure TestObservable dataSet extension base}
    (data :
      CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    domain →
  CarriesLink data
    (R434.rawTerm (selectedHead data domain))
    (leftMark data)
selectedHeadCarriesLeft data domain =
  R434.carriesLeft (selectedHead data domain)

selectedHeadCarriesRight :
  ∀ {Measure TestObservable dataSet extension base}
    (data :
      CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    domain →
  CarriesLink data
    (R434.rawTerm (selectedHead data domain))
    (rightMark data)
selectedHeadCarriesRight data domain =
  R434.carriesRight (selectedHead data domain)

round444BothMarksStructuralLevel : ProofLevel
round444BothMarksStructuralLevel = machineChecked

round444NonemptyFibreStructuralLevel : ProofLevel
round444NonemptyFibreStructuralLevel = machineChecked

round444R429CompilerLevel : ProofLevel
round444R429CompilerLevel = machineChecked

round444R435LegacyAdapterLevel : ProofLevel
round444R435LegacyAdapterLevel = machineChecked

round444GlobalTreeMetricNotPreferredLevel : ProofLevel
round444GlobalTreeMetricNotPreferredLevel = conditional

-- B2 is no longer an independent proof obligation on this preferred carrier:
-- both source marks and retained-fibre nonemptiness are constructor data.
--
-- The live B1 theorem is now exactly the source construction of these literal
-- twice-marked raw terms plus canonicalPathReplay/scalarization.  B3/B4 must
-- use the domain-dependent Source.sourceTreeDistance.  The old global
-- ymTreeEdgeCount equality is available only through LegacyGlobalTreeMetricAttachment.
literalRound444TwiceDifferentiatedTermConstructionAndScalarizationLevel : ProofLevel
literalRound444TwiceDifferentiatedTermConstructionAndScalarizationLevel =
  conditional
