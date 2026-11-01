module DASHI.Promotion.StandardModelFirstPrinciplesGapIndex where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.StandardModelFiniteAnomalyHyperchargeCheck as Anomaly
import DASHI.Promotion.StandardModelFiniteRepresentationNarrowing as Narrow
import DASHI.Promotion.StandardModelTerminalObligations as Terminal

------------------------------------------------------------------------
-- Standard Model first-principles gap index.
--
-- This module records why a broad "Standard Model from first principles"
-- claim is not currently promotable.  It preserves the positive finite
-- surfaces already available in the repository: finite gauge-name narrowing,
-- finite one-generation representation targets, finite hypercharge rows, and
-- finite anomaly-balance rows.

data FirstPrinciplesSMTarget : Set where
  gaugeGroupUniquenessTarget :
    FirstPrinciplesSMTarget

  representationUniquenessTarget :
    FirstPrinciplesSMTarget

  generationCountTarget :
    FirstPrinciplesSMTarget

  yukawaHierarchyTarget :
    FirstPrinciplesSMTarget

  higgsSectorTarget :
    FirstPrinciplesSMTarget

  ckmTarget :
    FirstPrinciplesSMTarget

  pmnsTarget :
    FirstPrinciplesSMTarget

  gaugeCouplingsRunningTarget :
    FirstPrinciplesSMTarget

  qftObservableBridgeTarget :
    FirstPrinciplesSMTarget

  empiricalAuthorityTarget :
    FirstPrinciplesSMTarget

targetLabel :
  FirstPrinciplesSMTarget →
  String
targetLabel gaugeGroupUniquenessTarget =
  "gauge-group uniqueness"
targetLabel representationUniquenessTarget =
  "representation uniqueness"
targetLabel generationCountTarget =
  "generation count"
targetLabel yukawaHierarchyTarget =
  "Yukawa hierarchy"
targetLabel higgsSectorTarget =
  "Higgs sector"
targetLabel ckmTarget =
  "CKM"
targetLabel pmnsTarget =
  "PMNS"
targetLabel gaugeCouplingsRunningTarget =
  "gauge couplings/running"
targetLabel qftObservableBridgeTarget =
  "QFT observable bridge"
targetLabel empiricalAuthorityTarget =
  "empirical authority"

data GapKind : Set where
  proofGap :
    GapKind

  authorityGap :
    GapKind

  bridgeGap :
    GapKind

  empiricalGap :
    GapKind

data FiniteSurfaceStatus : Set where
  finiteSurfacePreserved :
    FiniteSurfaceStatus

  finiteSurfacePartial :
    FiniteSurfaceStatus

  noFiniteSurface :
    FiniteSurfaceStatus

record FirstPrinciplesGapRow : Set where
  field
    target :
      FirstPrinciplesSMTarget

    label :
      String

    labelIsCanonical :
      label ≡ targetLabel target

    gapKind :
      GapKind

    finiteSurfaceStatus :
      FiniteSurfaceStatus

    positiveFiniteInputs :
      List String

    missingFirstPrinciplesEvidence :
      List String

    consumedPromotionObligations :
      List String

    authoritySurface :
      String

    broadClaimPromoted :
      Bool

    broadClaimPromotedIsFalse :
      broadClaimPromoted ≡ false

    rowBoundary :
      String

open FirstPrinciplesGapRow public

mkGapRow :
  FirstPrinciplesSMTarget →
  GapKind →
  FiniteSurfaceStatus →
  List String →
  List String →
  List String →
  String →
  String →
  FirstPrinciplesGapRow
mkGapRow target kind finiteStatus positives missing obligations authority
  boundary =
  record
    { target = target
    ; label = targetLabel target
    ; labelIsCanonical = refl
    ; gapKind = kind
    ; finiteSurfaceStatus = finiteStatus
    ; positiveFiniteInputs = positives
    ; missingFirstPrinciplesEvidence = missing
    ; consumedPromotionObligations = obligations
    ; authoritySurface = authority
    ; broadClaimPromoted = false
    ; broadClaimPromotedIsFalse = refl
    ; rowBoundary = boundary
    }

gaugeGroupUniquenessGapRow :
  FirstPrinciplesGapRow
gaugeGroupUniquenessGapRow =
  mkGapRow
    gaugeGroupUniquenessTarget
    proofGap
    finiteSurfacePreserved
    ( "three finite gauge-name rows: U1Y, SU2L, SU3c"
    ∷ "p2/p3/p5 prime-surface association"
    ∷ "finite SM gauge-group candidate receipts"
    ∷ []
    )
    ( "unique continuous compact gauge group theorem"
    ∷ "finite-to-continuous U1Y, SU2L, and SU3c bridges"
    ∷ "proof that no competing first-principles gauge group remains"
    ∷ []
    )
    ( "continuous SU3 x SU2 x U1 bridge"
    ∷ "exact SM match token boundary"
    ∷ []
    )
    "DASHI.Promotion.StandardModelFiniteRepresentationNarrowing"
    "finite gauge names are preserved; continuous uniqueness is not promoted"

representationUniquenessGapRow :
  FirstPrinciplesGapRow
representationUniquenessGapRow =
  mkGapRow
    representationUniquenessTarget
    proofGap
    finiteSurfacePreserved
    ( "five one-generation representation target rows"
    ∷ "six finite all-left-handed hypercharge multiplet rows"
    ∷ "four finite anomaly-balance rows"
    ∷ []
    )
    ( "physical irrep reconstruction theorem"
    ∷ "uniqueness of the SM chiral representation table"
    ∷ "carrier-to-continuous representation functor equivalence"
    ∷ []
    )
    ( "representation table"
    ∷ "hypercharge convention"
    ∷ "anomaly cancellation"
    ∷ []
    )
    "DASHI.Promotion.StandardModelFiniteAnomalyHyperchargeCheck"
    "finite representation and anomaly checks are positive; irrep uniqueness remains open"

generationCountGapRow :
  FirstPrinciplesGapRow
generationCountGapRow =
  mkGapRow
    generationCountTarget
    proofGap
    finiteSurfacePartial
    ( "one-generation finite target surface"
    ∷ "physical table total Weyl count recorded in finite hypercharge check"
    ∷ []
    )
    ( "first-principles proof of exactly three generations"
    ∷ "neutrino convention and right-handed-neutrino boundary"
    ∷ "proof that generation replication is forced rather than inserted"
    ∷ []
    )
    ( "representation table"
    ∷ "physical sector map"
    ∷ []
    )
    "DASHI.Promotion.StandardModelTerminalObligations"
    "the finite surface checks one-generation bookkeeping, not a derivation of three generations"

yukawaHierarchyGapRow :
  FirstPrinciplesGapRow
yukawaHierarchyGapRow =
  mkGapRow
    yukawaHierarchyTarget
    authorityGap
    noFiniteSurface
    ( "none: Yukawa values are not derived by the finite anomaly surface"
    ∷ []
    )
    ( "Yukawa matrices or masses from first principles"
    ∷ "hierarchy, phases, and basis conventions"
    ∷ "versioned PDG authority when using measured inputs"
    ∷ []
    )
    ( "Higgs Yukawa CKM PMNS PDG authority"
    ∷ "physical sector map"
    ∷ []
    )
    "DASHI.Constants.Registry"
    "Yukawa hierarchy is neither finite-derived nor authority-accepted"

higgsSectorGapRow :
  FirstPrinciplesGapRow
higgsSectorGapRow =
  mkGapRow
    higgsSectorTarget
    proofGap
    noFiniteSurface
    ( "none: finite gauge and anomaly rows do not construct a Higgs potential"
    ∷ []
    )
    ( "Higgs representation and potential from first principles"
    ∷ "electroweak symmetry-breaking receipt"
    ∷ "Higgs mass and vacuum expectation convention"
    ∷ []
    )
    ( "Higgs Yukawa CKM PMNS PDG authority"
    ∷ "physical sector map"
    ∷ []
    )
    "DASHI.Promotion.StandardModelTerminalObligations"
    "Higgs-sector data are terminal obligations, not promoted first-principles facts"

ckmGapRow :
  FirstPrinciplesGapRow
ckmGapRow =
  mkGapRow
    ckmTarget
    authorityGap
    noFiniteSurface
    ( "none: finite representation rows do not determine quark mixing"
    ∷ []
    )
    ( "CKM matrix derivation or accepted PDG token"
    ∷ "phase convention and uncertainty policy"
    ∷ "binding from quark Yukawa sector to observables"
    ∷ []
    )
    ( "Higgs Yukawa CKM PMNS PDG authority"
    ∷ "empirical observable bridge"
    ∷ []
    )
    "DASHI.Constants.Registry"
    "CKM remains an authority/proof gap"

pmnsGapRow :
  FirstPrinciplesGapRow
pmnsGapRow =
  mkGapRow
    pmnsTarget
    authorityGap
    noFiniteSurface
    ( "none: finite lepton rows do not determine neutrino mixing"
    ∷ []
    )
    ( "PMNS matrix derivation or accepted authority token"
    ∷ "neutrino mass ordering and convention"
    ∷ "Dirac/Majorana boundary"
    ∷ []
    )
    ( "Higgs Yukawa CKM PMNS PDG authority"
    ∷ "physical sector map"
    ∷ []
    )
    "DASHI.Constants.Registry"
    "PMNS remains an authority/proof gap"

gaugeCouplingsRunningGapRow :
  FirstPrinciplesGapRow
gaugeCouplingsRunningGapRow =
  mkGapRow
    gaugeCouplingsRunningTarget
    authorityGap
    finiteSurfacePartial
    ( "finite gauge-name rows identify U1Y, SU2L, and SU3c labels"
    ∷ []
    )
    ( "physical normalization and measured coupling constants"
    ∷ "renormalization scheme and scale convention"
    ∷ "running law bridge to empirical comparison"
    ∷ []
    )
    ( "gauge normalization"
    ∷ "empirical observable bridge"
    ∷ []
    )
    "DASHI.Constants.Registry"
    "finite gauge labels do not determine measured couplings or running"

qftObservableBridgeGapRow :
  FirstPrinciplesGapRow
qftObservableBridgeGapRow =
  mkGapRow
    qftObservableBridgeTarget
    bridgeGap
    noFiniteSurface
    ( "finite anomaly numerators are checked as internal consistency rows"
    ∷ []
    )
    ( "observable definition and projection law"
    ∷ "comparison, covariance, calibration, and holdout receipts"
    ∷ "QFT-to-runtime observable bridge"
    ∷ []
    )
    ( "empirical observable bridge"
    ∷ "physical sector map"
    ∷ []
    )
    "DASHI.Constants.Registry"
    "finite internal checks are not empirical QFT observables"

empiricalAuthorityGapRow :
  FirstPrinciplesGapRow
empiricalAuthorityGapRow =
  mkGapRow
    empiricalAuthorityTarget
    empiricalGap
    noFiniteSurface
    ( "none: authority is an external input surface"
    ∷ []
    )
    ( "accepted provider authority token"
    ∷ "source checksum, access date, uncertainty, and rounding policy"
    ∷ "consumer receipt proving values were loaded under policy"
    ∷ []
    )
    ( "Higgs Yukawa CKM PMNS PDG authority"
    ∷ "empirical observable bridge"
    ∷ []
    )
    "DASHI.Constants.Registry"
    "empirical authority is explicitly not accepted in the current registry receipts"

canonicalFirstPrinciplesGapRows :
  List FirstPrinciplesGapRow
canonicalFirstPrinciplesGapRows =
  gaugeGroupUniquenessGapRow
  ∷ representationUniquenessGapRow
  ∷ generationCountGapRow
  ∷ yukawaHierarchyGapRow
  ∷ higgsSectorGapRow
  ∷ ckmGapRow
  ∷ pmnsGapRow
  ∷ gaugeCouplingsRunningGapRow
  ∷ qftObservableBridgeGapRow
  ∷ empiricalAuthorityGapRow
  ∷ []

data FalseBroadPromotionGuard : Set where
  finiteSurfaceIsNotFirstPrinciplesGuard :
    FalseBroadPromotionGuard

  missingContinuousGaugeUniquenessGuard :
    FalseBroadPromotionGuard

  missingRepresentationUniquenessGuard :
    FalseBroadPromotionGuard

  missingGenerationAndYukawaGuard :
    FalseBroadPromotionGuard

  missingHiggsMixingAndCouplingAuthorityGuard :
    FalseBroadPromotionGuard

  missingQFTObservableAndEmpiricalAuthorityGuard :
    FalseBroadPromotionGuard

canonicalFalseBroadPromotionGuards :
  List FalseBroadPromotionGuard
canonicalFalseBroadPromotionGuards =
  finiteSurfaceIsNotFirstPrinciplesGuard
  ∷ missingContinuousGaugeUniquenessGuard
  ∷ missingRepresentationUniquenessGuard
  ∷ missingGenerationAndYukawaGuard
  ∷ missingHiggsMixingAndCouplingAuthorityGuard
  ∷ missingQFTObservableAndEmpiricalAuthorityGuard
  ∷ []

listCount :
  {A : Set} →
  List A →
  Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

record StandardModelFirstPrinciplesGapIndexReceipt : Setω where
  field
    finiteRepresentationNarrowingReceipt :
      Narrow.StandardModelFiniteRepresentationNarrowingReceipt

    finiteAnomalyHyperchargeCheckReceipt :
      Anomaly.FiniteSMAnomalyHyperchargeCheckReceipt

    terminalObligationReceipt :
      Terminal.StandardModelTerminalPromotionObligationReceipt

    physicsRegistryReceipt :
      Registry.PhysicsAdapterKnownInputsReferenceReceipt

    authorityPolicyReceipt :
      Registry.AuthorityConsumptionPolicyReceipt

    empiricalRuntimeReceipt :
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt

    gapRows :
      List FirstPrinciplesGapRow

    gapRowsAreCanonical :
      gapRows ≡ canonicalFirstPrinciplesGapRows

    firstPrinciplesGapRowCount :
      Nat

    firstPrinciplesGapRowCountIsTen :
      firstPrinciplesGapRowCount ≡ 10

    falseBroadPromotionGuards :
      List FalseBroadPromotionGuard

    falseBroadPromotionGuardsAreCanonical :
      falseBroadPromotionGuards ≡ canonicalFalseBroadPromotionGuards

    falseBroadPromotionGuardCount :
      Nat

    falseBroadPromotionGuardCountIsSix :
      falseBroadPromotionGuardCount ≡ 6

    finiteGaugeNameRowCount :
      Nat

    finiteGaugeNameRowCountIsThree :
      finiteGaugeNameRowCount ≡ 3

    finiteRepresentationTargetCount :
      Nat

    finiteRepresentationTargetCountIsFive :
      finiteRepresentationTargetCount ≡ 5

    finiteHyperchargeMultipletRowCount :
      Nat

    finiteHyperchargeMultipletRowCountIsSix :
      finiteHyperchargeMultipletRowCount ≡ 6

    finiteAnomalyBalanceRowCount :
      Nat

    finiteAnomalyBalanceRowCountIsFour :
      finiteAnomalyBalanceRowCount ≡ 4

    terminalSMObligationCount :
      Nat

    terminalSMObligationCountIsNine :
      terminalSMObligationCount ≡ 9

    finiteRepresentationContentNarrowed :
      Bool

    finiteRepresentationContentNarrowedIsTrue :
      finiteRepresentationContentNarrowed ≡ true

    finiteHyperchargeRowsChecked :
      Bool

    finiteHyperchargeRowsCheckedIsTrue :
      finiteHyperchargeRowsChecked ≡ true

    finiteAnomalyBalanceChecked :
      Bool

    finiteAnomalyBalanceCheckedIsTrue :
      finiteAnomalyBalanceChecked ≡ true

    registryStandardModelPromoted :
      Bool

    registryStandardModelPromotedIsFalse :
      registryStandardModelPromoted ≡ false

    authorityNumericValuePromoted :
      Bool

    authorityNumericValuePromotedIsFalse :
      authorityNumericValuePromoted ≡ false

    empiricalProviderAuthorityPromoted :
      Bool

    empiricalProviderAuthorityPromotedIsFalse :
      empiricalProviderAuthorityPromoted ≡ false

    empiricalComparisonLawPromoted :
      Bool

    empiricalComparisonLawPromotedIsFalse :
      empiricalComparisonLawPromoted ≡ false

    broadStandardModelFromFirstPrinciplesPromoted :
      Bool

    broadStandardModelFromFirstPrinciplesPromotedIsFalse :
      broadStandardModelFromFirstPrinciplesPromoted ≡ false

    falseBroadStandardModelPromotion :
      Bool

    falseBroadStandardModelPromotionIsFalse :
      falseBroadStandardModelPromotion ≡ false

    terminalUnificationPromoted :
      Bool

    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

    receiptBoundary :
      List String

open StandardModelFirstPrinciplesGapIndexReceipt public

canonicalStandardModelFirstPrinciplesGapIndexReceipt :
  StandardModelFirstPrinciplesGapIndexReceipt
canonicalStandardModelFirstPrinciplesGapIndexReceipt =
  record
    { finiteRepresentationNarrowingReceipt =
        Narrow.canonicalStandardModelFiniteRepresentationNarrowingReceipt
    ; finiteAnomalyHyperchargeCheckReceipt =
        Anomaly.canonicalFiniteSMAnomalyHyperchargeCheckReceipt
    ; terminalObligationReceipt =
        Terminal.canonicalStandardModelTerminalPromotionObligationReceipt
    ; physicsRegistryReceipt =
        Registry.canonicalPhysicsAdapterKnownInputsReferenceReceipt
    ; authorityPolicyReceipt =
        Registry.canonicalAuthorityConsumptionPolicyReceipt
    ; empiricalRuntimeReceipt =
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
    ; gapRows =
        canonicalFirstPrinciplesGapRows
    ; gapRowsAreCanonical =
        refl
    ; firstPrinciplesGapRowCount =
        listCount canonicalFirstPrinciplesGapRows
    ; firstPrinciplesGapRowCountIsTen =
        refl
    ; falseBroadPromotionGuards =
        canonicalFalseBroadPromotionGuards
    ; falseBroadPromotionGuardsAreCanonical =
        refl
    ; falseBroadPromotionGuardCount =
        listCount canonicalFalseBroadPromotionGuards
    ; falseBroadPromotionGuardCountIsSix =
        refl
    ; finiteGaugeNameRowCount =
        Narrow.finiteGaugeNameRowCount
          Narrow.canonicalStandardModelFiniteRepresentationNarrowingReceipt
    ; finiteGaugeNameRowCountIsThree =
        refl
    ; finiteRepresentationTargetCount =
        Narrow.oneGenerationRepresentationTargetCount
          Narrow.canonicalStandardModelFiniteRepresentationNarrowingReceipt
    ; finiteRepresentationTargetCountIsFive =
        refl
    ; finiteHyperchargeMultipletRowCount =
        Anomaly.finiteHyperchargeMultipletRowCount
          Anomaly.canonicalFiniteSMAnomalyHyperchargeCheckReceipt
    ; finiteHyperchargeMultipletRowCountIsSix =
        refl
    ; finiteAnomalyBalanceRowCount =
        Anomaly.anomalyBalanceRowCount
          Anomaly.canonicalFiniteSMAnomalyHyperchargeCheckReceipt
    ; finiteAnomalyBalanceRowCountIsFour =
        refl
    ; terminalSMObligationCount =
        Terminal.standardModelObligationCount
          Terminal.canonicalStandardModelTerminalPromotionObligationReceipt
    ; terminalSMObligationCountIsNine =
        refl
    ; finiteRepresentationContentNarrowed =
        Narrow.finiteRepresentationContentNarrowed
          Narrow.canonicalStandardModelFiniteRepresentationNarrowingReceipt
    ; finiteRepresentationContentNarrowedIsTrue =
        refl
    ; finiteHyperchargeRowsChecked =
        Anomaly.finiteHyperchargeRowsChecked
          Anomaly.canonicalFiniteSMAnomalyHyperchargeCheckReceipt
    ; finiteHyperchargeRowsCheckedIsTrue =
        refl
    ; finiteAnomalyBalanceChecked =
        Anomaly.finiteAnomalyBalanceChecked
          Anomaly.canonicalFiniteSMAnomalyHyperchargeCheckReceipt
    ; finiteAnomalyBalanceCheckedIsTrue =
        refl
    ; registryStandardModelPromoted =
        Registry.PhysicsAdapterKnownInputsReferenceReceipt.standardModelPromoted
          Registry.canonicalPhysicsAdapterKnownInputsReferenceReceipt
    ; registryStandardModelPromotedIsFalse =
        Registry.PhysicsAdapterKnownInputsReferenceReceipt.standardModelPromotedIsFalse
          Registry.canonicalPhysicsAdapterKnownInputsReferenceReceipt
    ; authorityNumericValuePromoted =
        Registry.AuthorityConsumptionPolicyReceipt.numericValuePromoted
          Registry.canonicalAuthorityConsumptionPolicyReceipt
    ; authorityNumericValuePromotedIsFalse =
        Registry.AuthorityConsumptionPolicyReceipt.numericValuePromotedIsFalse
          Registry.canonicalAuthorityConsumptionPolicyReceipt
    ; empiricalProviderAuthorityPromoted =
        Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.acceptedProviderAuthorityPromoted
          Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
    ; empiricalProviderAuthorityPromotedIsFalse =
        Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.acceptedProviderAuthorityPromotedIsFalse
          Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
    ; empiricalComparisonLawPromoted =
        Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.comparisonLawPromoted
          Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
    ; empiricalComparisonLawPromotedIsFalse =
        Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.comparisonLawPromotedIsFalse
          Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
    ; broadStandardModelFromFirstPrinciplesPromoted =
        false
    ; broadStandardModelFromFirstPrinciplesPromotedIsFalse =
        refl
    ; falseBroadStandardModelPromotion =
        false
    ; falseBroadStandardModelPromotionIsFalse =
        refl
    ; terminalUnificationPromoted =
        Terminal.terminalPromotion
          Terminal.canonicalStandardModelTerminalPromotionObligationReceipt
    ; terminalUnificationPromotedIsFalse =
        Terminal.terminalPromotionIsFalse
          Terminal.canonicalStandardModelTerminalPromotionObligationReceipt
    ; receiptBoundary =
        "Positive finite surface preserved: three finite gauge-name rows"
        ∷ "Positive finite surface preserved: five representation targets, six hypercharge rows, and four zero anomaly-balance rows"
        ∷ "Gap index blocks broad first-principles promotion across gauge uniqueness, representation uniqueness, generations, Yukawa, Higgs, CKM, PMNS, couplings, QFT observables, and empirical authority"
        ∷ "Registry, empirical runtime, broad Standard Model, false broad promotion, and terminal promotion bits remain false"
        ∷ []
    }

canonicalFirstPrinciplesGapRowCountIsTen :
  firstPrinciplesGapRowCount
    canonicalStandardModelFirstPrinciplesGapIndexReceipt
  ≡
  10
canonicalFirstPrinciplesGapRowCountIsTen =
  refl

canonicalFalseBroadPromotionGuardCountIsSix :
  falseBroadPromotionGuardCount
    canonicalStandardModelFirstPrinciplesGapIndexReceipt
  ≡
  6
canonicalFalseBroadPromotionGuardCountIsSix =
  refl

canonicalFirstPrinciplesFiniteGaugeNameRowCountIsThree :
  finiteGaugeNameRowCount
    canonicalStandardModelFirstPrinciplesGapIndexReceipt
  ≡
  3
canonicalFirstPrinciplesFiniteGaugeNameRowCountIsThree =
  refl

canonicalFirstPrinciplesFiniteRepresentationTargetCountIsFive :
  finiteRepresentationTargetCount
    canonicalStandardModelFirstPrinciplesGapIndexReceipt
  ≡
  5
canonicalFirstPrinciplesFiniteRepresentationTargetCountIsFive =
  refl

canonicalFirstPrinciplesFiniteHyperchargeRowCountIsSix :
  finiteHyperchargeMultipletRowCount
    canonicalStandardModelFirstPrinciplesGapIndexReceipt
  ≡
  6
canonicalFirstPrinciplesFiniteHyperchargeRowCountIsSix =
  refl

canonicalFirstPrinciplesFiniteAnomalyBalanceRowCountIsFour :
  finiteAnomalyBalanceRowCount
    canonicalStandardModelFirstPrinciplesGapIndexReceipt
  ≡
  4
canonicalFirstPrinciplesFiniteAnomalyBalanceRowCountIsFour =
  refl

canonicalFirstPrinciplesTerminalSMObligationCountIsNine :
  terminalSMObligationCount
    canonicalStandardModelFirstPrinciplesGapIndexReceipt
  ≡
  9
canonicalFirstPrinciplesTerminalSMObligationCountIsNine =
  refl

standardModelFirstPrinciplesGapIndexPreservesFiniteNarrowing :
  finiteRepresentationContentNarrowed
    canonicalStandardModelFirstPrinciplesGapIndexReceipt
  ≡
  true
standardModelFirstPrinciplesGapIndexPreservesFiniteNarrowing =
  refl

standardModelFirstPrinciplesGapIndexPreservesFiniteAnomalyCheck :
  finiteAnomalyBalanceChecked
    canonicalStandardModelFirstPrinciplesGapIndexReceipt
  ≡
  true
standardModelFirstPrinciplesGapIndexPreservesFiniteAnomalyCheck =
  refl

standardModelFirstPrinciplesGapIndexRejectsBroadPromotion :
  broadStandardModelFromFirstPrinciplesPromoted
    canonicalStandardModelFirstPrinciplesGapIndexReceipt
  ≡
  false
standardModelFirstPrinciplesGapIndexRejectsBroadPromotion =
  refl

standardModelFirstPrinciplesGapIndexFalseBroadPromotionGuard :
  falseBroadStandardModelPromotion
    canonicalStandardModelFirstPrinciplesGapIndexReceipt
  ≡
  false
standardModelFirstPrinciplesGapIndexFalseBroadPromotionGuard =
  refl

standardModelFirstPrinciplesGapIndexKeepsTerminalPromotionFalse :
  terminalUnificationPromoted
    canonicalStandardModelFirstPrinciplesGapIndexReceipt
  ≡
  false
standardModelFirstPrinciplesGapIndexKeepsTerminalPromotionFalse =
  refl
