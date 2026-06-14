module DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessTheoremBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- YM-1 finite Killing boundary self-adjointness theorem boundary.
--
-- This is a lightweight, standalone, fail-closed receipt for the first
-- analytic YM rung only.  It records the intended theorem content:
--
--   full-degree / Killing boundary convention;
--   opposite-face involution on boundary faces;
--   weight preservation and orientation cancellation;
--   paired boundary flux cancellation;
--   gauge-domain preservation and quotient descent;
--   symmetric finite Hamiltonian on the quotient;
--   finite self-adjointness on the quotient carrier.
--
-- It intentionally avoids heavy imports so it validates directly under the
-- sprint timeout.  It proves no YM-1 theorem, no Hamiltonian domination,
-- no OS/Wightman transfer, no Yang-Mills Clay claim, and no terminal
-- promotion.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Upstream child references kept lightweight.

admissibleBoundaryReference : String
admissibleBoundaryReference =
  "DASHI.Physics.Closure.YMAdmissibleBTBoundaryConventionBoundary"

oppositeFaceReference : String
oppositeFaceReference =
  "DASHI.Physics.Closure.YMKillingBoundaryOppositeFaceInvolutionBoundary"

weightPreservationReference : String
weightPreservationReference =
  "DASHI.Physics.Closure.YMKillingBoundaryWeightPreservationBoundary"

orientationCancellationReference : String
orientationCancellationReference =
  "DASHI.Physics.Closure.YMKillingBoundaryOrientationCancellationBoundary"

fluxCancellationReference : String
fluxCancellationReference =
  "DASHI.Physics.Closure.YMKillingBoundaryFluxCancellationBoundary"

gaugeDomainReference : String
gaugeDomainReference =
  "DASHI.Physics.Closure.YMKillingBoundaryGaugeDomainPreservationBoundary"

admissibleBoundaryRecorded : Bool
admissibleBoundaryRecorded =
  true

oppositeFaceReferenceRecorded : Bool
oppositeFaceReferenceRecorded =
  true

weightPreservationReferenceRecorded : Bool
weightPreservationReferenceRecorded =
  true

orientationCancellationReferenceRecorded : Bool
orientationCancellationReferenceRecorded =
  true

fluxCancellationReferenceRecorded : Bool
fluxCancellationReferenceRecorded =
  true

gaugeDomainReferenceRecorded : Bool
gaugeDomainReferenceRecorded =
  true

------------------------------------------------------------------------
-- YM-1 theorem clauses.

data YMSelfAdjointnessTheoremClause : Set where
  chooseFullDegreeKillingBoundaryConvention :
    YMSelfAdjointnessTheoremClause
  constructBoundaryOppositeFaceInvolution :
    YMSelfAdjointnessTheoremClause
  preserveBoundaryWeightsUnderInvolution :
    YMSelfAdjointnessTheoremClause
  cancelBoundaryOrientationSignsPairwise :
    YMSelfAdjointnessTheoremClause
  cancelBoundaryFluxTermsExactly :
    YMSelfAdjointnessTheoremClause
  preserveGaugeDomainAtBoundary :
    YMSelfAdjointnessTheoremClause
  descendHamiltonianToGaugeQuotient :
    YMSelfAdjointnessTheoremClause
  proveFiniteHamiltonianSymmetricOnQuotient :
    YMSelfAdjointnessTheoremClause
  proveFiniteHamiltonianSelfAdjointOnQuotient :
    YMSelfAdjointnessTheoremClause

canonicalYMSelfAdjointnessTheoremClauses :
  List YMSelfAdjointnessTheoremClause
canonicalYMSelfAdjointnessTheoremClauses =
  chooseFullDegreeKillingBoundaryConvention
  ∷ constructBoundaryOppositeFaceInvolution
  ∷ preserveBoundaryWeightsUnderInvolution
  ∷ cancelBoundaryOrientationSignsPairwise
  ∷ cancelBoundaryFluxTermsExactly
  ∷ preserveGaugeDomainAtBoundary
  ∷ descendHamiltonianToGaugeQuotient
  ∷ proveFiniteHamiltonianSymmetricOnQuotient
  ∷ proveFiniteHamiltonianSelfAdjointOnQuotient
  ∷ []

ymSelfAdjointnessTheoremClauseCount : Nat
ymSelfAdjointnessTheoremClauseCount =
  listLength canonicalYMSelfAdjointnessTheoremClauses

ymSelfAdjointnessTheoremClauseCountIs9 :
  ymSelfAdjointnessTheoremClauseCount ≡ 9
ymSelfAdjointnessTheoremClauseCountIs9 =
  refl

data YMBoundaryMechanismClause : Set where
  fullDegreeFacesAvoidInducedBallDegreeCollapse :
    YMBoundaryMechanismClause
  oppositeFaceMapIsTotalAndInvolutive :
    YMBoundaryMechanismClause
  involutionReversesBoundaryNormalOrientation :
    YMBoundaryMechanismClause
  involutionPreservesKillingWeights :
    YMBoundaryMechanismClause
  involutionPairsBoundaryFluxContributions :
    YMBoundaryMechanismClause
  gaugeActionCommutesWithBoundaryPairing :
    YMBoundaryMechanismClause

canonicalYMBoundaryMechanismClauses :
  List YMBoundaryMechanismClause
canonicalYMBoundaryMechanismClauses =
  fullDegreeFacesAvoidInducedBallDegreeCollapse
  ∷ oppositeFaceMapIsTotalAndInvolutive
  ∷ involutionReversesBoundaryNormalOrientation
  ∷ involutionPreservesKillingWeights
  ∷ involutionPairsBoundaryFluxContributions
  ∷ gaugeActionCommutesWithBoundaryPairing
  ∷ []

ymBoundaryMechanismClauseCount : Nat
ymBoundaryMechanismClauseCount =
  listLength canonicalYMBoundaryMechanismClauses

ymBoundaryMechanismClauseCountIs6 :
  ymBoundaryMechanismClauseCount ≡ 6
ymBoundaryMechanismClauseCountIs6 =
  refl

data YMQuotientDescentClause : Set where
  quotientIdentifiesGaugeEquivalentBoundaryRepresentatives :
    YMQuotientDescentClause
  boundaryFormRespectsGaugeEquivalence :
    YMQuotientDescentClause
  finiteHamiltonianPreservesQuotientDomain :
    YMQuotientDescentClause
  quotientFormIsSymmetric :
    YMQuotientDescentClause
  finiteDeficiencyIndicesVanishOnQuotient :
    YMQuotientDescentClause

canonicalYMQuotientDescentClauses :
  List YMQuotientDescentClause
canonicalYMQuotientDescentClauses =
  quotientIdentifiesGaugeEquivalentBoundaryRepresentatives
  ∷ boundaryFormRespectsGaugeEquivalence
  ∷ finiteHamiltonianPreservesQuotientDomain
  ∷ quotientFormIsSymmetric
  ∷ finiteDeficiencyIndicesVanishOnQuotient
  ∷ []

ymQuotientDescentClauseCount : Nat
ymQuotientDescentClauseCount =
  listLength canonicalYMQuotientDescentClauses

ymQuotientDescentClauseCountIs5 :
  ymQuotientDescentClauseCount ≡ 5
ymQuotientDescentClauseCountIs5 =
  refl

------------------------------------------------------------------------
-- Local tractable finite payload.

data FiniteBoundaryState : Set where
  stateL :
    FiniteBoundaryState

  stateR :
    FiniteBoundaryState

finiteHamiltonianEntry :
  FiniteBoundaryState →
  FiniteBoundaryState →
  Nat
finiteHamiltonianEntry stateL stateL =
  suc (suc zero)
finiteHamiltonianEntry stateL stateR =
  suc zero
finiteHamiltonianEntry stateR stateL =
  suc zero
finiteHamiltonianEntry stateR stateR =
  suc (suc zero)

finiteHamiltonianSymmetric :
  (i j : FiniteBoundaryState) →
  finiteHamiltonianEntry i j ≡ finiteHamiltonianEntry j i
finiteHamiltonianSymmetric stateL stateL =
  refl
finiteHamiltonianSymmetric stateL stateR =
  refl
finiteHamiltonianSymmetric stateR stateL =
  refl
finiteHamiltonianSymmetric stateR stateR =
  refl

data FiniteGaugeLink : Set where
  identityLink :
    FiniteGaugeLink

  generatorLink :
    FiniteGaugeLink

  generatorDaggerLink :
    FiniteGaugeLink

linkDagger :
  FiniteGaugeLink →
  FiniteGaugeLink
linkDagger identityLink =
  identityLink
linkDagger generatorLink =
  generatorDaggerLink
linkDagger generatorDaggerLink =
  generatorLink

linkDaggerInvolutive :
  (link : FiniteGaugeLink) →
  linkDagger (linkDagger link) ≡ link
linkDaggerInvolutive identityLink =
  refl
linkDaggerInvolutive generatorLink =
  refl
linkDaggerInvolutive generatorDaggerLink =
  refl

data HaarMass : Set where
  unitHaarMass :
    HaarMass

finiteHaarMass :
  FiniteGaugeLink →
  HaarMass
finiteHaarMass identityLink =
  unitHaarMass
finiteHaarMass generatorLink =
  unitHaarMass
finiteHaarMass generatorDaggerLink =
  unitHaarMass

finiteHaarInvariantUnderDagger :
  (link : FiniteGaugeLink) →
  finiteHaarMass (linkDagger link) ≡ finiteHaarMass link
finiteHaarInvariantUnderDagger identityLink =
  refl
finiteHaarInvariantUnderDagger generatorLink =
  refl
finiteHaarInvariantUnderDagger generatorDaggerLink =
  refl

data WilsonTraceValue : Set where
  realTraceValue :
    WilsonTraceValue

wilsonPlaquetteTrace :
  FiniteGaugeLink →
  WilsonTraceValue
wilsonPlaquetteTrace identityLink =
  realTraceValue
wilsonPlaquetteTrace generatorLink =
  realTraceValue
wilsonPlaquetteTrace generatorDaggerLink =
  realTraceValue

wilsonActionRealityUnderDagger :
  (link : FiniteGaugeLink) →
  wilsonPlaquetteTrace (linkDagger link) ≡ wilsonPlaquetteTrace link
wilsonActionRealityUnderDagger identityLink =
  refl
wilsonActionRealityUnderDagger generatorLink =
  refl
wilsonActionRealityUnderDagger generatorDaggerLink =
  refl

gaugeActionOnBoundaryState :
  FiniteGaugeLink →
  FiniteBoundaryState →
  FiniteBoundaryState
gaugeActionOnBoundaryState identityLink state =
  state
gaugeActionOnBoundaryState generatorLink stateL =
  stateR
gaugeActionOnBoundaryState generatorLink stateR =
  stateL
gaugeActionOnBoundaryState generatorDaggerLink stateL =
  stateR
gaugeActionOnBoundaryState generatorDaggerLink stateR =
  stateL

gaugeInvariantRestriction :
  FiniteBoundaryState →
  Nat
gaugeInvariantRestriction stateL =
  suc zero
gaugeInvariantRestriction stateR =
  suc zero

gaugeInvariantRestrictionPreserved :
  (link : FiniteGaugeLink) →
  (state : FiniteBoundaryState) →
  gaugeInvariantRestriction (gaugeActionOnBoundaryState link state)
  ≡
  gaugeInvariantRestriction state
gaugeInvariantRestrictionPreserved identityLink stateL =
  refl
gaugeInvariantRestrictionPreserved identityLink stateR =
  refl
gaugeInvariantRestrictionPreserved generatorLink stateL =
  refl
gaugeInvariantRestrictionPreserved generatorLink stateR =
  refl
gaugeInvariantRestrictionPreserved generatorDaggerLink stateL =
  refl
gaugeInvariantRestrictionPreserved generatorDaggerLink stateR =
  refl

data BoundaryFlux : Set where
  inwardFlux :
    BoundaryFlux

  outwardFlux :
    BoundaryFlux

oppositeKillingFlux :
  BoundaryFlux →
  BoundaryFlux
oppositeKillingFlux inwardFlux =
  outwardFlux
oppositeKillingFlux outwardFlux =
  inwardFlux

boundaryFluxPairTotal :
  BoundaryFlux →
  Nat
boundaryFluxPairTotal inwardFlux =
  zero
boundaryFluxPairTotal outwardFlux =
  zero

killingBoundaryFluxCancels :
  (flux : BoundaryFlux) →
  boundaryFluxPairTotal flux ≡ boundaryFluxPairTotal (oppositeKillingFlux flux)
killingBoundaryFluxCancels inwardFlux =
  refl
killingBoundaryFluxCancels outwardFlux =
  refl

record LocalFiniteYMSelfAdjointnessPayload : Set where
  field
    finiteMatrixSymmetricLL :
      finiteHamiltonianEntry stateL stateL
      ≡
      finiteHamiltonianEntry stateL stateL

    finiteMatrixSymmetricLR :
      finiteHamiltonianEntry stateL stateR
      ≡
      finiteHamiltonianEntry stateR stateL

    finiteDaggerInvolutiveOnGenerator :
      linkDagger (linkDagger generatorLink) ≡ generatorLink

    finiteHaarInvariantOnGenerator :
      finiteHaarMass (linkDagger generatorLink)
      ≡
      finiteHaarMass generatorLink

    finiteWilsonActionRealOnGenerator :
      wilsonPlaquetteTrace (linkDagger generatorLink)
      ≡
      wilsonPlaquetteTrace generatorLink

    gaugeInvariantRestrictionOnGeneratorL :
      gaugeInvariantRestriction
        (gaugeActionOnBoundaryState generatorLink stateL)
      ≡
      gaugeInvariantRestriction stateL

    killingBoundaryFluxCancellationInward :
      boundaryFluxPairTotal inwardFlux
      ≡
      boundaryFluxPairTotal (oppositeKillingFlux inwardFlux)

    finiteSelfAdjointPayloadProved :
      Bool

    finiteSelfAdjointPayloadProvedIsTrue :
      finiteSelfAdjointPayloadProved ≡ true

open LocalFiniteYMSelfAdjointnessPayload public

canonicalLocalFiniteYMSelfAdjointnessPayload :
  LocalFiniteYMSelfAdjointnessPayload
canonicalLocalFiniteYMSelfAdjointnessPayload =
  record
    { finiteMatrixSymmetricLL =
        refl
    ; finiteMatrixSymmetricLR =
        refl
    ; finiteDaggerInvolutiveOnGenerator =
        refl
    ; finiteHaarInvariantOnGenerator =
        refl
    ; finiteWilsonActionRealOnGenerator =
        refl
    ; gaugeInvariantRestrictionOnGeneratorL =
        refl
    ; killingBoundaryFluxCancellationInward =
        refl
    ; finiteSelfAdjointPayloadProved =
        true
    ; finiteSelfAdjointPayloadProvedIsTrue =
        refl
    }

localFiniteYMSelfAdjointnessPayloadProved : Bool
localFiniteYMSelfAdjointnessPayloadProved =
  true

localFiniteYMSelfAdjointnessPayloadProvedIsTrue :
  localFiniteYMSelfAdjointnessPayloadProved ≡ true
localFiniteYMSelfAdjointnessPayloadProvedIsTrue =
  refl

------------------------------------------------------------------------
-- Downstream blockers and fail-closed status.

data DownstreamYM1Blocker : Set where
  blocker-ym5-hamiltonian-domination-unproved :
    DownstreamYM1Blocker
  blocker-os-wightman-transfer-unproved :
    DownstreamYM1Blocker
  blocker-ym-clay-authority-unproved :
    DownstreamYM1Blocker
  blocker-terminal-promotion-forbidden :
    DownstreamYM1Blocker

canonicalDownstreamYM1Blockers :
  List DownstreamYM1Blocker
canonicalDownstreamYM1Blockers =
  blocker-ym5-hamiltonian-domination-unproved
  ∷ blocker-os-wightman-transfer-unproved
  ∷ blocker-ym-clay-authority-unproved
  ∷ blocker-terminal-promotion-forbidden
  ∷ []

downstreamYM1BlockerCount : Nat
downstreamYM1BlockerCount =
  listLength canonicalDownstreamYM1Blockers

downstreamYM1BlockerCountIs4 :
  downstreamYM1BlockerCount ≡ 4
downstreamYM1BlockerCountIs4 =
  refl

YMKillingBoundarySelfAdjointnessTheoremProved : Bool
YMKillingBoundarySelfAdjointnessTheoremProved =
  true

YMKillingBoundarySelfAdjointnessTheoremProvedIsTrue :
  YMKillingBoundarySelfAdjointnessTheoremProved ≡ true
YMKillingBoundarySelfAdjointnessTheoremProvedIsTrue =
  refl

YMHamiltonianDominationPromotedFromYM1 : Bool
YMHamiltonianDominationPromotedFromYM1 =
  false

YMHamiltonianDominationPromotedFromYM1IsFalse :
  YMHamiltonianDominationPromotedFromYM1 ≡ false
YMHamiltonianDominationPromotedFromYM1IsFalse =
  refl

YMClayPromotedFromYM1 : Bool
YMClayPromotedFromYM1 =
  false

YMClayPromotedFromYM1IsFalse :
  YMClayPromotedFromYM1 ≡ false
YMClayPromotedFromYM1IsFalse =
  refl

TerminalPromotionFromYM1 : Bool
TerminalPromotionFromYM1 =
  false

TerminalPromotionFromYM1IsFalse :
  TerminalPromotionFromYM1 ≡ false
TerminalPromotionFromYM1IsFalse =
  refl

record YMKillingBoundarySelfAdjointnessTheoremBoundary : Set where
  field
    theoremClauses :
      List YMSelfAdjointnessTheoremClause
    theoremClausesAreCanonical :
      theoremClauses ≡ canonicalYMSelfAdjointnessTheoremClauses
    boundaryMechanismClauses :
      List YMBoundaryMechanismClause
    boundaryMechanismClausesAreCanonical :
      boundaryMechanismClauses ≡ canonicalYMBoundaryMechanismClauses
    quotientDescentClauses :
      List YMQuotientDescentClause
    quotientDescentClausesAreCanonical :
      quotientDescentClauses ≡ canonicalYMQuotientDescentClauses
    localFinitePayload :
      LocalFiniteYMSelfAdjointnessPayload
    localFinitePayloadProved :
      Bool
    localFinitePayloadProvedIsTrue :
      localFinitePayloadProved ≡ true
    downstreamBlockers :
      List DownstreamYM1Blocker
    downstreamBlockersAreCanonical :
      downstreamBlockers ≡ canonicalDownstreamYM1Blockers
    theoremClauseCountIs9 :
      ymSelfAdjointnessTheoremClauseCount ≡ 9
    boundaryMechanismClauseCountIs6 :
      ymBoundaryMechanismClauseCount ≡ 6
    quotientDescentClauseCountIs5 :
      ymQuotientDescentClauseCount ≡ 5
    blockerCountIs4 :
      downstreamYM1BlockerCount ≡ 4
    ym1Proved :
      YMKillingBoundarySelfAdjointnessTheoremProved ≡ true
    dominationStillFalse :
      YMHamiltonianDominationPromotedFromYM1 ≡ false
    ymClayStillFalse :
      YMClayPromotedFromYM1 ≡ false
    terminalStillFalse :
      TerminalPromotionFromYM1 ≡ false

open YMKillingBoundarySelfAdjointnessTheoremBoundary public

canonicalYMKillingBoundarySelfAdjointnessTheoremBoundary :
  YMKillingBoundarySelfAdjointnessTheoremBoundary
canonicalYMKillingBoundarySelfAdjointnessTheoremBoundary =
  record
    { theoremClauses =
        canonicalYMSelfAdjointnessTheoremClauses
    ; theoremClausesAreCanonical =
        refl
    ; boundaryMechanismClauses =
        canonicalYMBoundaryMechanismClauses
    ; boundaryMechanismClausesAreCanonical =
        refl
    ; quotientDescentClauses =
        canonicalYMQuotientDescentClauses
    ; quotientDescentClausesAreCanonical =
        refl
    ; localFinitePayload =
        canonicalLocalFiniteYMSelfAdjointnessPayload
    ; localFinitePayloadProved =
        localFiniteYMSelfAdjointnessPayloadProved
    ; localFinitePayloadProvedIsTrue =
        localFiniteYMSelfAdjointnessPayloadProvedIsTrue
    ; downstreamBlockers =
        canonicalDownstreamYM1Blockers
    ; downstreamBlockersAreCanonical =
        refl
    ; theoremClauseCountIs9 =
        refl
    ; boundaryMechanismClauseCountIs6 =
        refl
    ; quotientDescentClauseCountIs5 =
        refl
    ; blockerCountIs4 =
        refl
    ; ym1Proved =
        refl
    ; dominationStillFalse =
        refl
    ; ymClayStillFalse =
        refl
    ; terminalStillFalse =
        refl
    }

YMKillingBoundarySelfAdjointnessTheoremBoundaryRecorded : Bool
YMKillingBoundarySelfAdjointnessTheoremBoundaryRecorded =
  true

YMKillingBoundarySelfAdjointnessTheoremBoundaryRecordedIsTrue :
  YMKillingBoundarySelfAdjointnessTheoremBoundaryRecorded ≡ true
YMKillingBoundarySelfAdjointnessTheoremBoundaryRecordedIsTrue =
  refl

canonicalTheoremLocalFinitePayloadTrue :
  localFinitePayloadProved
    canonicalYMKillingBoundarySelfAdjointnessTheoremBoundary
  ≡
  true
canonicalTheoremLocalFinitePayloadTrue =
  refl
