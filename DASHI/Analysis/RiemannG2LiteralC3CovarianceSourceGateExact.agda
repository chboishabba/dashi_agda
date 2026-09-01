module DASHI.Analysis.RiemannG2LiteralC3CovarianceSourceGateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.ThreeChannelC3EquivarianceGateExact as C3
import DASHI.Analysis.RiemannAristotleTwoZeroThreeTaperReturnExact as Return
import DASHI.Analysis.RiemannG2CommonC3DeterminantCovarianceCompilerExact as Common

------------------------------------------------------------------------
-- LITERAL RH C3 SOURCE GATE
--
-- The current Agda cross-prover return records that Lean owns an explicitly
-- constructed positive three-taper theorem, but the Agda object intentionally
-- retains only theorem/provenance/status data.  It does not export the actual
-- taper functions, the two nuisance rows, or equations describing how those
-- objects transform under any order-three action.
--
-- Therefore absence of an Agda C3 witness is NOT a mathematical no-go for the
-- Lean construction.  The exact next source obligation is recovery of the
-- literal constructor payload.  Only after that recovery is it meaningful to
-- attempt a same-object common-C3 attachment.
------------------------------------------------------------------------

data LiteralC3SourceStage : Set where
  provenanceReturnOnly
  literalConstructorsRecovered
  commonActionRecovered
  scalarIdentityRecovered
  : LiteralC3SourceStage

currentLiteralC3SourceStage : LiteralC3SourceStage
currentLiteralC3SourceStage = provenanceReturnOnly

record RecoveredLiteralThreeTaperConstructors : Set₁ where
  field
    Scalar : Set
    Row : Set
    Taper : Set
    Parameter : Set

    nuisanceOne nuisanceTwo : Row
    taperOne taperTwo taperThree : Taper
    taperPointVector : Parameter -> Row

    -- Same-object receipts: these names must denote the literal objects from
    -- the owner theorem, not parallel reconstruction objects.
    sameLeanTheorem : Set
    sameNuisanceOne : Set
    sameNuisanceTwo : Set
    sameTaperOne : Set
    sameTaperTwo : Set
    sameTaperThree : Set
    sameTaperPointVector : Set

open RecoveredLiteralThreeTaperConstructors public

record RecoveredLiteralCommonC3
    (S : RecoveredLiteralThreeTaperConstructors) : Set₁ where
  field
    rowAction : C3.OrderThreeAction (Row S)

    nuisanceOneRotatesInsideConstruction : Set
    nuisanceTwoRotatesInsideConstruction : Set
    taperVectorRotatesInsideConstruction : Set

    -- This is deliberately stronger than a target-only channel permutation.
    -- It is the literal same-object covariance required by the determinant
    -- compiler: all three determinant rows co-transform under one action.
    commonActionUsesLiteralRows : Set

open RecoveredLiteralCommonC3 public

------------------------------------------------------------------------
-- Current return classification.
------------------------------------------------------------------------

currentReturnOwnsConstructedPositiveTriple : Bool
currentReturnOwnsConstructedPositiveTriple =
  Return.constructedPositiveTaperTriple Return.canonicalTwoZeroThreeTaperReturn

currentReturnOwnsExactSelectedNuisanceElimination : Bool
currentReturnOwnsExactSelectedNuisanceElimination =
  Return.twoSelectedNuisancesEliminatedExactly Return.canonicalTwoZeroThreeTaperReturn

currentReturnExportsLiteralConstructorPayload : Bool
currentReturnExportsLiteralConstructorPayload = false

currentReturnExportsLiteralConstructorPayloadIsFalse :
  currentReturnExportsLiteralConstructorPayload ≡ false
currentReturnExportsLiteralConstructorPayloadIsFalse = refl

currentReturnExportsCommonC3Action : Bool
currentReturnExportsCommonC3Action = false

currentReturnExportsCommonC3ActionIsFalse :
  currentReturnExportsCommonC3Action ≡ false
currentReturnExportsCommonC3ActionIsFalse = refl

------------------------------------------------------------------------
-- Route disposition after the generic determinant theorem.
--
-- Even if literal common-C3 covariance is later recovered, the common compiler
-- already shows that q-preservation yields consumer invariance.  Invariance of
-- the three orbit values is equality, not a signed cancellation theorem.
-- Hence "C3 symmetry alone closes G2d" is pruned now.  Source recovery remains
-- useful only if it yields an additional nontrivial scalar q/phase identity.
------------------------------------------------------------------------

data C3RouteDisposition : Set where
  sourceRecoveryDiagnostic
  symmetryOnlyCancellationPruned
  scalarSignedDeterminantAttackLive
  : C3RouteDisposition

literalC3SourceRecoveryDisposition : C3RouteDisposition
literalC3SourceRecoveryDisposition = sourceRecoveryDiagnostic

symmetryOnlyCancellationDisposition : C3RouteDisposition
symmetryOnlyCancellationDisposition = symmetryOnlyCancellationPruned

scalarSignedDeterminantDisposition : C3RouteDisposition
scalarSignedDeterminantDisposition = scalarSignedDeterminantAttackLive

record LiteralC3SourceGateBoundary : Set where
  constructor literal-c3-source-gate-boundary
  field
    currentAgdaReturnIsProvenanceSurface : Bool
    currentAgdaReturnIsProvenanceSurfaceIsTrue :
      currentAgdaReturnIsProvenanceSurface ≡ true

    missingAgdaPayloadProvesLiteralLeanConstructionHasNoC3 : Bool
    missingAgdaPayloadProvesLiteralLeanConstructionHasNoC3IsFalse :
      missingAgdaPayloadProvesLiteralLeanConstructionHasNoC3 ≡ false

    literalConstructorRecoveryRequiredBeforeSameObjectC3Audit : Bool
    literalConstructorRecoveryRequiredBeforeSameObjectC3AuditIsTrue :
      literalConstructorRecoveryRequiredBeforeSameObjectC3Audit ≡ true

    commonC3InvarianceAloneProvesSignedCancellation : Bool
    commonC3InvarianceAloneProvesSignedCancellationIsFalse :
      commonC3InvarianceAloneProvesSignedCancellation ≡ false

    symmetryOnlyG2dRoutePruned : Bool
    symmetryOnlyG2dRoutePrunedIsTrue :
      symmetryOnlyG2dRoutePruned ≡ true

    scalarSignedDeterminantSumRemainsLive : Bool
    scalarSignedDeterminantSumRemainsLiveIsTrue :
      scalarSignedDeterminantSumRemainsLive ≡ true

    highestAlphaReading : String

canonicalLiteralC3SourceGateBoundary : LiteralC3SourceGateBoundary
canonicalLiteralC3SourceGateBoundary =
  literal-c3-source-gate-boundary
    true refl
    false refl
    true refl
    false refl
    true refl
    true refl
    "The current Agda return does not contain enough source payload to decide whether the literal Lean taper/nuisance constructors admit a common C3 action. Recovering those constructors is a valid diagnostic task, but common-C3 determinant invariance alone can only make the determinant-sufficient consumer orbit-invariant, not cancel it. Therefore the symmetry-only G2d route is pruned; absent a recovered extra scalar q/phase identity, the live RH mathematics is the direct signed determinant-response cosine sum."
