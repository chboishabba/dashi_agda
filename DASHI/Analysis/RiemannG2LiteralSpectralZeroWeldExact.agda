module DASHI.Analysis.RiemannG2LiteralSpectralZeroWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compatibility
import DASHI.Analysis.RiemannAristotleCurrentFrontierExact as Frontier
import DASHI.Analysis.RiemannAristotleFiniteNearCoreSchurCompilerExact as Schur
import DASHI.Analysis.RiemannAristotleFiniteNearReflectionOrbitReturnExact as Near
import DASHI.Analysis.RiemannAristotleExplicitCutoffCarrierLeanReturnExact as Cutoff
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- LITERAL SPECTRAL-ZERO WELD FOR THE CURRENT G2 FINITE NEAR CORE
--
-- DASHI integration only.  No external source is credited with this typed
-- adapter.  The existing repo already owns:
--
--   * an abstract explicit-formula surface with arithmeticForm = spectralZeroForm;
--   * compatibility requiring the spectral form to use the owned xi-zero carrier;
--   * a finite reflection-stable nearOffFinset source surface;
--   * an explicit far-shell remainder / literal D_off cutoff theorem in Lean;
--   * an Agda finite-near-plus-far Schur consumer.
--
-- What is NOT yet owned is the same-object identification saying that the
-- spectralZeroForm for the actual determinant taper is exactly the literal
-- reflection-paired D_near + D_far object entering that Schur consumer.
------------------------------------------------------------------------

data LiteralG2Component : Set where
  determinantTaperTest
  fullSpectralZeroObject
  finiteNearReflectionPairedObject
  explicitFarRemainderObject
  postSchurNearEnergy
  postSchurFarEnergy
  : LiteralG2Component

------------------------------------------------------------------------
-- The weld is parameterised by the already-existing abstract explicit-formula
-- owner.  It deliberately requires equalities/realisation receipts rather than
-- identifying carriers because they share words such as "zero sum".
------------------------------------------------------------------------

record LiteralSpectralZeroWeld
    {Space : Set₁}
    (space : Space) : Set₁ where
  constructor literalSpectralZeroWeld
  field
    Formula : Set₁
    formula : Formula

    TaperTest : Set
    taper : TaperTest
    taperAdmissible : Set

    SpectralZeroValue : Set
    LiteralFullZeroValue : Set
    LiteralNearValue : Set
    LiteralFarValue : Set

    spectralZeroValue : SpectralZeroValue
    literalFullZeroValue : LiteralFullZeroValue
    literalNearValue : LiteralNearValue
    literalFarValue : LiteralFarValue

    spectralToLiteralFull : Set
    literalFullEqualsNearPlusFar : Set
    nearCarrierIsActualNearOffFinset : Set
    nearCarrierReflectionPairingPreserved : Set
    farCarrierIsActualCutoffRemainder : Set

    weldReference : String

open LiteralSpectralZeroWeld public

------------------------------------------------------------------------
-- After the same-object weld, a separate analytic transport is still required:
-- the explicit/arithmetic side must imply a bound on the POST-SCHUR finite near
-- energy.  This is deliberately downstream of the object identification.
------------------------------------------------------------------------

record ArithmeticToFiniteNearSchurBound
    {Space : Set₁}
    {space : Space}
    (weld : LiteralSpectralZeroWeld space) : Set₁ where
  constructor arithmeticToFiniteNearSchurBound
  field
    ArithmeticDatum : Set
    arithmeticDatum : ArithmeticDatum

    NearBoundClaim : Set
    nearBoundClaim : NearBoundClaim

    explicitFormulaArithmeticToSpectral : Set
    spectralWeldUsed : Set
    schurEliminationCompatibility : Set
    arithmeticImpliesNearBound : Set

    boundReference : String

open ArithmeticToFiniteNearSchurBound public

------------------------------------------------------------------------
-- Consumer-complete route.  This still does not produce RH by itself: it only
-- pays the exact finite-near piece consumed by the already-owned Schur compiler.
------------------------------------------------------------------------

record LiteralG2FiniteNearRoute
    {Space : Set₁}
    {space : Space}
    (weld : LiteralSpectralZeroWeld space) : Set₁ where
  constructor literalG2FiniteNearRoute
  field
    arithmeticBound : ArithmeticToFiniteNearSchurBound weld
    finiteNearAllowance : Schur.FiniteNearCoreAllowance
    allowanceIsForSameLiteralNearObject : Set
    farAllowanceUsesOwnedCutoffRemainder : Set
    routeReference : String

open LiteralG2FiniteNearRoute public

------------------------------------------------------------------------
-- Current source/status inheritance.
------------------------------------------------------------------------

nearCarrierReflectionStable :
  Near.finiteNearCarrierReflectionStableBySource
    Near.canonicalFiniteNearReflectionOrbitReturn ≡ true
nearCarrierReflectionStable =
  Near.finiteNearCarrierReflectionStableBySourceIsTrue
    Near.canonicalFiniteNearReflectionOrbitReturn

finiteNearCarrierAlreadyOwnedInLean :
  Cutoff.finiteSignedNearCarrierOwned Cutoff.canonicalExplicitCutoffCarrierLeanReturn ≡ true
finiteNearCarrierAlreadyOwnedInLean =
  Cutoff.finiteSignedNearCarrierOwnedIsTrue Cutoff.canonicalExplicitCutoffCarrierLeanReturn

literalDoffCutoffAlreadyOwnedInLean :
  Cutoff.literalDoffCutoffTransportOwned Cutoff.canonicalExplicitCutoffCarrierLeanReturn ≡ true
literalDoffCutoffAlreadyOwnedInLean =
  Cutoff.literalDoffCutoffTransportOwnedIsTrue Cutoff.canonicalExplicitCutoffCarrierLeanReturn

finiteSchurCompilerAlreadyClosedInAgda :
  Schur.scalarPerturbationConsumerClosedInAgda Schur.canonicalFiniteNearCoreSchurBoundary ≡ true
finiteSchurCompilerAlreadyClosedInAgda =
  Schur.scalarPerturbationConsumerClosedInAgdaIsTrue Schur.canonicalFiniteNearCoreSchurBoundary

finiteNearCancellationStillOpen :
  Frontier.finiteSignedNearSchurCancellationClosed Frontier.canonicalAristotleCurrentFrontier ≡ false
finiteNearCancellationStillOpen =
  Frontier.finiteSignedNearSchurCancellationClosedIsFalse Frontier.canonicalAristotleCurrentFrontier

------------------------------------------------------------------------
-- Relation-strength classification.
------------------------------------------------------------------------

literalSpectralWeldRelation : Relation.RelationKind
literalSpectralWeldRelation = Relation.exactSameObjectRealisation

literalWeldAloneCannotTransferTheorem :
  Relation.TheoremTransferCapability literalSpectralWeldRelation → ⊥
literalWeldAloneCannotTransferTheorem =
  Relation.sameObjectAloneCannotDirectlyTransferTheorem

------------------------------------------------------------------------
-- Current cut.
------------------------------------------------------------------------

literalSpectralZeroWeldRecovered : Bool
literalSpectralZeroWeldRecovered = false

arithmeticToFiniteNearSchurBoundRecovered : Bool
arithmeticToFiniteNearSchurBoundRecovered = false

literalSpectralZeroWeldRecoveredIsFalse :
  literalSpectralZeroWeldRecovered ≡ false
literalSpectralZeroWeldRecoveredIsFalse = refl

arithmeticToFiniteNearSchurBoundRecoveredIsFalse :
  arithmeticToFiniteNearSchurBoundRecovered ≡ false
arithmeticToFiniteNearSchurBoundRecoveredIsFalse = refl

record LiteralSpectralZeroWeldBoundary : Set where
  constructor literalSpectralZeroWeldBoundary
  field
    abstractExplicitFormulaIsAlreadyOwned : Bool
    abstractExplicitFormulaIsAlreadyOwnedIsTrue :
      abstractExplicitFormulaIsAlreadyOwned ≡ true

    finiteNearAndFarCarrierAreAlreadyOwned : Bool
    finiteNearAndFarCarrierAreAlreadyOwnedIsTrue :
      finiteNearAndFarCarrierAreAlreadyOwned ≡ true

    matchingZeroVocabularyCreatesSameObjectWeld : Bool
    matchingZeroVocabularyCreatesSameObjectWeldIsFalse :
      matchingZeroVocabularyCreatesSameObjectWeld ≡ false

    sameObjectWeldAutomaticallyProvesSignedCancellation : Bool
    sameObjectWeldAutomaticallyProvesSignedCancellationIsFalse :
      sameObjectWeldAutomaticallyProvesSignedCancellation ≡ false

    highestAlphaObjectIsPostSchurFiniteNearEnergy : Bool
    highestAlphaObjectIsPostSchurFiniteNearEnergyIsTrue :
      highestAlphaObjectIsPostSchurFiniteNearEnergy ≡ true

canonicalLiteralSpectralZeroWeldBoundary : LiteralSpectralZeroWeldBoundary
canonicalLiteralSpectralZeroWeldBoundary =
  literalSpectralZeroWeldBoundary
    true refl
    true refl
    false refl
    false refl
    true refl
