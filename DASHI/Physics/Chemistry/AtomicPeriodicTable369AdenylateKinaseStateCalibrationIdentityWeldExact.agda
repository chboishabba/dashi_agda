module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseStateCalibrationIdentityWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseStructuralIdentitySnowballExact as Structural

------------------------------------------------------------------------
-- STATE-CALIBRATION / STRUCTURAL-IDENTITY WELD
--
-- Structural provenance is attached only where the state role actually supports
-- it.  Alpha and zeta retain open/closed structural-reference provenance; other
-- named landscape states do not inherit a PDB identity by proximity.
------------------------------------------------------------------------

data StructuralReferenceRole : Set where
  openEndpointReference : StructuralReferenceRole
  closedEndpointReference : StructuralReferenceRole
  noStructuralReferencePaid : StructuralReferenceRole

data StructuralIdentityPayment : Set where
  paidOpen4AKEReference : StructuralIdentityPayment
  paidClosed1AKEReference : StructuralIdentityPayment
  unpaidStructuralIdentity : String → StructuralIdentityPayment

record AttributedStateCalibration : Set where
  constructor attributed-state-calibration
  field
    calibration : Sparse.StateCalibrationObservation
    articleEnvelope : Attr.CalibrationAtomEnvelope
    structuralRole : StructuralReferenceRole
    structuralIdentity : StructuralIdentityPayment
    interpretation : String
open AttributedStateCalibration public

mkArticleStateAtom :
  Sparse.CalibrationStateLabel →
  Sparse.SparseNumericCoordinate →
  String →
  Attr.CalibrationAtomEnvelope
mkArticleStateAtom state coordinate label =
  Attr.mkLiLiuJiAtom
    label
    coordinate
    "named-state calibration role"
    "article-level calibration source retained independently from any structural-reference identity"

stateCalibrationWithIdentity :
  Sparse.CalibrationStateLabel → AttributedStateCalibration
stateCalibrationWithIdentity Sparse.alphaState =
  attributed-state-calibration
    (Sparse.stateCalibration Sparse.alphaState)
    (mkArticleStateAtom Sparse.alphaState
      (Sparse.thetaOneDegrees (Sparse.stateCalibration Sparse.alphaState))
      "alpha state calibration attribution")
    openEndpointReference
    paidOpen4AKEReference
    "alpha carries open-endpoint structural-reference provenance through the separately attributed 4AKE deposition; this is a role/reference weld, not definitional equality alpha=4AKE"
stateCalibrationWithIdentity Sparse.betaState =
  attributed-state-calibration
    (Sparse.stateCalibration Sparse.betaState)
    (mkArticleStateAtom Sparse.betaState
      (Sparse.thetaOneDegrees (Sparse.stateCalibration Sparse.betaState))
      "beta state calibration attribution")
    noStructuralReferencePaid
    (unpaidStructuralIdentity "no same-object PDB identity paid for beta")
    "beta remains a source-named intermediate without manufactured PDB identity"
stateCalibrationWithIdentity Sparse.gammaState =
  attributed-state-calibration
    (Sparse.stateCalibration Sparse.gammaState)
    (mkArticleStateAtom Sparse.gammaState
      (Sparse.relativeFreeEnergyTenthsKcalMol (Sparse.stateCalibration Sparse.gammaState))
      "gamma reference-energy attribution")
    noStructuralReferencePaid
    (unpaidStructuralIdentity "no same-object PDB identity paid for gamma")
    "gamma retains its free-energy reference role without inheriting 4AKE/1AKE identity"
stateCalibrationWithIdentity Sparse.deltaState =
  attributed-state-calibration
    (Sparse.stateCalibration Sparse.deltaState)
    (mkArticleStateAtom Sparse.deltaState
      (Sparse.thetaOneDegrees (Sparse.stateCalibration Sparse.deltaState))
      "delta state calibration attribution")
    noStructuralReferencePaid
    (unpaidStructuralIdentity "no same-object PDB identity paid for delta")
    "delta remains a qualitative intermediate without manufactured PDB identity"
stateCalibrationWithIdentity Sparse.epsilonState =
  attributed-state-calibration
    (Sparse.stateCalibration Sparse.epsilonState)
    (mkArticleStateAtom Sparse.epsilonState
      (Sparse.thetaOneDegrees (Sparse.stateCalibration Sparse.epsilonState))
      "epsilon state calibration attribution")
    noStructuralReferencePaid
    (unpaidStructuralIdentity "no same-object PDB identity paid for epsilon")
    "epsilon remains a qualitative intermediate without manufactured PDB identity"
stateCalibrationWithIdentity Sparse.zetaState =
  attributed-state-calibration
    (Sparse.stateCalibration Sparse.zetaState)
    (mkArticleStateAtom Sparse.zetaState
      (Sparse.thetaOneDegrees (Sparse.stateCalibration Sparse.zetaState))
      "zeta state calibration attribution")
    closedEndpointReference
    paidClosed1AKEReference
    "zeta carries closed-endpoint structural-reference provenance through the separately attributed 1AKE deposition; this is a role/reference weld, not definitional equality zeta=1AKE"
stateCalibrationWithIdentity Sparse.etaState =
  attributed-state-calibration
    (Sparse.stateCalibration Sparse.etaState)
    (mkArticleStateAtom Sparse.etaState
      (Sparse.thetaOneDegrees (Sparse.stateCalibration Sparse.etaState))
      "eta state calibration attribution")
    noStructuralReferencePaid
    (unpaidStructuralIdentity "no same-object PDB identity paid for eta")
    "eta remains a near-closed source region without manufactured PDB identity"
stateCalibrationWithIdentity Sparse.lambdaState =
  attributed-state-calibration
    (Sparse.stateCalibration Sparse.lambdaState)
    (mkArticleStateAtom Sparse.lambdaState
      (Sparse.thetaOneDegrees (Sparse.stateCalibration Sparse.lambdaState))
      "lambda state calibration attribution")
    noStructuralReferencePaid
    (unpaidStructuralIdentity "no same-object PDB identity paid for lambda")
    "lambda remains a near-closed source region without manufactured PDB identity"

------------------------------------------------------------------------
-- Expose the actual structural source objects rather than copying identifier
-- strings into this owner.
------------------------------------------------------------------------

alphaStructuralSource = Structural.open4AKESource
zetaStructuralSource = Structural.closed1AKESource
alphaPdbDoi = Structural.openPdbDoi
zetaPdbDoi = Structural.closedPdbDoi
sharedProteinIdentity = Structural.adkUniProt
sharedAdkQid = Structural.adkQid

------------------------------------------------------------------------
-- WrongType / same-object firewalls.
------------------------------------------------------------------------

data AlphaDefinitionallyEquals4AKE : Set where
data ZetaDefinitionallyEquals1AKE : Set where
data PdbReferenceCreatesTransitionRate : Set where
data QidCreatesStateCoordinate : Set where

aRoleReferenceIsNotDefinitionalIdentity : AlphaDefinitionallyEquals4AKE → ⊥
aRoleReferenceIsNotDefinitionalIdentity ()

zRoleReferenceIsNotDefinitionalIdentity : ZetaDefinitionallyEquals1AKE → ⊥
zRoleReferenceIsNotDefinitionalIdentity ()

pdbReferenceDoesNotCreateRate : PdbReferenceCreatesTransitionRate → ⊥
pdbReferenceDoesNotCreateRate ()

qidDoesNotCreateCoordinate : QidCreatesStateCoordinate → ⊥
qidDoesNotCreateCoordinate ()

record AdKStateCalibrationIdentityWeldBoundary : Set where
  constructor adk-state-calibration-identity-weld-boundary
  field
    alphaCarriesOpenStructuralReference : Bool
    zetaCarriesClosedStructuralReference : Bool
    gammaCarriesNoManufacturedPdbIdentity : Bool
    betaCarriesNoManufacturedPdbIdentity : Bool
    intermediateStatesRemainSparse : Bool
    alphaDefinitionallyEquals4AKE : Bool
    zetaDefinitionallyEquals1AKE : Bool
    pdbReferenceCreatesTransitionRate : Bool
    qidCreatesStateCoordinate : Bool

canonicalAdKStateCalibrationIdentityWeldBoundary : AdKStateCalibrationIdentityWeldBoundary
canonicalAdKStateCalibrationIdentityWeldBoundary =
  adk-state-calibration-identity-weld-boundary
    true true true true true
    false false false false
