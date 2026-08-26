module DASHI.Core.ExceptionalSignalLatticeExact where

------------------------------------------------------------------------
-- EXCEPTION / CONTROL LATTICE
--
-- Source basis:
--   User-supplied DASHI reconstruction notes recover the older qMETA/qVOID/
--   qPARA and signaling variants as a separate exception/control vocabulary,
--   not ordinary Base369 values and not M1--M10 motifs.
--
-- This module extracts only the reusable finite severity semantics:
-- known contradiction outranks mere absence, and aggregation is monotone.
-- It does not claim IEEE-754 identity, paraconsistent completeness, or that
-- every historical spelling was fixed across all notes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Quiet/signaling mode is orthogonal to exceptional kind.
------------------------------------------------------------------------

data SignalMode : Set where
  quiet signaling : SignalMode

data ExceptionKind : Set where
  metaBoundary voidState paradoxState : ExceptionKind

record ExceptionalSignal : Set where
  constructor exceptionalSignal
  field
    mode : SignalMode
    kind : ExceptionKind

open ExceptionalSignal public

qMETA qVOID qPARA sVOID sPARA : ExceptionalSignal
qMETA = exceptionalSignal quiet metaBoundary
qVOID = exceptionalSignal quiet voidState
qPARA = exceptionalSignal quiet paradoxState
sVOID = exceptionalSignal signaling voidState
sPARA = exceptionalSignal signaling paradoxState

------------------------------------------------------------------------
-- Severity join.  Signaling mode is preserved if either input signals.
------------------------------------------------------------------------

joinMode : SignalMode → SignalMode → SignalMode
joinMode quiet quiet = quiet
joinMode _ _ = signaling

joinKind : ExceptionKind → ExceptionKind → ExceptionKind
joinKind paradoxState _ = paradoxState
joinKind _ paradoxState = paradoxState
joinKind voidState _ = voidState
joinKind _ voidState = voidState
joinKind metaBoundary metaBoundary = metaBoundary

infixl 6 _⊔E_

_⊔E_ : ExceptionalSignal → ExceptionalSignal → ExceptionalSignal
exceptionalSignal m₁ k₁ ⊔E exceptionalSignal m₂ k₂ =
  exceptionalSignal (joinMode m₁ m₂) (joinKind k₁ k₂)

paradoxDominatesVoid : qPARA ⊔E qVOID ≡ qPARA
paradoxDominatesVoid = refl

voidDominatesMeta : qVOID ⊔E qMETA ≡ qVOID
voidDominatesMeta = refl

signalingIsSticky : sVOID ⊔E qMETA ≡ sVOID
signalingIsSticky = refl

signalingParadoxDominatesQuietVoid : sPARA ⊔E qVOID ≡ sPARA
signalingParadoxDominatesQuietVoid = refl

------------------------------------------------------------------------
-- Distinguish value propagation from exception propagation.
------------------------------------------------------------------------

data ControlSurfaceKind : Set where
  ordinaryValueSurface exceptionalControlSurface : ControlSurfaceKind

ordinaryAndExceptionalAreDistinct :
  ordinaryValueSurface ≡ exceptionalControlSurface → ⊥
ordinaryAndExceptionalAreDistinct ()

record ExceptionalSignalBoundary : Set where
  constructor exceptional-signal-boundary
  field
    exceptionCodeIsOrdinaryBase369Value : Bool
    exceptionCodeIsOrdinaryBase369ValueIsFalse :
      exceptionCodeIsOrdinaryBase369Value ≡ false
    exceptionCodeIsMotif : Bool
    exceptionCodeIsMotifIsFalse : exceptionCodeIsMotif ≡ false
    missingInformationErasesKnownContradiction : Bool
    missingInformationErasesKnownContradictionIsFalse :
      missingInformationErasesKnownContradiction ≡ false
    joinIsInverseResolutionOperator : Bool
    joinIsInverseResolutionOperatorIsFalse :
      joinIsInverseResolutionOperator ≡ false

canonicalExceptionalSignalBoundary : ExceptionalSignalBoundary
canonicalExceptionalSignalBoundary =
  exceptional-signal-boundary false refl false refl false refl false refl
