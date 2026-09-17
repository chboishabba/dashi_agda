module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePDBMirrorTransportValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePDBMirrorTransportExact as Mirror

boundary = Mirror.canonicalAdKPDBMirrorTransportBoundary

_ : Mirror.pdbAuthorityIdentityRetained boundary ≡ true
_ = refl

_ : Mirror.transportMirrorIdentityRetained boundary ≡ true
_ = refl

_ : Mirror.gitBlobIdentityRetained boundary ≡ true
_ = refl

_ : Mirror.canonicalArchiveByteEqualityObserved boundary ≡ false
_ = refl

_ : Mirror.transportMirrorCreatesScientificAuthority boundary ≡ false
_ = refl

_ : Mirror.samePDBIdCreatesSameBytes boundary ≡ false
_ = refl
