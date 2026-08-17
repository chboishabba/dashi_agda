module DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityLookupExactRound71Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- ROUND 71 / EXACT REALITY LOOKUP
--
-- The fixed-canonical full-space Picard carrier stores one arbitrary Complex3 F
-- value for every canonical positive reality-orbit mode.  This module proves
-- the executable lookup has the intended physical meaning exactly:
--
--   velocity(k)  = stored value,
--   velocity(-k) = conjugate(stored value).
--
-- The proof uses the canonical orbit carrier's duplicate-freedom and exact
-- exclusion of opposite pairs.  Thus reality is an actual invariant of the
-- finite state representation, not a marker field in the raw Audit record.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffOrbitCarrierRound63Exact as Orbit
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact as Fixed

entryModeMember :
  ∀ {r} {F : C3.RealField r} {entry entries} →
  entry Cube.∈ entries →
  Fixed.mode entry Cube.∈ Fixed.modeList entries
entryModeMember (Cube.here equality) = Cube.here (cong Fixed.mode equality)
entryModeMember (Cube.there member) = Cube.there (entryModeMember member)

stateModeListNoDuplicates :
  ∀ {r} {F : C3.RealField r} {N}
    (state : Fixed.CanonicalRealityState F N) →
  Cube.NoDuplicates (Fixed.modeList (Fixed.positiveValues state))
stateModeListNoDuplicates {N = N} state =
  subst Cube.NoDuplicates
    (sym (Fixed.positiveModesExact state))
    (Orbit.canonicalCutoffOrbitNoDuplicates N)

lookupPositiveExact :
  ∀ {r} {F : C3.RealField r} {entries}
    (noDuplicates : Cube.NoDuplicates (Fixed.modeList entries))
    (entry : Fixed.CanonicalModeValue F) →
  entry Cube.∈ entries →
  Fixed.lookupPositive entries (Fixed.mode entry) ≡ Fixed.value entry
lookupPositiveExact {entries = []} noDuplicates entry ()
lookupPositiveExact {entries = head ∷ rest}
    (Cube.unique∷ fresh tailUnique) entry (Cube.here refl)
  rewrite Output.modeEqualRefl (Fixed.mode head) = refl
lookupPositiveExact {entries = head ∷ rest}
    (Cube.unique∷ fresh tailUnique) entry (Cube.there member)
  with Output.modeEqual (Fixed.mode entry) (Fixed.mode head) in equality
... | true =
  let
    same : Fixed.mode entry ≡ Fixed.mode head
    same = Output.modeEqualSound equality
    entryModeTail : Fixed.mode entry Cube.∈ Fixed.modeList rest
    entryModeTail = entryModeMember member
    headModeTail : Fixed.mode head Cube.∈ Fixed.modeList rest
    headModeTail = subst
      (λ selected → selected Cube.∈ Fixed.modeList rest)
      same entryModeTail
  in
  Output.falseNotTrue (fresh headModeTail)
... | false = lookupPositiveExact tailUnique entry member

positiveModeOccursFalseWhenAbsent :
  ∀ {r} {F : C3.RealField r} {entries selected} →
  selected Cube.∉ Fixed.modeList entries →
  Fixed.positiveModeOccurs entries selected ≡ false
positiveModeOccursFalseWhenAbsent {entries = []} absent = refl
positiveModeOccursFalseWhenAbsent {entries = head ∷ rest} {selected} absent
  with Output.modeEqual selected (Fixed.mode head) in equality
... | true =
  let
    same = Output.modeEqualSound equality
    member : selected Cube.∈ Fixed.modeList (head ∷ rest)
    member = Cube.here same
  in
  Output.falseNotTrue (absent member)
... | false =
  positiveModeOccursFalseWhenAbsent
    (λ member → absent (Cube.there member))

lookupNegativeExact :
  ∀ {r} {F : C3.RealField r} {entries}
    (noDuplicates : Cube.NoDuplicates (Fixed.modeList entries))
    (entry : Fixed.CanonicalModeValue F) →
  entry Cube.∈ entries →
  Fixed.lookupNegative entries (Z3.negateMode (Fixed.mode entry))
    ≡ C3.complex3Conjugate (Fixed.value entry)
lookupNegativeExact {entries = []} noDuplicates entry ()
lookupNegativeExact {entries = head ∷ rest}
    (Cube.unique∷ fresh tailUnique) entry (Cube.here refl)
  rewrite Output.modeEqualRefl (Z3.negateMode (Fixed.mode head)) = refl
lookupNegativeExact {entries = head ∷ rest}
    (Cube.unique∷ fresh tailUnique) entry (Cube.there member)
  with Output.modeEqual
    (Z3.negateMode (Fixed.mode entry))
    (Z3.negateMode (Fixed.mode head)) in equality
... | true =
  let
    negSame = Output.modeEqualSound equality
    same : Fixed.mode entry ≡ Fixed.mode head
    same = trans
      (sym (Symmetry.negateModeInvolutive (Fixed.mode entry)))
      (trans (cong Z3.negateMode negSame)
        (Symmetry.negateModeInvolutive (Fixed.mode head)))
    entryModeTail : Fixed.mode entry Cube.∈ Fixed.modeList rest
    entryModeTail = entryModeMember member
    headModeTail : Fixed.mode head Cube.∈ Fixed.modeList rest
    headModeTail = subst
      (λ selected → selected Cube.∈ Fixed.modeList rest)
      same entryModeTail
  in
  Output.falseNotTrue (fresh headModeTail)
... | false = lookupNegativeExact tailUnique entry member

stateEntryModeCanonicalMember :
  ∀ {r} {F : C3.RealField r} {N}
    (state : Fixed.CanonicalRealityState F N)
    (entry : Fixed.CanonicalModeValue F) →
  entry Cube.∈ Fixed.positiveValues state →
  Fixed.mode entry Cube.∈ Orbit.canonicalCutoffOrbitModes N
stateEntryModeCanonicalMember state entry member =
  subst
    (λ modes → Fixed.mode entry Cube.∈ modes)
    (Fixed.positiveModesExact state)
    (entryModeMember member)

negativeModeAbsentFromPositiveList :
  ∀ {r} {F : C3.RealField r} {N}
    (state : Fixed.CanonicalRealityState F N)
    (entry : Fixed.CanonicalModeValue F) →
  entry Cube.∈ Fixed.positiveValues state →
  Z3.negateMode (Fixed.mode entry)
    Cube.∉ Fixed.modeList (Fixed.positiveValues state)
negativeModeAbsentFromPositiveList {N = N} state entry member negMember =
  let
    positiveMember = stateEntryModeCanonicalMember state entry member
    nonzero : Z3.NonZeroMode (Fixed.mode entry)
    nonzero = record
      { notZero = λ zeroEquality →
          Orbit.canonicalCutoffExcludesZero N
            (subst
              (λ selected → selected Cube.∈ Orbit.canonicalCutoffOrbitModes N)
              (sym zeroEquality) positiveMember)
      }
    canonicalNegMember :
      Z3.negateMode (Fixed.mode entry)
        Cube.∈ Orbit.canonicalCutoffOrbitModes N
    canonicalNegMember =
      subst
        (λ modes → Z3.negateMode (Fixed.mode entry) Cube.∈ modes)
        (Fixed.positiveModesExact state)
        negMember
  in
  Orbit.canonicalCutoffNeverContainsOppositePair
    nonzero positiveMember canonicalNegMember

positiveModeOccursAtMember :
  ∀ {r} {F : C3.RealField r} {entries}
    (entry : Fixed.CanonicalModeValue F) →
  entry Cube.∈ entries →
  Fixed.positiveModeOccurs entries (Fixed.mode entry) ≡ true
positiveModeOccursAtMember entry {entries = []} ()
positiveModeOccursAtMember entry {entries = head ∷ rest} (Cube.here refl)
  rewrite Output.modeEqualRefl (Fixed.mode head) = refl
positiveModeOccursAtMember entry {entries = head ∷ rest} (Cube.there member)
  with Output.modeEqual (Fixed.mode entry) (Fixed.mode head)
... | true = refl
... | false = positiveModeOccursAtMember entry member

realityVelocityPositiveExact :
  ∀ {r} {F : C3.RealField r} {N}
    (state : Fixed.CanonicalRealityState F N)
    (entry : Fixed.CanonicalModeValue F) →
  entry Cube.∈ Fixed.positiveValues state →
  Fixed.realityVelocity state (Fixed.mode entry) ≡ Fixed.value entry
realityVelocityPositiveExact state entry member
  with Fixed.positiveModeOccurs (Fixed.positiveValues state) (Fixed.mode entry)
       in occurs
... | true =
  lookupPositiveExact (stateModeListNoDuplicates state) entry member
... | false =
  Output.falseNotTrue
    (trans (sym occurs) (positiveModeOccursAtMember entry member))

realityVelocityNegativeExact :
  ∀ {r} {F : C3.RealField r} {N}
    (state : Fixed.CanonicalRealityState F N)
    (entry : Fixed.CanonicalModeValue F) →
  entry Cube.∈ Fixed.positiveValues state →
  Fixed.realityVelocity state (Z3.negateMode (Fixed.mode entry))
    ≡ C3.complex3Conjugate (Fixed.value entry)
realityVelocityNegativeExact state entry member
  rewrite positiveModeOccursFalseWhenAbsent
    (negativeModeAbsentFromPositiveList state entry member) =
  lookupNegativeExact (stateModeListNoDuplicates state) entry member

round71FixedRealityPositiveLookupExact : Bool
round71FixedRealityPositiveLookupExact = true

round71FixedRealityNegativeLookupExact : Bool
round71FixedRealityNegativeLookupExact = true

round71RealityBuiltIntoFiniteState : Bool
round71RealityBuiltIntoFiniteState = true

round71RealityBuiltIntoFiniteStateIsTrue :
  round71RealityBuiltIntoFiniteState ≡ true
round71RealityBuiltIntoFiniteStateIsTrue = refl
