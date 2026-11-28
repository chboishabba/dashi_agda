module DASHI.Algebra.TriadicFiniteSignedIntegerWeldExact where

-- Connect the ORIGINAL quotient prefix to the ORIGINAL Tekum/Hunhold signed
-- integer evaluator and its proved centered reconstruction. The older
-- numericRepresentative is a radix-label codec, not this carry semantics.
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base as Z using (ℤ; +_; -[1+_]; _+_; _*_)
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as E
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteArithmetic as A
import DASHI.Algebra.Trit as T
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as P
import DASHI.Algebra.BalancedTernaryCenteredReconstructionExact as C

toTrit : E.Trit → T.Trit
toTrit E.neg = T.neg
toTrit E.zer = T.zer
toTrit E.pos = T.pos

fromTrit : T.Trit → E.Trit
fromTrit T.neg = E.neg
fromTrit T.zer = E.zer
fromTrit T.pos = E.pos

toVec : ∀ {n} → Q.Residue3Pow n → Vec T.Trit n
toVec E.[] = vnil
toVec (t E.∷ ts) = toTrit t vcons toVec ts

fromVec : ∀ {n} → Vec T.Trit n → Q.Residue3Pow n
fromVec vnil = E.[]
fromVec (t vcons ts) = fromTrit t E.∷ fromVec ts

prefixRoundTrip : ∀ {n} (x : Q.Residue3Pow n) → fromVec (toVec x) ≡ x
prefixRoundTrip E.[] = refl
prefixRoundTrip (E.neg E.∷ ts) rewrite prefixRoundTrip ts = refl
prefixRoundTrip (E.zer E.∷ ts) rewrite prefixRoundTrip ts = refl
prefixRoundTrip (E.pos E.∷ ts) rewrite prefixRoundTrip ts = refl

vecRoundTrip : ∀ {n} (x : Vec T.Trit n) → toVec (fromVec x) ≡ x
vecRoundTrip vnil = refl
vecRoundTrip (T.neg vcons ts) rewrite vecRoundTrip ts = refl
vecRoundTrip (T.zer vcons ts) rewrite vecRoundTrip ts = refl
vecRoundTrip (T.pos vcons ts) rewrite vecRoundTrip ts = refl

signedValue : ∀ {n} → Q.Residue3Pow n → ℤ
signedValue x = BT.toInteger (BT.eval (toVec x))

signedCons : ∀ {n} (t : E.Trit) (ts : Q.Residue3Pow n) →
  signedValue (t E.∷ ts) ≡ P.digitInteger (toTrit t) Z.+ ((+ 3) Z.* signedValue ts)
signedCons t ts = P.evalIntegerCons (toTrit t) (toVec ts)

signedInjective : ∀ {n} {x y : Q.Residue3Pow n} →
  signedValue x ≡ signedValue y → x ≡ y
signedInjective {x = x} {y = y} eq =
  trans (sym (prefixRoundTrip x))
    (trans (cong fromVec (P.toIntegerInjective eq)) (prefixRoundTrip y))

centered : ∀ {n} → Q.Residue3Pow n → C.CenteredInteger n
centered x = C.encodeCentered (toVec x)

uncentered : ∀ {n} → C.CenteredInteger n → Q.Residue3Pow n
uncentered x = fromVec (C.decodeCentered x)

uncenterCenter : ∀ {n} (x : Q.Residue3Pow n) → uncentered (centered x) ≡ x
uncenterCenter x =
  trans (cong fromVec (C.decodeEncodeCentered (toVec x))) (prefixRoundTrip x)

centerUncenter : ∀ {n} (x : C.CenteredInteger n) → centered (uncentered x) ≡ x
centerUncenter x =
  trans (cong C.encodeCentered (vecRoundTrip (C.decodeCentered x))) (C.encodeDecodeCentered x)

centeredIsSigned : ∀ {n} (x : Q.Residue3Pow n) → C.centeredValue (centered x) ≡ signedValue x
centeredIsSigned x = C.centeredValueEncode (toVec x)

-- Literal counterexample at depth two: replacing neg with ordinary digit 2
-- without propagating a carry changes the integer residue modulo nine.
minusOne : Q.Residue3Pow 2
minusOne = E.neg E.∷ E.zer E.∷ E.[]

minusOneSigned : signedValue minusOne ≡ -[1+ 0 ]
minusOneSigned = refl

minusOneRadixLabel : Q.numericRepresentative minusOne ≡ 2
minusOneRadixLabel = refl

plusOne : Q.Residue3Pow 2
plusOne = E.pos E.∷ E.zer E.∷ E.[]

oldLabelsDoNotAddModuloNine : Q.numericRepresentative (A.addResidue minusOne plusOne) ≡ 0
oldLabelsDoNotAddModuloNine = refl

-- Next: carry semantics of A.addWithCarry and compatible multiplication
-- modulo 3^n, then use the existing pinned Mathlib PadicInt.lift/spec/ext.
-- No second signed evaluator or claim of a checked cross-kernel ring map.
