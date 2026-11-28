module DASHI.Mathematics.Complexity.PNPQuadraticMobiusExact where

-- Classical finite-field completion of the square and Boolean
-- inclusion-exclusion. Reuse the actual Base369 F3 and C3 histogram
-- owners. Native source; full table and kernel reification are separate.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)
open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)
import DASHI.Foundations.Base369TriTruthField as F
import DASHI.Mathematics.Complexity.PNPF3SyndromeBoundaryExact as S
import DASHI.Mathematics.Complexity.PNPSignedCharacterTailExact as H
import DASHI.Mathematics.Complexity.PNPDualSyndromeFourierExact as D

square : TriTruth → TriTruth
square x = F.triMul x x

quad : TriTruth → TriTruth → TriTruth → TriTruth
quad a b x = F.triAdd (F.triMul a (square x)) (F.triMul b x)

shift : TriTruth → TriTruth → TriTruth → TriTruth
shift a b x = F.triAdd (F.triNeg (F.triMul a b)) x

unshift : TriTruth → TriTruth → TriTruth → TriTruth
unshift a b x = F.triAdd (F.triMul a b) x

shiftUnshift : ∀ a b x → shift a b (unshift a b x) ≡ x
shiftUnshift a b x = S.cancelTrit (F.triMul a b) x

unshiftShift : ∀ a b x → unshift a b (shift a b x) ≡ x
unshiftShift a b x = S.restoreTrit (F.triMul a b) x

completed : TriTruth → TriTruth → TriTruth → TriTruth
completed a b x =
  F.triAdd (F.triMul a (square (shift a b x)))
    (F.triNeg (F.triMul a (square b)))

completeMid : ∀ b x → quad tri-mid b x ≡ completed tri-mid b x
completeMid tri-low tri-low = refl
completeMid tri-low tri-mid = refl
completeMid tri-low tri-high = refl
completeMid tri-mid tri-low = refl
completeMid tri-mid tri-mid = refl
completeMid tri-mid tri-high = refl
completeMid tri-high tri-low = refl
completeMid tri-high tri-mid = refl
completeMid tri-high tri-high = refl

completeHigh : ∀ b x → quad tri-high b x ≡ completed tri-high b x
completeHigh tri-low tri-low = refl
completeHigh tri-low tri-mid = refl
completeHigh tri-low tri-high = refl
completeHigh tri-mid tri-low = refl
completeHigh tri-mid tri-mid = refl
completeHigh tri-mid tri-high = refl
completeHigh tri-high tri-low = refl
completeHigh tri-high tri-mid = refl
completeHigh tri-high tri-high = refl

axisQuad : TriTruth → TriTruth → H.Hist
axisQuad a b = S.hadd (D.phase (quad a b tri-low))
  (S.hadd (D.phase (quad a b tri-mid)) (D.phase (quad a b tri-high)))

factorAxis : TriTruth → TriTruth → H.Hist
factorAxis a b =
  H.conv (D.phase (F.triNeg (F.triMul a (square b)))) (axisQuad a tri-low)

gaussMid : ∀ b → axisQuad tri-mid b ≡ factorAxis tri-mid b
gaussMid tri-low = refl
gaussMid tri-mid = refl
gaussMid tri-high = refl

gaussHigh : ∀ b → axisQuad tri-high b ≡ factorAxis tri-high b
gaussHigh tri-low = refl
gaussHigh tri-mid = refl
gaussHigh tri-high = refl

-- Falsifying clause fibres are Boolean partial assignments. Impossible
-- is retained until the indicator vanishes, never interpreted as a
-- refused or unexamined source.
data Pin : Set where
  any off on impossible : Pin

_and_ : Bool → Bool → Bool
true and b = b
false and b = false

allows : Pin → Bool → Bool
allows any b = true
allows off false = true
allows off true = false
allows on false = false
allows on true = true
allows impossible b = false

meet : Pin → Pin → Pin
meet any q = q
meet off any = off
meet off off = off
meet off on = impossible
meet off impossible = impossible
meet on any = on
meet on off = impossible
meet on on = on
meet on impossible = impossible
meet impossible q = impossible

pinMeetExact : ∀ p q b → allows (meet p q) b ≡ (allows p b and allows q b)
pinMeetExact any any false = refl
pinMeetExact any any true = refl
pinMeetExact any off false = refl
pinMeetExact any off true = refl
pinMeetExact any on false = refl
pinMeetExact any on true = refl
pinMeetExact any impossible false = refl
pinMeetExact any impossible true = refl
pinMeetExact off any false = refl
pinMeetExact off any true = refl
pinMeetExact off off false = refl
pinMeetExact off off true = refl
pinMeetExact off on false = refl
pinMeetExact off on true = refl
pinMeetExact off impossible false = refl
pinMeetExact off impossible true = refl
pinMeetExact on any false = refl
pinMeetExact on any true = refl
pinMeetExact on off false = refl
pinMeetExact on off true = refl
pinMeetExact on on false = refl
pinMeetExact on on true = refl
pinMeetExact on impossible false = refl
pinMeetExact on impossible true = refl
pinMeetExact impossible any false = refl
pinMeetExact impossible any true = refl
pinMeetExact impossible off false = refl
pinMeetExact impossible off true = refl
pinMeetExact impossible on false = refl
pinMeetExact impossible on true = refl
pinMeetExact impossible impossible false = refl
pinMeetExact impossible impossible true = refl

andInterchange : ∀ a b c d → ((a and b) and (c and d)) ≡ ((a and c) and (b and d))
andInterchange false false false false = refl
andInterchange false false false true = refl
andInterchange false false true false = refl
andInterchange false false true true = refl
andInterchange false true false false = refl
andInterchange false true false true = refl
andInterchange false true true false = refl
andInterchange false true true true = refl
andInterchange true false false false = refl
andInterchange true false false true = refl
andInterchange true false true false = refl
andInterchange true false true true = refl
andInterchange true true false false = refl
andInterchange true true false true = refl
andInterchange true true true false = refl
andInterchange true true true true = refl

Cube : Nat → Set
Cube n = Vec Pin n

intersect : ∀ {n} → Cube n → Cube n → Cube n
intersect [] [] = []
intersect (p ∷ ps) (q ∷ qs) = meet p q ∷ intersect ps qs

holds : ∀ {n} → Cube n → Vec Bool n → Bool
holds [] [] = true
holds (p ∷ ps) (b ∷ bs) = allows p b and holds ps bs

intersectionExact : ∀ {n} (p q : Cube n) x →
  holds (intersect p q) x ≡ (holds p x and holds q x)
intersectionExact [] [] [] = refl
intersectionExact (p ∷ ps) (q ∷ qs) (x ∷ xs) =
  trans (cong₂ _and_ (pinMeetExact p q x) (intersectionExact ps qs xs))
    (andInterchange (allows p x) (allows q x) (holds ps xs) (holds qs xs))
