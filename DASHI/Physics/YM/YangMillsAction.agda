module DASHI.Physics.YM.YangMillsAction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming
  (_+_ to _+ℤ_)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Finite SU(2) carrier and local bracket table.
--
-- This module is self-contained so it does not depend on the current sibling
-- YM stubs, which are still under active development elsewhere in the tree.

data SU2Gen : Set where
  T1 T2 T3 : SU2Gen

data SU2Signed : Set where
  zero : SU2Signed
  plus : SU2Gen → SU2Signed
  minus : SU2Gen → SU2Signed

bracket : SU2Gen → SU2Gen → SU2Signed
bracket T1 T2 = plus T3
bracket T2 T3 = plus T1
bracket T3 T1 = plus T2
bracket T2 T1 = minus T3
bracket T3 T2 = minus T1
bracket T1 T3 = minus T2
bracket T1 T1 = zero
bracket T2 T2 = zero
bracket T3 T3 = zero

SU2Element : Set
SU2Element = List SU2Signed

data LatticeSite : Set where
  source target : LatticeSite

data LatticeEdge : Set where
  edge01 : LatticeEdge

GaugeField : Set
GaugeField = LatticeEdge → SU2Element

zeroElement : SU2Element
zeroElement = []

F_A : GaugeField → LatticeEdge → LatticeEdge → SU2Element
F_A _ _ _ = zeroElement

------------------------------------------------------------------------
-- Killing form on the finite signed SU(2) carrier.

negTwo : ℤ
negTwo = -[1+ 1 ]

two : ℤ
two = + 2

killingSigned : SU2Signed → SU2Signed → ℤ
killingSigned zero _ = + 0
killingSigned _ zero = + 0
killingSigned (plus T1) (plus T1) = negTwo
killingSigned (plus T1) (minus T1) = two
killingSigned (minus T1) (plus T1) = two
killingSigned (minus T1) (minus T1) = negTwo
killingSigned (plus T2) (plus T2) = negTwo
killingSigned (plus T2) (minus T2) = two
killingSigned (minus T2) (plus T2) = two
killingSigned (minus T2) (minus T2) = negTwo
killingSigned (plus T3) (plus T3) = negTwo
killingSigned (plus T3) (minus T3) = two
killingSigned (minus T3) (plus T3) = two
killingSigned (minus T3) (minus T3) = negTwo
killingSigned _ _ = + 0

-- Lift the signed carrier to the list-shaped SU2Element used by the finite
-- carrier style elsewhere in the repo.
killingForm : SU2Element → SU2Element → ℤ
killingForm [] [] = + 0
killingForm [] (_ ∷ _) = + 0
killingForm (_ ∷ _) [] = + 0
killingForm (x ∷ xs) (y ∷ ys) = killingSigned x y +ℤ killingForm xs ys

------------------------------------------------------------------------
-- Ad-invariance on the finite basis.

adInvariance : ∀ i j k →
  killingSigned (bracket i j) (plus k) ≡ killingSigned (plus i) (bracket j k)
adInvariance T1 T1 T1 = refl
adInvariance T1 T1 T2 = refl
adInvariance T1 T1 T3 = refl
adInvariance T1 T2 T1 = refl
adInvariance T1 T2 T2 = refl
adInvariance T1 T2 T3 = refl
adInvariance T1 T3 T1 = refl
adInvariance T1 T3 T2 = refl
adInvariance T1 T3 T3 = refl
adInvariance T2 T1 T1 = refl
adInvariance T2 T1 T2 = refl
adInvariance T2 T1 T3 = refl
adInvariance T2 T2 T1 = refl
adInvariance T2 T2 T2 = refl
adInvariance T2 T2 T3 = refl
adInvariance T2 T3 T1 = refl
adInvariance T2 T3 T2 = refl
adInvariance T2 T3 T3 = refl
adInvariance T3 T1 T1 = refl
adInvariance T3 T1 T2 = refl
adInvariance T3 T1 T3 = refl
adInvariance T3 T2 T1 = refl
adInvariance T3 T2 T2 = refl
adInvariance T3 T2 T3 = refl
adInvariance T3 T3 T1 = refl
adInvariance T3 T3 T2 = refl
adInvariance T3 T3 T3 = refl

------------------------------------------------------------------------
-- Finite plaquette carrier and action.

data Plaquette : Set where
  p12 p23 p31 : Plaquette

plaquettes : List Plaquette
plaquettes = p12 ∷ p23 ∷ p31 ∷ []

fieldStrengthAtPlaquette : GaugeField → Plaquette → SU2Element
fieldStrengthAtPlaquette A p = F_A A edge01 edge01

traceSquare : SU2Element → ℤ
traceSquare x = killingForm x x

plaquetteAction : GaugeField → Plaquette → ℤ
plaquetteAction A p = traceSquare (fieldStrengthAtPlaquette A p)

sumPlaquettes : GaugeField → List Plaquette → ℤ
sumPlaquettes A [] = + 0
sumPlaquettes A (p ∷ ps) = plaquetteAction A p +ℤ sumPlaquettes A ps

ymAction : GaugeField → ℤ
ymAction A = sumPlaquettes A plaquettes

------------------------------------------------------------------------
-- Honest Bianchi proxy.
--
-- The current lattice API exposed by the sibling modules still only carries a
-- flat zero-curvature proxy, so the exact covariant D_A F_A = 0 law is not
-- available here.  What we can prove concretely is that the present field
-- strength evaluates definitionally to the zero carrier.

bianchi : (A : GaugeField) (e1 e2 e3 : LatticeEdge) → F_A A e1 e2 ≡ zeroElement
bianchi _ _ _ _ = refl
