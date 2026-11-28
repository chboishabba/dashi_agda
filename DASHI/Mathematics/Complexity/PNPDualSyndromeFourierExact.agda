module DASHI.Mathematics.Complexity.PNPDualSyndromeFourierExact where

-- Classical character orthogonality on the direct product F3^r.
-- Reuse the previous histogram/convolution, rational mass and Gram owners.
-- No heavy-character oracle or global low-rank assertion.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base using (Vec; []; _∷_)
import Data.List.Base as List
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as Q
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)
open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)
import DASHI.Foundations.Base369TriTruthField as F
import DASHI.Mathematics.Complexity.PNPSignedCharacterTailExact as H
import DASHI.Mathematics.Complexity.PNPF3SyndromeBoundaryExact as S
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as CS

three : ℚ
three = 1ℚ + 1ℚ + 1ℚ

phase : TriTruth → H.Hist
phase tri-low = H.hist 1ℚ 0ℚ 0ℚ
phase tri-mid = H.hist 0ℚ 1ℚ 0ℚ
phase tri-high = H.hist 0ℚ 0ℚ 1ℚ

-- Every dual choice occurs once. The recursion is the factored
-- exact histogram of the dot product over the full dual carrier.
axis : TriTruth → H.Hist
axis a = S.hadd (phase (F.triMul tri-low a))
  (S.hadd (phase (F.triMul tri-mid a)) (phase (F.triMul tri-high a)))

orthHistogram : ∀ {n} → Vec TriTruth n → H.Hist
orthHistogram [] = phase tri-low
orthHistogram (a ∷ as) = H.conv (axis a) (orthHistogram as)

pow3 : Nat → ℚ
pow3 zero = 1ℚ
pow3 (suc n) = three * pow3 n

axisMass : ∀ a → S.mass (axis a) ≡ three
axisMass tri-low = refl
axisMass tri-mid = refl
axisMass tri-high = refl

orthMass : ∀ {n} (v : Vec TriTruth n) → S.mass (orthHistogram v) ≡ pow3 n
orthMass [] = refl
orthMass (a ∷ as)
  rewrite S.massProduct (axis a) (orthHistogram as)
        | axisMass a | orthMass as = refl

allZero : ∀ {n} → Vec TriTruth n → Bool
allZero [] = true
allZero (tri-low ∷ as) = allZero as
allZero (tri-mid ∷ as) = false
allZero (tri-high ∷ as) = false

axisMidEnergy : H.energy (axis tri-mid) ≡ 0ℚ
axisMidEnergy = refl

axisHighEnergy : H.energy (axis tri-high) ≡ 0ℚ
axisHighEnergy = refl

orthZeroEnergy : ∀ {n} (v : Vec TriTruth n) → allZero v ≡ false →
  H.energy (orthHistogram v) ≡ 0ℚ
orthZeroEnergy [] ()
orthZeroEnergy (tri-low ∷ as) h
  rewrite H.energyProduct (axis tri-low) (orthHistogram as)
        | orthZeroEnergy as h = Q.*-zeroʳ _
orthZeroEnergy (tri-mid ∷ as) h
  rewrite H.energyProduct (axis tri-mid) (orthHistogram as)
        | axisMidEnergy = Q.*-zeroˡ _
orthZeroEnergy (tri-high ∷ as) h
  rewrite H.energyProduct (axis tri-high) (orthHistogram as)
        | axisHighEnergy = Q.*-zeroˡ _

zeroAxisProduct : ∀ a → H.conv (axis tri-low) (H.hist a 0ℚ 0ℚ) ≡
  H.hist (three * a) 0ℚ 0ℚ
zeroAxisProduct a = H.histEq (solve (a List.∷ List.[]))
  (solve (a List.∷ List.[])) (solve (a List.∷ List.[]))

orthIdentity : ∀ {n} (v : Vec TriTruth n) → allZero v ≡ true →
  orthHistogram v ≡ H.hist (pow3 n) 0ℚ 0ℚ
orthIdentity [] h = refl
orthIdentity (tri-low ∷ as) h rewrite orthIdentity as h = zeroAxisProduct _
orthIdentity (tri-mid ∷ as) ()
orthIdentity (tri-high ∷ as) ()

-- For actual retained/omitted finite mode lists use the exact existing
-- rational Gram inequality, not an assumed small Fourier tail.
-- Phases are carried by the histograms before projection; the factor
-- 1/3^r is accounted in the consumer's normalization.
dualDirectionalTailSquared :
  (modes : List.List (H.Hist × H.Hist)) →
  CS.square (H.projectionSum modes) ≤ H.leftEnergy4 modes * H.rightEnergy4 modes
dualDirectionalTailSquared = H.boundaryTailSquared

-- The nonconstant characters themselves vanish, not merely their
-- energies. This avoids relying on a floating square-root decision.
axisMidA : H.ca (axis tri-mid) ≡ 0ℚ
axisMidA = refl
axisMidB : H.cb (axis tri-mid) ≡ 0ℚ
axisMidB = refl
axisHighA : H.ca (axis tri-high) ≡ 0ℚ
axisHighA = refl
axisHighB : H.cb (axis tri-high) ≡ 0ℚ
axisHighB = refl

open import Data.Product using (proj₁; proj₂)

zeroCharacterLeft : ∀ h k → H.ca h ≡ 0ℚ → H.cb h ≡ 0ℚ →
  (H.ca (H.conv h k) ≡ 0ℚ) × (H.cb (H.conv h k) ≡ 0ℚ)
zeroCharacterLeft h k a b
  rewrite H.characterA h k | H.characterB h k | a | b =
  solve (H.ca k List.∷ H.cb k List.∷ List.[]) ,
  solve (H.ca k List.∷ H.cb k List.∷ List.[])

zeroCharacterRight : ∀ h k → H.ca k ≡ 0ℚ → H.cb k ≡ 0ℚ →
  (H.ca (H.conv h k) ≡ 0ℚ) × (H.cb (H.conv h k) ≡ 0ℚ)
zeroCharacterRight h k a b
  rewrite H.characterA h k | H.characterB h k | a | b =
  solve (H.ca h List.∷ H.cb h List.∷ List.[]) ,
  solve (H.ca h List.∷ H.cb h List.∷ List.[])

orthVanishing : ∀ {n} (v : Vec TriTruth n) → allZero v ≡ false →
  (H.ca (orthHistogram v) ≡ 0ℚ) × (H.cb (orthHistogram v) ≡ 0ℚ)
orthVanishing [] ()
orthVanishing (tri-low ∷ as) h =
  zeroCharacterRight (axis tri-low) (orthHistogram as)
    (proj₁ (orthVanishing as h)) (proj₂ (orthVanishing as h))
orthVanishing (tri-mid ∷ as) h =
  zeroCharacterLeft (axis tri-mid) (orthHistogram as) axisMidA axisMidB
orthVanishing (tri-high ∷ as) h =
  zeroCharacterLeft (axis tri-high) (orthHistogram as) axisHighA axisHighB
