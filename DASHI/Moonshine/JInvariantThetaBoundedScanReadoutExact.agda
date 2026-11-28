module DASHI.Moonshine.JInvariantThetaBoundedScanReadoutExact where

-- Source-written, kernel pending. Connect the literal finite exponent
-- scans to the graded Cauchy product; no replacement theta coefficients.
open import Agda.Builtin.Nat using (Nat; zero; suc) renaming (_*_ to _*N_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Data.Integer using (ℤ; +_; _+_; _*_)
import Data.Integer.Properties as Z
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; cong₂; sym; trans; subst)
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as One
import DASHI.Moonshine.JInvariantThetaLegendreSignedGeometryExact as T
import DASHI.Moonshine.JInvariantThetaGradedCauchyCountExact as G

deltaSame : ∀ n → G.delta n n ≡ + 1
deltaSame zero = refl
deltaSame (suc n) = deltaSame n

deltaDifferent : ∀ k n → k ≢ n → G.delta k n ≡ + 0
deltaDifferent zero zero neq = ⊥-elim (neq refl)
deltaDifferent zero (suc n) neq = refl
deltaDifferent (suc k) zero neq = refl
deltaDifferent (suc k) (suc n) neq = deltaDifferent k n (λ e → neq (cong suc e))

scan : (Nat → Nat) → Nat → List Nat
scan f zero = f zero ∷ []
scan f (suc k) = f (suc k) ∷ scan f k

scanRead : ∀ f n k → G.hist (scan f k) n ≡ + T.count f n k
scanRead f n zero with f zero NP.≟ n
... | yes eq rewrite eq | deltaSame n = refl
... | no neq rewrite deltaDifferent (f zero) n neq = refl
scanRead f n (suc k) with f (suc k) NP.≟ n
... | yes eq rewrite eq | deltaSame n | scanRead f n k = refl
... | no neq rewrite deltaDifferent (f (suc k)) n neq | scanRead f n k = refl

-- Once the scan has passed the requested degree, new indices cannot
-- contribute because f(j) >= j.
stable : ∀ f → (∀ k → k ≤ f k) → ∀ n k → n ≤ k →
  T.count f n k ≡ T.count f n n
stable f bound zero zero h = refl
stable f bound (suc n) zero ()
stable f bound n (suc k) h with n NP.≟ suc k
... | yes refl = refl
... | no neq with f (suc k) NP.≟ n
...   | yes eq = ⊥-elim
  (NP.1+n≰n (NP.≤-trans (subst (suc k ≤_) eq (bound (suc k)))
    (One.≤-pred (One.strictFromLeDifferent h neq))))
...   | no ne = stable f bound n k (One.≤-pred (One.strictFromLeDifferent h neq))

squareBound : ∀ k → k ≤ T.sqN k
squareBound zero = z≤n
squareBound (suc k) = NP.m≤m*n (suc k) (suc k)

triBound : ∀ k → k ≤ T.triN k
triBound k = NP.m≤m*n k (suc k)

halfAt : ∀ cutoff n → n ≤ cutoff → G.hist (scan T.triN cutoff) n ≡ T.halfTheta n
halfAt cutoff n h = trans (scanRead T.triN n cutoff)
  (cong +_ (stable T.triN triBound n cutoff h))

-- Positive magnitude labels have two independent signs. Zero is
-- deliberately single, not two coincident signed zeros.
positive : (Nat → Nat) → Nat → List Nat
positive f zero = []
positive f (suc k) = f (suc k) ∷ positive f k

positiveRead : ∀ f n k → f zero ≢ n →
  G.hist (positive f k) n ≡ + T.count f n k
positiveRead f n zero neq with f zero NP.≟ n
... | yes eq = ⊥-elim (neq eq)
... | no ne = refl
positiveRead f n (suc k) neq with f (suc k) NP.≟ n
... | yes eq rewrite eq | deltaSame n | positiveRead f n k neq = refl
... | no ne rewrite deltaDifferent (f (suc k)) n ne | positiveRead f n k neq = refl

positiveZero : ∀ f → (∀ k → f (suc k) ≢ zero) → ∀ cutoff →
  G.hist (positive f cutoff) zero ≡ + 0
positiveZero f nonzero zero = refl
positiveZero f nonzero (suc k) rewrite deltaDifferent (f (suc k)) zero (nonzero k)
  | positiveZero f nonzero k = refl

squareNonzero : ∀ k → T.sqN (suc k) ≢ zero
squareNonzero k eq = NP.1+n≰n
  (subst (suc k ≤_) eq (squareBound (suc k)))

squareScan : Nat → List Nat
squareScan k = zero ∷ (positive T.sqN k ++ positive T.sqN k)

squareAt : ∀ cutoff n → n ≤ cutoff → G.hist (squareScan cutoff) n ≡ T.theta3 n
squareAt cutoff zero h
  rewrite G.histAppend (positive T.sqN cutoff) (positive T.sqN cutoff) zero
    | positiveZero T.sqN squareNonzero cutoff = refl
squareAt cutoff (suc n) h =
  let m = T.count T.sqN (suc n) (suc n)
      e = trans (positiveRead T.sqN (suc n) cutoff (λ ()))
        (cong +_ (stable T.sqN squareBound (suc n) cutoff h))
  in trans (cong ((+ 0) +_) (G.histAppend (positive T.sqN cutoff) (positive T.sqN cutoff) (suc n)))
    (trans (Z.+-identityˡ _)
      (trans (cong₂ _+_ e e)
        (sym (solve 1 (λ x → con (+ 2) :* x := x :+ x) refl (+ m)))))

-- Every index, including zero, on the original integer fourth powers.
BCount : ∀ cutoff n → n ≤ cutoff →
  G.hist (G.fourGrades (squareScan cutoff)) n ≡ T.B n
BCount cutoff n h = G.fourCountThrough (squareScan cutoff) T.theta3 n
  (λ i hi → squareAt cutoff i (NP.≤-trans hi h))

HCount : ∀ cutoff n → n ≤ cutoff →
  G.hist (G.fourGrades (scan T.triN cutoff)) n ≡ T.fourth T.halfTheta n
HCount cutoff n h = G.fourCountThrough (scan T.triN cutoff) T.halfTheta n
  (λ i hi → halfAt cutoff i (NP.≤-trans hi h))
