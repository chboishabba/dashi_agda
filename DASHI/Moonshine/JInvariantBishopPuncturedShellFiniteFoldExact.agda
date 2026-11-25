module DASHI.Moonshine.JInvariantBishopPuncturedShellFiniteFoldExact where

-- Actual source square-shell list, literal punctured Bishop summands.
-- A guard produces a proof of membership before constructing a reciprocal.
-- No reciprocal or assigned summand at the origin.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Unit using (tt)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool.Base using (T)
open import Data.Product using (_,_)
open import Data.Bool.Properties using (T-∧)
open import Function.Bundles using (Equivalence)
open import Data.Nat.Base using (z≤n)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import Real as R
import RealProperties as RP
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopPositiveCrossReciprocalUpperExact as Cross
import DASHI.Foundations.BishopSquareNonnegativeExact as NN
import DASHI.Foundations.BishopCubicTranslationIteratedExact as N
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Len
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact as S
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopLatticeReciprocalShellMajorantExact as Major
import DASHI.Moonshine.JInvariantBishopLatticeEvenPowerShellMajorantExact as E
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L

originInside : ∀ n → T (S.insideSquare? n K.origin)
originInside n = Equivalence.from T-∧
  (Radius.positiveInCutoff n 0 z≤n , Radius.positiveInCutoff n 0 z≤n)

falseImpossible : T false → L.⊥
falseImpossible ()

falseOrigin : ∀ n → T (S.onSuccessorSquareShell? n K.origin) → L.⊥
falseOrigin n proof with S.insideSquare? n K.origin | originInside n
... | false | ()
... | true | inside with S.insideSquare? (suc n) K.origin
...   | false = falseImpossible proof
...   | true = falseImpossible proof

nonzero : ∀ n p → T (S.onSuccessorSquareShell? n p) → K.NonzeroLatticePoint
nonzero n p onShell = K.nonzero-lattice-point p
  (λ eq → falseOrigin n (subst (λ q → T (S.onSuccessorSquareShell? n q)) eq onShell))

-- Raw finite square list, guarded by the actual source shell predicate.
-- The bound uses the square cover (not an unproved sharper shell count).
fold : (n : Nat) →
  (K.NonzeroLatticePoint → R.ℝ) → List L.LatticePoint → R.ℝ
fold n f [] = R.0ℝ
fold n f (p ∷ ps) with S.onSuccessorSquareShell? n p in eq
... | false = fold n f ps
... | true = R._+_ (f (nonzero n p (subst T (sym eq) tt))) (fold n f ps)

foldTriangle : ∀ n f ps →
  R._≤_ (R.∣_∣ (fold n f ps)) (fold n (λ i → R.∣_∣ (f i)) ps)
foldTriangle n f [] = RP.≤-reflexive (RP.nonNegx⇒∣x∣≃x RP.nonNeg0)
foldTriangle n f (p ∷ ps) with S.onSuccessorSquareShell? n p in eq
... | false = foldTriangle n f ps
... | true = RP.≤-trans
  (RP.∣x+y∣≤∣x∣+∣y∣ (f (nonzero n p (subst T (sym eq) tt))) (fold n f ps))
  (RP.+-mono-≤ RP.≤-refl (foldTriangle n f ps))

foldDomination : ∀ n f (m : R.ℝ) →
  R.NonNegative m →
  ((p : L.LatticePoint) → (onShell : T (S.onSuccessorSquareShell? n p)) →
    R._≤_ (f (nonzero n p onShell)) m) →
  (ps : List L.LatticePoint) →
  R._≤_ (fold n f ps) (N.natScale (Len.listLength ps) m)
foldDomination n f m mNN bound [] = RP.≤-refl
foldDomination n f m mNN bound (p ∷ ps)
  with S.onSuccessorSquareShell? n p in eq
... | false =
  RP.≤-trans (foldDomination n f m mNN bound ps)
    (RP.≤-respˡ-≃ (RP.+-identityʳ (N.natScale (Len.listLength ps) m))
      (RP.+-monoʳ-≤ (N.natScale (Len.listLength ps) m) (RP.nonNegx⇒0≤x mNN)))
... | true =
  RP.≤-respʳ-≃ (RP.+-comm m (N.natScale (Len.listLength ps) m))
    (RP.+-mono-≤ (bound p (subst T (sym eq) tt))
      (foldDomination n f m mNN bound ps))

shellComponent : ∀ n → (K.NonzeroLatticePoint → R.ℝ) → R.ℝ
shellComponent n f = fold n f (S.squarePoints (suc n))

shellAbsolute : ∀ n → (K.NonzeroLatticePoint → R.ℝ) → R.ℝ
shellAbsolute n f = shellComponent n (λ i → R.∣_∣ (f i))

shellAbsoluteBound : ∀ n f m →
  R.NonNegative m →
  ((p : L.LatticePoint) → (onShell : T (S.onSuccessorSquareShell? n p)) →
    R._≤_ (R.∣_∣ (f (nonzero n p onShell))) m) →
  R._≤_ (shellAbsolute n f) (R._*_ (N.natReal (S.squareCodeCount (suc n))) m)
shellAbsoluteBound n f m mNN bound =
  RP.≤-respʳ-≃
    (N.natScaleAsEmbeddedNatMul (S.squareCodeCount (suc n)) m)
    (subst (λ k → R._≤_ (shellAbsolute n f) (N.natScale k m))
      (S.squarePointsLength (suc n))
      (foldDomination n (λ i → R.∣_∣ (f i)) m mNN bound
        (S.squarePoints (suc n))))

majorantNN : ∀ tau n → R.NonNegative (E.majorant tau n)
majorantNN tau n = RP.nonNegx,y⇒nonNegx*y
  (RP.nonNegx,y⇒nonNegx+y RP.nonNeg1
    (RP.nonNegx,y⇒nonNegx+y
      (NN.bishopSquareNonnegative (C.im (U.tau tau)))
      (NN.bishopSquareNonnegative (C.re (U.tau tau)))))
  (Cross.positiveInverseNonnegative (Major.weightedRadiusPositive tau n))

real4Abs : ∀ tau n →
  R._≤_ (shellAbsolute n (λ i → C.re (E.summand 4 tau i)))
    (R._*_ (N.natReal (S.squareCodeCount (suc n))) (R.pow (E.majorant tau n) 2))
real4Abs tau n = shellAbsoluteBound n _ _
  (Seq.nonNegx⇒nonNegxⁿ 2 (majorantNN tau n))
  (λ p onShell → E.realWeight4 tau n (nonzero n p onShell) onShell)

imag4Abs : ∀ tau n →
  R._≤_ (shellAbsolute n (λ i → C.im (E.summand 4 tau i)))
    (R._*_ (N.natReal (S.squareCodeCount (suc n))) (R.pow (E.majorant tau n) 2))
imag4Abs tau n = shellAbsoluteBound n _ _
  (Seq.nonNegx⇒nonNegxⁿ 2 (majorantNN tau n))
  (λ p onShell → E.imagWeight4 tau n (nonzero n p onShell) onShell)

real6Abs : ∀ tau n →
  R._≤_ (shellAbsolute n (λ i → C.re (E.summand 6 tau i)))
    (R._*_ (N.natReal (S.squareCodeCount (suc n))) (R.pow (E.majorant tau n) 3))
real6Abs tau n = shellAbsoluteBound n _ _
  (Seq.nonNegx⇒nonNegxⁿ 3 (majorantNN tau n))
  (λ p onShell → E.realWeight6 tau n (nonzero n p onShell) onShell)

imag6Abs : ∀ tau n →
  R._≤_ (shellAbsolute n (λ i → C.im (E.summand 6 tau i)))
    (R._*_ (N.natReal (S.squareCodeCount (suc n))) (R.pow (E.majorant tau n) 3))
imag6Abs tau n = shellAbsoluteBound n _ _
  (Seq.nonNegx⇒nonNegxⁿ 3 (majorantNN tau n))
  (λ p onShell → E.imagWeight6 tau n (nonzero n p onShell) onShell)
