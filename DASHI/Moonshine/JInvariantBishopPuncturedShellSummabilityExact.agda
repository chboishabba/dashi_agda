module DASHI.Moonshine.JInvariantBishopPuncturedShellSummabilityExact where

-- SOURCE-WRITTEN. Actual weight-four/six punctured shell absolute sums:
-- original reciprocal majorant + finite shell count + original Basel.
-- Neither a value of Basel nor a Fourier normalization is assumed.
open import Agda.Builtin.Nat using (Nat; zero; suc) renaming (_+_ to _+N_; _*_ to _*N_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Bool.Base using (T)
open import Data.List.Base using (List; []; _∷_)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import ExtraProperties as Extra
import Data.Nat.Properties as NP
import Data.Nat.Base
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopPositiveCrossReciprocalUpperExact as Cross
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Rec
import DASHI.Foundations.BishopNatRealPositiveExact as Pos
import DASHI.Foundations.BishopInverseSquareProductExact as InvProd
import DASHI.Foundations.BishopSquareNonnegativeExact as NN
import DASHI.Foundations.BishopFiniteSeriesCommonFactorExact as Common
import DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact as NE
import DASHI.Foundations.BishopCubicTranslationIteratedExact as N
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact as S
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopLatticeDenominatorCoercivityExact as Coercive
import DASHI.Moonshine.JInvariantBishopLatticeReciprocalShellMajorantExact as Major
import DASHI.Moonshine.JInvariantBishopLatticeEvenPowerShellMajorantExact as E
import DASHI.Moonshine.JInvariantBishopPuncturedShellFiniteFoldExact as F
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L

module At (tau : U.BishopUpperHalfPlanePoint) where

  y : ℝ
  y = C.im (U.tau tau)

  yInv : ℝ
  yInv = Cross.positiveInverse (U.imaginaryPositive tau)

  c : ℝ
  c = Coercive.coercivityFactor (U.tau tau) * (yInv * yInv)

  cNN : R.NonNegative c
  cNN = P.nonNegx,y⇒nonNegx*y
    (P.nonNegx,y⇒nonNegx+y P.nonNeg1
      (P.nonNegx,y⇒nonNegx+y (NN.bishopSquareNonnegative y)
        (NN.bishopSquareNonnegative (C.re (U.tau tau)))))
    (NN.bishopSquareNonnegative yInv)

  r : Nat → ℝ
  r n = N.natReal (suc n)

  u : Nat → ℝ
  u = Basel.reciprocalSequence

  uNN : ∀ n → R.NonNegative (u n)
  uNN n = P.0≤x⇒nonNegx (P.p≤q⇒p⋆≤q⋆ Q.0ℚᵘ (+ 1 / suc n)
    (QP.nonNegative⁻¹ (+ 1 / suc n)))

  u≤1 : ∀ n → u n ≤ R.1ℝ
  u≤1 n = P.p≤q⇒p⋆≤q⋆ (+ 1 / suc n) Q.1ℚᵘ
    (Extra.q≤r⇒+p/r≤+p/q 1 1 (suc n) (Data.Nat.Base.s≤s Data.Nat.Base.z≤n))

  uSquare : ∀ n → (u n * u n) ≃ Basel.baselTerm n
  uSquare n = P.≃-trans
    (P.≃-symm (P.⋆-distrib-* (+ 1 / suc n) (+ 1 / suc n)))
    (P.⋆-cong (Rec.reciprocalNatSquareIsBaselRational n))

  radiusInverse : ∀ n → Cross.positiveInverse (Major.radiusSquarePositive n) ≃ (u n * u n)
  radiusInverse n = P.≃-trans
    (InvProd.inverseProduct (Major.radiusPositive n) (Major.radiusPositive n))
    (P.*-cong (Rec.natRealInverseIsEmbeddedReciprocal n)
      (Rec.natRealInverseIsEmbeddedReciprocal n))

  imagInverse : Cross.positiveInverse (Major.imagSquarePositive tau) ≃ (yInv * yInv)
  imagInverse = InvProd.inverseProduct (U.imaginaryPositive tau) (U.imaginaryPositive tau)

  majorantRead : ∀ n → E.majorant tau n ≃ (c * (u n * u n))
  majorantRead n = P.≃-trans
    (P.*-congˡ (P.≃-trans
      (InvProd.inverseProduct (Major.imagSquarePositive tau) (Major.radiusSquarePositive n))
      (P.*-cong imagInverse (radiusInverse n))))
    (P.≃-symm (P.*-assoc (Coercive.coercivityFactor (U.tau tau)) (yInv * yInv) (u n * u n)))

  countRead : ∀ n → N.natReal (S.squareCodeCount (suc n)) ≃
    (((r n + r n) + R.1ℝ) * ((r n + r n) + R.1ℝ))
  countRead n = P.≃-trans (N.natRealMul (suc (suc n +N suc n)) (suc (suc n +N suc n)))
    (P.*-cong side side)
    where
    side : N.natReal (suc (suc n +N suc n)) ≃ ((r n + r n) + R.1ℝ)
    side = P.≃-trans (N.natRealSuccessor (suc n +N suc n))
      (P.+-cong (P.≃-trans (P.⋆-cong (NE.natAsRationalAdd (suc n) (suc n))) (P.⋆-distrib-+ (NE.natAsRational (suc n)) (NE.natAsRational (suc n)))) P.≃-refl)

  -- Count*majorant^k = c^k*(2+u)^2*u^(2k-2).
  -- The exact successor radius is cancelled before estimating the shell.
  scaledSide : ∀ n → (((r n + r n) + R.1ℝ) * u n) ≃ (((+ 2 / 1) ⋆) + u n)
  scaledSide n = let open P.ℝ-Solver in
    P.≃-trans (solve 2 (λ r u → ((r ⊕ r) ⊕ Κ Q.1ℚᵘ) ⊗ u ⊜
      Κ (+ 2 / 1) ⊗ (u ⊗ r) ⊕ u) P.≃-refl (r n) (u n))
      (P.≃-trans (P.+-cong (P.*-congˡ (Rec.embeddedReciprocalNatCancels n)) P.≃-refl)
        (P.+-cong (P.*-identityʳ ((+ 2 / 1) ⋆)) P.≃-refl))

  sideBound : ∀ n → (((+ 2 / 1) ⋆) + u n) ≤ ((+ 3 / 1) ⋆)
  sideBound n = P.≤-respʳ-≃
    (let open P.ℝ-Solver in solve 0
      (Κ (+ 2 / 1) ⊕ Κ Q.1ℚᵘ ⊜ Κ (+ 3 / 1)) P.≃-refl)
    (P.+-monoʳ-≤ ((+ 2 / 1) ⋆) (u≤1 n))

  sideNN : ∀ n → R.NonNegative (((+ 2 / 1) ⋆) + u n)
  sideNN n = P.nonNegx,y⇒nonNegx+y
    (P.0≤x⇒nonNegx (P.p≤q⇒p⋆≤q⋆ Q.0ℚᵘ (+ 2 / 1) (QP.nonNegative⁻¹ (+ 2 / 1))))
    (uNN n)

  sideSquareBound : ∀ n → ((((+ 2 / 1) ⋆) + u n) * (((+ 2 / 1) ⋆) + u n)) ≤ ((+ 9 / 1) ⋆)
  sideSquareBound n = P.≤-respʳ-≃
    (let open P.ℝ-Solver in solve 0 (Κ (+ 3 / 1) ⊗ Κ (+ 3 / 1) ⊜ Κ (+ 9 / 1)) P.≃-refl)
    (P.*-mono-≤ (sideNN n) (sideNN n) (sideBound n) (sideBound n))

  power2Read : ∀ n → R.pow (E.majorant tau n) 2 ≃
    ((c * (u n * u n)) * (c * (u n * u n)))
  power2Read n = P.≃-trans
    (let open P.ℝ-Solver in solve 1 (λ x → (Κ Q.1ℚᵘ ⊗ x) ⊗ x ⊜ x ⊗ x)
      P.≃-refl (E.majorant tau n))
    (P.*-cong (majorantRead n) (majorantRead n))

  power3Read : ∀ n → R.pow (E.majorant tau n) 3 ≃
    (((c * (u n * u n)) * (c * (u n * u n))) * (c * (u n * u n)))
  power3Read n = P.*-cong (power2Read n) (majorantRead n)

  budget4 budget6 : ℝ
  budget4 = ((+ 9 / 1) ⋆) * (c * c)
  budget6 = ((+ 9 / 1) ⋆) * ((c * c) * c)

  cover4 : ∀ n → (N.natReal (S.squareCodeCount (suc n)) * R.pow (E.majorant tau n) 2) ≤
    (Basel.baselTerm n * budget4)
  cover4 n =
    let v = u n
        side = (r n + r n) + R.1ℝ
        open P.ℝ-Solver
        shape = solve 3 (λ s c u →
          (s ⊗ s) ⊗ ((c ⊗ (u ⊗ u)) ⊗ (c ⊗ (u ⊗ u))) ⊜
          ((s ⊗ u) ⊗ (s ⊗ u)) ⊗ ((c ⊗ c) ⊗ (u ⊗ u)))
          P.≃-refl side c v
        bound = P.*-monoʳ-≤-nonNeg (sideSquareBound n)
          (P.nonNegx,y⇒nonNegx*y (NN.bishopSquareNonnegative c) (NN.bishopSquareNonnegative v))
    in P.≤-respˡ-≃
      (P.≃-trans (P.*-cong (countRead n) (power2Read n))
        (P.≃-trans shape (P.*-congʳ (P.*-cong (scaledSide n) (scaledSide n)))))
      (P.≤-respʳ-≃
        (P.≃-trans (solve 2 (λ c u → Κ (+ 9 / 1) ⊗ ((c ⊗ c) ⊗ (u ⊗ u)) ⊜
          (u ⊗ u) ⊗ (Κ (+ 9 / 1) ⊗ (c ⊗ c))) P.≃-refl c v)
          (P.*-congʳ (uSquare n))) bound)

  cover6 : ∀ n → (N.natReal (S.squareCodeCount (suc n)) * R.pow (E.majorant tau n) 3) ≤
    (Basel.baselTerm n * budget6)
  cover6 n =
    let v = u n
        side = (r n + r n) + R.1ℝ
        open P.ℝ-Solver
        v4≤v2 : ((v * v) * (v * v)) ≤ (v * v)
        v4≤v2 = P.≤-respʳ-≃ (P.*-identityʳ (v * v))
          (P.*-monoˡ-≤-nonNeg
            (P.≤-trans (P.≤-respʳ-≃ (P.*-identityʳ v)
              (P.*-monoˡ-≤-nonNeg (u≤1 n) (uNN n))) (u≤1 n))
            (NN.bishopSquareNonnegative v))
        shape = solve 3 (λ s c u →
          (s ⊗ s) ⊗ (((c ⊗ (u ⊗ u)) ⊗ (c ⊗ (u ⊗ u))) ⊗ (c ⊗ (u ⊗ u))) ⊜
          ((s ⊗ u) ⊗ (s ⊗ u)) ⊗ (((c ⊗ c) ⊗ c) ⊗ ((u ⊗ u) ⊗ (u ⊗ u))))
          P.≃-refl side c v
        c3NN = P.nonNegx,y⇒nonNegx*y (NN.bishopSquareNonnegative c) cNN
        bound = P.*-mono-≤ (NN.bishopSquareNonnegative (((+ 2 / 1) ⋆) + v))
          (P.nonNegx,y⇒nonNegx*y c3NN (NN.bishopSquareNonnegative (v * v)))
          (sideSquareBound n) (P.*-monoˡ-≤-nonNeg v4≤v2 c3NN)
    in P.≤-respˡ-≃
      (P.≃-trans (P.*-cong (countRead n) (power3Read n))
        (P.≃-trans shape (P.*-congʳ (P.*-cong (scaledSide n) (scaledSide n)))))
      (P.≤-respʳ-≃
        (P.≃-trans (solve 2 (λ c u → Κ (+ 9 / 1) ⊗ (((c ⊗ c) ⊗ c) ⊗ (u ⊗ u)) ⊜
          (u ⊗ u) ⊗ (Κ (+ 9 / 1) ⊗ ((c ⊗ c) ⊗ c))) P.≃-refl c v)
          (P.*-congʳ (uSquare n))) bound)

  scaledBasel : (k : ℝ) → Seq._isConvergent (Seq.SeriesOf (λ n → Basel.baselTerm n * k))
  scaledBasel k = (Basel.baselLimit * k) ,
    Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ {(suc n) → P.≃-symm (Common.seriesOfCommonFactor Basel.baselTerm k (suc n))})
      (Seq.xₙyₙ→x₀y₀ Basel.baselSeriesConvergent
        (k , Seq.xₙ≃c⇒xₙ→c (λ {(suc n) → P.≃-refl})))

  shellAbsNN : ∀ n f ps → R.NonNegative (F.fold n (λ i → ∣ f i ∣) ps)
  shellAbsNN n f [] = P.nonNeg0
  shellAbsNN n f (p ∷ ps) with S.onSuccessorSquareShell? n p in eq
  ... | false = shellAbsNN n f ps
  ... | true = P.nonNegx,y⇒nonNegx+y
    (P.nonNeg∣x∣ (f (F.nonzero n p (subst T (sym eq) tt)))) (shellAbsNN n f ps)

  absoluteConverges : (f : K.NonzeroLatticePoint → ℝ) (k : ℝ) →
    (∀ n → F.shellAbsolute n f ≤ Basel.baselTerm n * k) →
    Seq._isConvergent (Seq.SeriesOf (λ n → F.shellAbsolute n f))
  absoluteConverges f k h = Seq.proposition-3-5 (scaledBasel k)
    (0 , λ n _ → P.≤-respˡ-≃
      (P.≃-symm (P.nonNegx⇒∣x∣≃x (shellAbsNN n f (S.squarePoints (suc n))))) (h n))

  real4Absolute = absoluteConverges (λ i → C.re (E.summand 4 tau i)) budget4
    (λ n → P.≤-trans (F.real4Abs tau n) (cover4 n))
  imag4Absolute = absoluteConverges (λ i → C.im (E.summand 4 tau i)) budget4
    (λ n → P.≤-trans (F.imag4Abs tau n) (cover4 n))
  real6Absolute = absoluteConverges (λ i → C.re (E.summand 6 tau i)) budget6
    (λ n → P.≤-trans (F.real6Abs tau n) (cover6 n))
  imag6Absolute = absoluteConverges (λ i → C.im (E.summand 6 tau i)) budget6
    (λ n → P.≤-trans (F.imag6Abs tau n) (cover6 n))

  componentConverges : (f : K.NonzeroLatticePoint → ℝ) (k : ℝ) →
    (∀ n → F.shellAbsolute n f ≤ Basel.baselTerm n * k) →
    Seq._isConvergent (Seq.SeriesOf (λ n → F.shellComponent n f))
  componentConverges f k h = Seq.proposition-3-5 (scaledBasel k)
    (0 , λ n _ → P.≤-trans (F.foldTriangle n f (S.squarePoints (suc n))) (h n))

  real4 = componentConverges (λ i → C.re (E.summand 4 tau i)) budget4
    (λ n → P.≤-trans (F.real4Abs tau n) (cover4 n))
  imag4 = componentConverges (λ i → C.im (E.summand 4 tau i)) budget4
    (λ n → P.≤-trans (F.imag4Abs tau n) (cover4 n))
  real6 = componentConverges (λ i → C.re (E.summand 6 tau i)) budget6
    (λ n → P.≤-trans (F.real6Abs tau n) (cover6 n))
  imag6 = componentConverges (λ i → C.im (E.summand 6 tau i)) budget6
    (λ n → P.≤-trans (F.imag6Abs tau n) (cover6 n))

  G4 G6 : C.BishopComplex
  G4 = C.complex (Seq.lim real4) (Seq.lim imag4)
  G6 = C.complex (Seq.lim real6) (Seq.lim imag6)

-- These are concrete shell-ordered lattice sums. Unconditional change of
-- exhaustion, the Fourier row identity and normalization remain distinct.
