module DASHI.Physics.Closure.NSTriadKNFiniteComplexFourierDynamics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (ℤ; +_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Relation.Nullary.Decidable using (yes; no)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNExactLatticeTriadZeroSum as ZeroSum
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Algebra
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffModeSupport as Support
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Sector
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy
import DASHI.Physics.Closure.NSTriadKNFiniteTriadCancellationAlgebra as Cancel

open Energy using (ModalTriadTransfer; transferLeft; transferRight; transferOut; conservation)

------------------------------------------------------------------------
-- Finite complex Fourier dynamics, deliberately instantaneous.
--
-- This is not a time-analysis library.  `formalWeightedEnergyDerivative`
-- is the finite algebraic expression which a later differentiability theorem
-- must identify with d/dt E_z.  Separating the two prevents a finite ODE
-- convention from being mistaken for the required continuum argument.
------------------------------------------------------------------------

record FiniteComplexFourierAuthority
    (K : Algebra.ExactOrderedCommutativeRing) : Set₁ where
  field
    Complex : Set
    Vec3C : Set

    zeroComplex : Complex
    _+ᶜ_ : Complex → Complex → Complex
    _*ᶜ_ : Complex → Complex → Complex
    -ᶜ_ : Complex → Complex
    conjugate : Complex → Complex
    realPart : Complex → Scalar.Scalar (Algebra.orderedScalar K)
    complexI : Complex
    embedInteger : ℤ → Complex

    zeroVector : Vec3C
    _+ᵥ_ : Vec3C → Vec3C → Vec3C
    -ᵥ_ : Vec3C → Vec3C
    scaleComplex : Complex → Vec3C → Vec3C
    conjugateVector : Vec3C → Vec3C
    innerC : Vec3C → Vec3C → Complex
    normSq : Vec3C → Scalar.Scalar (Algebra.orderedScalar K)

    waveDot : Lattice.LatticeMode3 → Vec3C → Complex
    leray : Lattice.LatticeMode3 → Vec3C → Vec3C

    realPartAdd :
      (a b : Complex) → realPart (a +ᶜ b) ≡
      Scalar._+_ (Algebra.orderedScalar K) (realPart a) (realPart b)
    realPartNeg :
      (a : Complex) → realPart (-ᶜ a) ≡
      Scalar.neg (Algebra.orderedScalar K) (realPart a)
    realPartConjugate :
      (a : Complex) → realPart (conjugate a) ≡ realPart a
    realPartZero : realPart zeroComplex ≡ Scalar.zero (Algebra.orderedScalar K)
    innerAddRight :
      (x y z : Vec3C) → innerC x (y +ᵥ z) ≡
      innerC x y +ᶜ innerC x z
    innerScaleRight :
      (x y : Vec3C) → (a : Complex) →
      innerC x (scaleComplex a y) ≡ a *ᶜ innerC x y
    innerConjugateSymmetry :
      (x y : Vec3C) → conjugate (innerC x y) ≡ innerC y x
    -- For the standard coordinate Hermitian form, conjugating the first
    -- argument exposes the underlying symmetric complex-bilinear dot.
    -- This is the precise pairing law needed for the modal triad reversal.
    innerConjugateLeftSymmetric :
      (x y : Vec3C) →
      innerC (conjugateVector x) y ≡ innerC (conjugateVector y) x
    innerZeroRight :
      (x : Vec3C) → innerC x zeroVector ≡ zeroComplex
    normSqIsDiagonalInner :
      (x : Vec3C) → normSq x ≡ realPart (innerC x x)

    -- Atomic zero laws used to reduce the singleton self-input orbit.  They
    -- are ordinary complex/vector algebra, not a triad-conservation axiom.
    complexMulZeroRight :
      (a : Complex) → a *ᶜ zeroComplex ≡ zeroComplex
    negComplexZero : -ᶜ zeroComplex ≡ zeroComplex
    scaleComplexZeroScalar :
      (x : Vec3C) → scaleComplex zeroComplex x ≡ zeroVector

    leraySelfAdjoint :
      (k : Lattice.LatticeMode3) → (x y : Vec3C) →
      innerC x (leray k y) ≡ innerC (leray k x) y
    lerayFixesDivergenceFree :
      (k : Lattice.LatticeMode3) → (x : Vec3C) →
      waveDot k x ≡ zeroComplex → leray k x ≡ x
    lerayProducesDivergenceFree :
      (k : Lattice.LatticeMode3) → (x : Vec3C) →
      waveDot k (leray k x) ≡ zeroComplex

    -- The lattice wavevectors are real, so conjugation preserves the
    -- divergence constraint at a fixed Fourier label.
    conjugateVectorPreservesDivergenceFree :
      (k : Lattice.LatticeMode3) → (x : Vec3C) →
      waveDot k x ≡ zeroComplex →
      waveDot k (conjugateVector x) ≡ zeroComplex

    -- This transport is also useful for the legacy labelled-triad pairing.
    -- It is strictly stronger than what the actual modal-energy convention
    -- below needs.
    conjugateVectorDivergenceFreeAtNegatedMode :
      (k : Lattice.LatticeMode3) → (x : Vec3C) →
      waveDot k x ≡ zeroComplex →
      waveDot (Lattice.modeNeg k) (conjugateVector x) ≡ zeroComplex

open FiniteComplexFourierAuthority public

------------------------------------------------------------------------
-- Local complex wave-dot algebra used by triad cancellation.
--
-- This is intentionally narrower than a concrete C^3 implementation.  It
-- isolates exactly the additive facts from which zero-sum geometry and one
-- divergence constraint imply a wave-dot reversal.  In particular, it does
-- not contain any modal-transfer or conservation assertion.
------------------------------------------------------------------------

record FiniteTriadWaveDotAlgebra
    (K : Algebra.ExactOrderedCommutativeRing)
    (A : FiniteComplexFourierAuthority K) : Set₁ where
  field
    complexAddAssociative :
      (a b c : Complex A) → _+ᶜ_ A (_+ᶜ_ A a b) c ≡
      _+ᶜ_ A a (_+ᶜ_ A b c)
    complexAddCommutative :
      (a b : Complex A) → _+ᶜ_ A a b ≡ _+ᶜ_ A b a
    complexAddZeroLeft :
      (a : Complex A) → _+ᶜ_ A (zeroComplex A) a ≡ a
    complexAddInverseLeft :
      (a : Complex A) → _+ᶜ_ A
        (FiniteComplexFourierAuthority.-ᶜ_ A a) a ≡ zeroComplex A
    complexAddLeftCancel :
      (a b c : Complex A) → _+ᶜ_ A a b ≡ _+ᶜ_ A a c → b ≡ c

    waveDotTriadSum :
      (τ : Lattice.LatticeTriad) → (v : Vec3C A) →
      waveDot A (Lattice.triadSum τ) v ≡
      _+ᶜ_ A
        (_+ᶜ_ A (waveDot A (Lattice.left τ) v)
          (waveDot A (Lattice.right τ) v))
        (waveDot A (Lattice.out τ) v)
    waveDotZeroMode :
      (v : Vec3C A) →
      waveDot A (Lattice.mkLatticeMode3 (+ 0) (+ 0) (+ 0)) v ≡
      zeroComplex A

open FiniteTriadWaveDotAlgebra public

record FiniteComplexProductNegationAlgebra
    (K : Algebra.ExactOrderedCommutativeRing)
    (A : FiniteComplexFourierAuthority K) : Set₁ where
  field
    complexMulNegRight :
      (a b : Complex A) →
      _*ᶜ_ A a (FiniteComplexFourierAuthority.-ᶜ_ A b) ≡
      FiniteComplexFourierAuthority.-ᶜ_ A (_*ᶜ_ A a b)
    complexNegMulLeft :
      (a b : Complex A) →
      _*ᶜ_ A (FiniteComplexFourierAuthority.-ᶜ_ A a) b ≡
      FiniteComplexFourierAuthority.-ᶜ_ A (_*ᶜ_ A a b)
    complexNegInvolutive :
      (a : Complex A) →
      FiniteComplexFourierAuthority.-ᶜ_ A
        (FiniteComplexFourierAuthority.-ᶜ_ A a) ≡ a

open FiniteComplexProductNegationAlgebra public

complexAddSwapFront :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (W : FiniteTriadWaveDotAlgebra K A) →
  (a b c : Complex A) →
  _+ᶜ_ A a (_+ᶜ_ A b c) ≡ _+ᶜ_ A b (_+ᶜ_ A a c)
complexAddSwapFront K A W a b c =
  trans
    (sym (complexAddAssociative W a b c))
    (trans
      (cong (λ x → _+ᶜ_ A x c) (complexAddCommutative W a b))
      (complexAddAssociative W b a c))

complexAddMoveEndToFront :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (W : FiniteTriadWaveDotAlgebra K A) →
  (a b c : Complex A) →
  _+ᶜ_ A a (_+ᶜ_ A b c) ≡ _+ᶜ_ A c (_+ᶜ_ A a b)
complexAddMoveEndToFront K A W a b c =
  trans
    (cong (λ x → _+ᶜ_ A a x) (complexAddCommutative W b c))
    (trans
      (sym (complexAddAssociative W a c b))
      (trans
        (cong (λ x → _+ᶜ_ A x b) (complexAddCommutative W a c))
        (complexAddAssociative W c a b)))

-- The literal six-term normal form is regrouped into its q/r/p cancellation
-- pairs.  This is purely commutative-group bookkeeping; it contains no
-- Fourier, reality, or divergence information.
complexAddSixPairShuffle :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (W : FiniteTriadWaveDotAlgebra K A) →
  (a b c d e f : Complex A) →
  _+ᶜ_ A
    (_+ᶜ_ A (_+ᶜ_ A a b) (_+ᶜ_ A c d))
    (_+ᶜ_ A e f) ≡
  _+ᶜ_ A
    (_+ᶜ_ A (_+ᶜ_ A a f) (_+ᶜ_ A b c))
    (_+ᶜ_ A d e)
complexAddSixPairShuffle K A W a b c d e f =
  trans
    (complexAddAssociative W (_+ᶜ_ A a b) (_+ᶜ_ A c d) (_+ᶜ_ A e f))
    (trans
      (complexAddAssociative W a b
        (_+ᶜ_ A (_+ᶜ_ A c d) (_+ᶜ_ A e f)))
      (trans
        (cong (λ x → _+ᶜ_ A a (_+ᶜ_ A b x))
          (complexAddAssociative W c d (_+ᶜ_ A e f)))
        (trans
          (cong (λ x → _+ᶜ_ A a (_+ᶜ_ A b (_+ᶜ_ A c x)))
            (complexAddMoveEndToFront K A W d e f))
          (trans
            (cong (λ x → _+ᶜ_ A a (_+ᶜ_ A b x))
              (complexAddSwapFront K A W c f (_+ᶜ_ A d e)))
            (trans
              (cong (λ x → _+ᶜ_ A a x)
                (complexAddSwapFront K A W b f
                  (_+ᶜ_ A c (_+ᶜ_ A d e))))
              (sym
                (trans
                  (complexAddAssociative W (_+ᶜ_ A a f)
                    (_+ᶜ_ A b c) (_+ᶜ_ A d e))
                  (trans
                    (complexAddAssociative W a f
                      (_+ᶜ_ A (_+ᶜ_ A b c) (_+ᶜ_ A d e)))
                    (cong (λ x → _+ᶜ_ A a (_+ᶜ_ A f x))
                      (complexAddAssociative W b c (_+ᶜ_ A d e)))))))))))

-- A reusable complex-ring normalization.  It is the exact algebra behind a
-- pair of modal occurrences once their wave-dot coefficients are opposite
-- and their negative-mode pairings have been identified.
negatedScaledPairZero :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (W : FiniteTriadWaveDotAlgebra K A) →
  (P : FiniteComplexProductNegationAlgebra K A) →
  (i a b h₁ h₂ : Complex A) →
  b ≡ FiniteComplexFourierAuthority.-ᶜ_ A a →
  h₂ ≡ h₁ →
  _+ᶜ_ A
    (FiniteComplexFourierAuthority.-ᶜ_ A (_*ᶜ_ A (_*ᶜ_ A i a) h₁))
    (FiniteComplexFourierAuthority.-ᶜ_ A (_*ᶜ_ A (_*ᶜ_ A i b) h₂)) ≡
  zeroComplex A
negatedScaledPairZero K A W P i a b h₁ h₂ bNeg pairing =
  trans
    (cong₂ (_+ᶜ_ A) refl secondToFirst)
    (complexAddInverseLeft W (_*ᶜ_ A (_*ᶜ_ A i a) h₁))
  where
  secondToFirst :
    FiniteComplexFourierAuthority.-ᶜ_ A (_*ᶜ_ A (_*ᶜ_ A i b) h₂) ≡
    _*ᶜ_ A (_*ᶜ_ A i a) h₁
  secondToFirst =
    trans
      (cong (FiniteComplexFourierAuthority.-ᶜ_ A)
        (cong (λ x → _*ᶜ_ A (_*ᶜ_ A i x) h₂) bNeg))
      (trans
        (cong (FiniteComplexFourierAuthority.-ᶜ_ A)
          (cong (λ x → _*ᶜ_ A x h₂) (complexMulNegRight P i a)))
        (trans
          (cong (FiniteComplexFourierAuthority.-ᶜ_ A)
            (complexNegMulLeft P (_*ᶜ_ A i a) h₂))
          (trans
            (complexNegInvolutive P (_*ᶜ_ A (_*ᶜ_ A i a) h₂))
            (cong (λ x → _*ᶜ_ A (_*ᶜ_ A i a) x) pairing))))

rightDotLeftEqNegOutDotLeft :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (W : FiniteTriadWaveDotAlgebra K A) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Lattice.zeroSum? τ ≡ true →
  waveDot A (Lattice.left τ) (u (Lattice.left τ)) ≡ zeroComplex A →
  waveDot A (Lattice.right τ) (u (Lattice.left τ)) ≡
  FiniteComplexFourierAuthority.-ᶜ_ A
    (waveDot A (Lattice.out τ) (u (Lattice.left τ)))
rightDotLeftEqNegOutDotLeft K A W u τ zeroSum leftDF =
  complexAddLeftCancel W r q (FiniteComplexFourierAuthority.-ᶜ_ A r)
    (trans
      (trans (sym (complexAddCommutative W q r)) qPlusRZero)
      (sym
        (trans (complexAddCommutative W r
          (FiniteComplexFourierAuthority.-ᶜ_ A r))
          (complexAddInverseLeft W r))))
  where
  v = u (Lattice.left τ)
  p = waveDot A (Lattice.left τ) v
  q = waveDot A (Lattice.right τ) v
  r = waveDot A (Lattice.out τ) v
  totalZero : _+ᶜ_ A (_+ᶜ_ A p q) r ≡ zeroComplex A
  totalZero =
    trans
      (sym (waveDotTriadSum W τ v))
      (trans
        (cong (λ k → waveDot A k v)
          (ZeroSum.triadSumIsZeroMode τ zeroSum))
        (waveDotZeroMode W v))
  qPlusRZero : _+ᶜ_ A q r ≡ zeroComplex A
  qPlusRZero =
    trans
      (sym
        (cong (λ x → _+ᶜ_ A x r)
          (complexAddZeroLeft W q)))
      (trans
        (cong (λ x → _+ᶜ_ A (_+ᶜ_ A x q) r) (sym leftDF))
        totalZero)

outDotRightEqNegLeftDotRight :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (W : FiniteTriadWaveDotAlgebra K A) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Lattice.zeroSum? τ ≡ true →
  waveDot A (Lattice.right τ) (u (Lattice.right τ)) ≡ zeroComplex A →
  waveDot A (Lattice.out τ) (u (Lattice.right τ)) ≡
  FiniteComplexFourierAuthority.-ᶜ_ A
    (waveDot A (Lattice.left τ) (u (Lattice.right τ)))
outDotRightEqNegLeftDotRight K A W u
  (Lattice.mkLatticeTriad p q r) zeroSum rightDF =
  rightDotLeftEqNegOutDotLeft K A W u
    (Lattice.mkLatticeTriad q r p)
    (ZeroSum.zeroSumCycle (Lattice.mkLatticeTriad p q r) zeroSum)
    rightDF

leftDotRightEqNegOutDotRight :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (W : FiniteTriadWaveDotAlgebra K A) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Lattice.zeroSum? τ ≡ true →
  waveDot A (Lattice.right τ) (u (Lattice.right τ)) ≡ zeroComplex A →
  waveDot A (Lattice.left τ) (u (Lattice.right τ)) ≡
  FiniteComplexFourierAuthority.-ᶜ_ A
    (waveDot A (Lattice.out τ) (u (Lattice.right τ)))
leftDotRightEqNegOutDotRight K A W u
  (Lattice.mkLatticeTriad p q r) zeroSum rightDF =
  rightDotLeftEqNegOutDotLeft K A W u
    (Lattice.mkLatticeTriad q p r)
    (ZeroSum.zeroSumSwap (Lattice.mkLatticeTriad p q r) zeroSum)
    rightDF

leftDotOutEqNegRightDotOut :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (W : FiniteTriadWaveDotAlgebra K A) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Lattice.zeroSum? τ ≡ true →
  waveDot A (Lattice.out τ) (u (Lattice.out τ)) ≡ zeroComplex A →
  waveDot A (Lattice.left τ) (u (Lattice.out τ)) ≡
  FiniteComplexFourierAuthority.-ᶜ_ A
    (waveDot A (Lattice.right τ) (u (Lattice.out τ)))
leftDotOutEqNegRightDotOut K A W u
  (Lattice.mkLatticeTriad p q r) zeroSum outDF =
  rightDotLeftEqNegOutDotLeft K A W u
    (Lattice.mkLatticeTriad r p q)
    (ZeroSum.zeroSumCycle (Lattice.mkLatticeTriad q r p)
      (ZeroSum.zeroSumCycle (Lattice.mkLatticeTriad p q r) zeroSum))
    outDF

------------------------------------------------------------------------
-- Leray removal against a divergence-free energy test vector.
--
-- This is a concrete finite-dimensional identity.  It does not assert the
-- Navier--Stokes triad cancellation; it only exposes the simplification which
-- makes that later six-term calculation possible.
------------------------------------------------------------------------

lerayDropsAgainstDivergenceFreeOutput :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (k : Lattice.LatticeMode3) →
  (output v : Vec3C A) →
  waveDot A k output ≡ zeroComplex A →
  realPart A
    (innerC A output (leray A k v)) ≡
  realPart A (innerC A output v)
lerayDropsAgainstDivergenceFreeOutput K A k output v outputDF =
  cong (realPart A)
    (trans
      (leraySelfAdjoint A k output v)
      (cong (λ x → innerC A x v)
        (lerayFixesDivergenceFree A k output outputDF)))

lerayDropsAgainstPhysicalOutput :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (k : Lattice.LatticeMode3) →
  (output v : Vec3C A) →
  waveDot A (Lattice.modeNeg k) output ≡ zeroComplex A →
  realPart A
    (innerC A output
      (leray A (Lattice.modeNeg k) v)) ≡
  realPart A (innerC A output v)
lerayDropsAgainstPhysicalOutput K A k output v outputDF =
  lerayDropsAgainstDivergenceFreeOutput K A (Lattice.modeNeg k) output v
    outputDF

------------------------------------------------------------------------
-- Concrete labelled modal transfers.
--
-- For `τ = (p , q , r)` with p + q + r = 0, its ordered interaction has
-- convolution output `-r` and is paired with `u_{-r}`.  `innerC` is
-- Hermitian (see `innerConjugateSymmetry`), so it supplies the outer
-- conjugation in the energy pairing itself.  Pre-conjugating this first
-- argument would therefore double-count conjugation and describe a different
-- trilinear form.  This is the actual modal-energy pairing for the Fourier
-- equation at output `-r`.
-- Cycling τ gives the corresponding contributions labelled by p and q.
-- Input swaps are combined only off the diagonal, exactly as in the
-- cutoff-convolution reconstruction; p = q retains its singleton occurrence.
------------------------------------------------------------------------

orderedModalInteraction :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (Lattice.LatticeMode3 → Vec3C A) → Lattice.LatticeTriad → Vec3C A
orderedModalInteraction K A u τ =
  scaleComplex A
    (_*ᶜ_ A (complexI A) (waveDot A (Lattice.right τ) (u (Lattice.left τ))))
    (u (Lattice.right τ))

-- The complex summand before applying `- realPart`.  Keeping it explicit
-- makes the later six-occurrence normal form a literal finite expression,
-- rather than a postulated link from modal transfers to cancellation atoms.
orderedModalComplexTerm :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (Lattice.LatticeMode3 → Vec3C A) → Lattice.LatticeTriad → Complex A
orderedModalComplexTerm K A u τ =
  innerC A (u (Lattice.modeNeg (Lattice.out τ)))
    (orderedModalInteraction K A u τ)

-- This is the scalar trilinear form underlying each modal occurrence.  It
-- follows solely from right-linearity of the Hermitian pairing; no reality,
-- incompressibility, or triad cancellation has been used yet.
orderedModalComplexTermExpansion :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  orderedModalComplexTerm K A u τ ≡
  _*ᶜ_ A
    (_*ᶜ_ A (complexI A)
      (waveDot A (Lattice.right τ) (u (Lattice.left τ))))
    (innerC A (u (Lattice.modeNeg (Lattice.out τ)))
      (u (Lattice.right τ)))
orderedModalComplexTermExpansion K A u τ =
  innerScaleRight A
    (u (Lattice.modeNeg (Lattice.out τ)))
    (u (Lattice.right τ))
    (_*ᶜ_ A (complexI A)
      (waveDot A (Lattice.right τ) (u (Lattice.left τ))))

-- The missing swapped occurrence of a diagonal input orbit carries the same
-- self-input factor.  Incompressibility makes that factor zero, so restoring
-- it for the six-term cancellation normal form does not alter the physical
-- cutoff contribution.
diagonalSelfInputInteractionVectorZero :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Lattice.left τ ≡ Lattice.right τ →
  waveDot A (Lattice.left τ) (u (Lattice.left τ)) ≡ zeroComplex A →
  orderedModalInteraction K A u τ ≡ zeroVector A
diagonalSelfInputInteractionVectorZero K A u τ refl divergence =
  trans
    (cong (λ d → scaleComplex A
      (_*ᶜ_ A (complexI A) d) (u (Lattice.right τ))) divergence)
    (trans
      (cong (λ c → scaleComplex A c (u (Lattice.right τ)))
        (complexMulZeroRight A (complexI A)))
      (scaleComplexZeroScalar A (u (Lattice.right τ))))

-- The instantaneous Fourier state is introduced before the modal-transfer
-- simplification lemmas because those lemmas use its concrete divergence-free
-- witness.  This is a dependency-ordering move only: the dynamics fields are
-- consumed later by the weighted-energy identity.
record FiniteFourierNSState
    (K : Algebra.ExactOrderedCommutativeRing)
    (A : FiniteComplexFourierAuthority K) (M : Nat) : Set₁ where
  field
    coefficient : Lattice.LatticeMode3 → Vec3C A
    velocityDot : Lattice.LatticeMode3 → Vec3C A

    outsideCutoffZero :
      (k : Lattice.LatticeMode3) →
      Sector.inExactCutoff? M k ≡ false → coefficient k ≡ zeroVector A
    reality :
      (k : Lattice.LatticeMode3) →
      coefficient (Lattice.modeNeg k) ≡ conjugateVector A (coefficient k)
    divergenceFree :
      (k : Lattice.LatticeMode3) →
      waveDot A k (coefficient k) ≡ zeroComplex A

    viscosity : Scalar.Scalar (Algebra.orderedScalar K)
    modeSquaredNorm : Lattice.LatticeMode3 → Scalar.Scalar (Algebra.orderedScalar K)
    viscousTerm : Lattice.LatticeMode3 → Vec3C A
    cutoffConvectionTerm : Lattice.LatticeMode3 → Vec3C A
    cutoffBoundaryTerm : Lattice.LatticeMode3 → Vec3C A

    dynamics :
      (k : Lattice.LatticeMode3) →
      velocityDot k ≡
      FiniteComplexFourierAuthority._+ᵥ_ A
        (cutoffConvectionTerm k)
        (FiniteComplexFourierAuthority._+ᵥ_ A
          (viscousTerm k) (cutoffBoundaryTerm k))

open FiniteFourierNSState public

-- Reality turns the coordinate-bilinear symmetry above into the exact mode
-- pairing reversal used by all three six-term pairs.  No triad geometry or
-- divergence constraint is involved in this lemma.
negativeModePairingSymmetric :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) →
  (a b : Lattice.LatticeMode3) →
  innerC A (coefficient u (Lattice.modeNeg a)) (coefficient u b) ≡
  innerC A (coefficient u (Lattice.modeNeg b)) (coefficient u a)
negativeModePairingSymmetric K A M u a b =
  trans
    (cong (λ x → innerC A x (coefficient u b)) (reality u a))
    (trans
      (innerConjugateLeftSymmetric A (coefficient u a) (coefficient u b))
      (sym
        (cong (λ x → innerC A x (coefficient u a)) (reality u b))))

orderedModalTransfer :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (Lattice.LatticeMode3 → Vec3C A) → Lattice.LatticeTriad →
  Scalar.Scalar (Algebra.orderedScalar K)
orderedModalTransfer K A u τ =
  Scalar.neg S
    (realPart A
      (innerC A (u (Lattice.modeNeg (Lattice.out τ)))
        (leray A (Lattice.modeNeg (Lattice.out τ))
          (orderedModalInteraction K A u τ))))
  where
  S = Algebra.orderedScalar K

orderedModalTransferNoLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (Lattice.LatticeMode3 → Vec3C A) → Lattice.LatticeTriad →
  Scalar.Scalar (Algebra.orderedScalar K)
orderedModalTransferNoLeray K A u τ =
  Scalar.neg (Algebra.orderedScalar K)
    (realPart A (orderedModalComplexTerm K A u τ))

orderedModalTransferWithoutLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  orderedModalTransfer K A (coefficient u) τ ≡
  orderedModalTransferNoLeray K A (coefficient u) τ
orderedModalTransferWithoutLeray K A M u τ =
  cong (Scalar.neg (Algebra.orderedScalar K))
    (lerayDropsAgainstDivergenceFreeOutput K A (Lattice.modeNeg (Lattice.out τ))
      (coefficient u (Lattice.modeNeg (Lattice.out τ)))
      (orderedModalInteraction K A (coefficient u) τ)
      (divergenceFree u (Lattice.modeNeg (Lattice.out τ))))

canonicalModalTransfer :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (Lattice.LatticeMode3 → Vec3C A) → Lattice.LatticeTriad →
  Scalar.Scalar (Algebra.orderedScalar K)
canonicalModalTransfer K A u τ
  with Support.latticeModeDecEq (Lattice.left τ) (Lattice.right τ)
... | yes _ = orderedModalTransfer K A u τ
... | no _ = Scalar._+_ S
  (orderedModalTransfer K A u τ)
  (orderedModalTransfer K A u (Lattice.triadSwap τ))
  where
  S = Algebra.orderedScalar K

canonicalModalTransferNoLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (Lattice.LatticeMode3 → Vec3C A) → Lattice.LatticeTriad →
  Scalar.Scalar (Algebra.orderedScalar K)
canonicalModalTransferNoLeray K A u τ
  with Support.latticeModeDecEq (Lattice.left τ) (Lattice.right τ)
... | yes _ = orderedModalTransferNoLeray K A u τ
... | no _ = Scalar._+_ S
  (orderedModalTransferNoLeray K A u τ)
  (orderedModalTransferNoLeray K A u (Lattice.triadSwap τ))
  where
  S = Algebra.orderedScalar K

-- A uniform two-occurrence form is used only for the cancellation normal
-- form.  On a diagonal input pair its extra swapped occurrence is exactly
-- zero by incompressibility, so this restores algebraic symmetry without
-- changing the physical singleton-orbit convention.
uniformModalTransferNoLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (Lattice.LatticeMode3 → Vec3C A) → Lattice.LatticeTriad →
  Scalar.Scalar (Algebra.orderedScalar K)
uniformModalTransferNoLeray K A u τ = Scalar._+_ S
  (orderedModalTransferNoLeray K A u τ)
  (orderedModalTransferNoLeray K A u (Lattice.triadSwap τ))
  where S = Algebra.orderedScalar K

swapPreservesDiagonalInputs :
  (τ : Lattice.LatticeTriad) →
  Lattice.left τ ≡ Lattice.right τ →
  Lattice.left (Lattice.triadSwap τ) ≡
  Lattice.right (Lattice.triadSwap τ)
swapPreservesDiagonalInputs (Lattice.mkLatticeTriad left right out) refl = refl

orderedModalTransferNoLerayZeroFromDiagonal :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  Lattice.left τ ≡ Lattice.right τ →
  orderedModalTransferNoLeray K A (coefficient u) τ ≡
  Scalar.zero (Algebra.orderedScalar K)
orderedModalTransferNoLerayZeroFromDiagonal K A M u τ left≡right =
  trans
    (cong (Scalar.neg S)
      (trans
        (cong (realPart A)
          (trans
            (cong (innerC A test)
              (diagonalSelfInputInteractionVectorZero K A (coefficient u) τ
                left≡right (divergenceFree u (Lattice.left τ))))
            (innerZeroRight A test)))
        (realPartZero A)))
    (Algebra.negZero K)
  where
  S = Algebra.orderedScalar K
  test = coefficient u (Lattice.modeNeg (Lattice.out τ))

canonicalModalTransferNoLerayEqualsUniform :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  canonicalModalTransferNoLeray K A (coefficient u) τ ≡
  uniformModalTransferNoLeray K A (coefficient u) τ
canonicalModalTransferNoLerayEqualsUniform K A M u τ
  with Support.latticeModeDecEq (Lattice.left τ) (Lattice.right τ)
... | yes left≡right =
  trans
    (sym (Algebra.addZeroRight K
      (orderedModalTransferNoLeray K A (coefficient u) τ)))
    (cong (Scalar._+_ S
      (orderedModalTransferNoLeray K A (coefficient u) τ))
      (sym
        (orderedModalTransferNoLerayZeroFromDiagonal K A M u
          (Lattice.triadSwap τ) (swapPreservesDiagonalInputs τ left≡right))))
  where S = Algebra.orderedScalar K
... | no _ = refl

canonicalModalTransferWithoutLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  canonicalModalTransfer K A (coefficient u) τ ≡
  canonicalModalTransferNoLeray K A (coefficient u) τ
canonicalModalTransferWithoutLeray K A M u τ
  with Support.latticeModeDecEq (Lattice.left τ) (Lattice.right τ)
... | yes _ = orderedModalTransferWithoutLeray K A M u τ
... | no _ = cong₂ (Scalar._+_ (Algebra.orderedScalar K))
  (orderedModalTransferWithoutLeray K A M u τ)
  (orderedModalTransferWithoutLeray K A M u (Lattice.triadSwap τ))

triadCycleTwice : Lattice.LatticeTriad → Lattice.LatticeTriad
triadCycleTwice τ = Lattice.triadCycle (Lattice.triadCycle τ)

record PhysicalModalTransferTriple
    (K : Algebra.ExactOrderedCommutativeRing)
    (A : FiniteComplexFourierAuthority K)
    (u : Lattice.LatticeMode3 → Vec3C A)
    (τ : Lattice.LatticeTriad) : Set where
  field
    transferP transferQ transferR : Scalar.Scalar (Algebra.orderedScalar K)

open PhysicalModalTransferTriple public

physicalModalTransferTriple :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  PhysicalModalTransferTriple K A u τ
physicalModalTransferTriple K A u τ = record
  { transferP = canonicalModalTransfer K A u (Lattice.triadCycle τ)
  ; transferQ = canonicalModalTransfer K A u (triadCycleTwice τ)
  ; transferR = canonicalModalTransfer K A u τ
  }

modalTransferPWithoutLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  transferP (physicalModalTransferTriple K A (coefficient u) τ) ≡
  canonicalModalTransferNoLeray K A (coefficient u) (Lattice.triadCycle τ)
modalTransferPWithoutLeray K A M u τ =
  canonicalModalTransferWithoutLeray K A M u (Lattice.triadCycle τ)

modalTransferQWithoutLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  transferQ (physicalModalTransferTriple K A (coefficient u) τ) ≡
  canonicalModalTransferNoLeray K A (coefficient u) (triadCycleTwice τ)
modalTransferQWithoutLeray K A M u τ =
  canonicalModalTransferWithoutLeray K A M u (triadCycleTwice τ)

modalTransferRWithoutLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  transferR (physicalModalTransferTriple K A (coefficient u) τ) ≡
  canonicalModalTransferNoLeray K A (coefficient u) τ
modalTransferRWithoutLeray K A M u τ =
  canonicalModalTransferWithoutLeray K A M u τ

-- The exact concrete left-hand side of the pending triad-cancellation
-- theorem.  The companion no-Leray form is obtained solely by the three
-- projector-removal identities above; no conservation statement enters here.
modalTransferSum :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Scalar.Scalar (Algebra.orderedScalar K)
modalTransferSum K A u τ =
  Scalar._+_ S
    (Scalar._+_ S (transferP triple) (transferQ triple))
    (transferR triple)
  where
  S = Algebra.orderedScalar K
  triple = physicalModalTransferTriple K A u τ

modalTransferSumNoLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Scalar.Scalar (Algebra.orderedScalar K)
modalTransferSumNoLeray K A u τ =
  Scalar._+_ S
    (Scalar._+_ S
      (canonicalModalTransferNoLeray K A u (Lattice.triadCycle τ))
      (canonicalModalTransferNoLeray K A u (triadCycleTwice τ)))
    (canonicalModalTransferNoLeray K A u τ)
  where
  S = Algebra.orderedScalar K

uniformModalTransferSumNoLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Scalar.Scalar (Algebra.orderedScalar K)
uniformModalTransferSumNoLeray K A u τ = Scalar._+_ S
  (Scalar._+_ S
    (uniformModalTransferNoLeray K A u (Lattice.triadCycle τ))
    (uniformModalTransferNoLeray K A u (triadCycleTwice τ)))
  (uniformModalTransferNoLeray K A u τ)
  where S = Algebra.orderedScalar K

modalTransferSumNoLerayEqualsUniform :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  modalTransferSumNoLeray K A (coefficient u) τ ≡
  uniformModalTransferSumNoLeray K A (coefficient u) τ
modalTransferSumNoLerayEqualsUniform K A M u τ =
  cong₂ (Scalar._+_ S)
    (cong₂ (Scalar._+_ S)
      (canonicalModalTransferNoLerayEqualsUniform K A M u (Lattice.triadCycle τ))
      (canonicalModalTransferNoLerayEqualsUniform K A M u (triadCycleTwice τ)))
    (canonicalModalTransferNoLerayEqualsUniform K A M u τ)
  where S = Algebra.orderedScalar K

-- The six complex occurrences that remain after the three Leray removals.
-- Negation is kept inside every occurrence so that applying `realPart` is a
-- purely additive calculation; no claim is made that this complex sum itself
-- vanishes.
sixTermComplexNormalForm :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Complex A
sixTermComplexNormalForm K A u τ = _+ᶜ_ A
  (_+ᶜ_ A
    (_+ᶜ_ A
      (FiniteComplexFourierAuthority.-ᶜ_ A
        (orderedModalComplexTerm K A u (Lattice.triadCycle τ)))
      (FiniteComplexFourierAuthority.-ᶜ_ A (orderedModalComplexTerm K A u
        (Lattice.triadSwap (Lattice.triadCycle τ)))))
    (_+ᶜ_ A
      (FiniteComplexFourierAuthority.-ᶜ_ A
        (orderedModalComplexTerm K A u (triadCycleTwice τ)))
      (FiniteComplexFourierAuthority.-ᶜ_ A (orderedModalComplexTerm K A u
        (Lattice.triadSwap (triadCycleTwice τ))))))
  (_+ᶜ_ A
    (FiniteComplexFourierAuthority.-ᶜ_ A (orderedModalComplexTerm K A u τ))
    (FiniteComplexFourierAuthority.-ᶜ_ A
      (orderedModalComplexTerm K A u (Lattice.triadSwap τ))))

realPartSixTermComplexNormalForm :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  realPart A (sixTermComplexNormalForm K A u τ) ≡
  uniformModalTransferSumNoLeray K A u τ
realPartSixTermComplexNormalForm K A u τ =
  trans
    (realPartAdd A leftPairs thirdPair)
    (cong₂ (Scalar._+_ S)
      (trans
        (realPartAdd A firstPair secondPair)
        (cong₂ (Scalar._+_ S)
          (trans
            (realPartAdd A first firstSwap)
            (cong₂ (Scalar._+_ S) (realPartNeg A firstTerm)
              (realPartNeg A firstSwapTerm)))
          (trans
            (realPartAdd A second secondSwap)
            (cong₂ (Scalar._+_ S) (realPartNeg A secondTerm)
              (realPartNeg A secondSwapTerm)))))
      (trans
        (realPartAdd A third thirdSwap)
        (cong₂ (Scalar._+_ S) (realPartNeg A thirdTerm)
          (realPartNeg A thirdSwapTerm))))
  where
  S = Algebra.orderedScalar K
  c₁ = Lattice.triadCycle τ
  c₂ = triadCycleTwice τ
  c₃ = τ
  firstTerm = orderedModalComplexTerm K A u c₁
  firstSwapTerm = orderedModalComplexTerm K A u (Lattice.triadSwap c₁)
  secondTerm = orderedModalComplexTerm K A u c₂
  secondSwapTerm = orderedModalComplexTerm K A u (Lattice.triadSwap c₂)
  thirdTerm = orderedModalComplexTerm K A u c₃
  thirdSwapTerm = orderedModalComplexTerm K A u (Lattice.triadSwap c₃)
  first = FiniteComplexFourierAuthority.-ᶜ_ A firstTerm
  firstSwap = FiniteComplexFourierAuthority.-ᶜ_ A firstSwapTerm
  second = FiniteComplexFourierAuthority.-ᶜ_ A secondTerm
  secondSwap = FiniteComplexFourierAuthority.-ᶜ_ A secondSwapTerm
  third = FiniteComplexFourierAuthority.-ᶜ_ A thirdTerm
  thirdSwap = FiniteComplexFourierAuthority.-ᶜ_ A thirdSwapTerm
  firstPair = _+ᶜ_ A first firstSwap
  secondPair = _+ᶜ_ A second secondSwap
  thirdPair = _+ᶜ_ A third thirdSwap
  leftPairs = _+ᶜ_ A firstPair secondPair

threeTransferSumWithoutLeray :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  modalTransferSum K A (coefficient u) τ ≡
  modalTransferSumNoLeray K A (coefficient u) τ
threeTransferSumWithoutLeray K A M u τ =
  cong₂ (Scalar._+_ S)
    (cong₂ (Scalar._+_ S)
      (modalTransferPWithoutLeray K A M u τ)
      (modalTransferQWithoutLeray K A M u τ))
    (modalTransferRWithoutLeray K A M u τ)
  where
  S = Algebra.orderedScalar K

threeTransferSumRealNormalForm :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  modalTransferSum K A (coefficient u) τ ≡
  realPart A (sixTermComplexNormalForm K A (coefficient u) τ)
threeTransferSumRealNormalForm K A M u τ =
  trans
    (threeTransferSumWithoutLeray K A M u τ)
    (trans
      (modalTransferSumNoLerayEqualsUniform K A M u τ)
      (sym (realPartSixTermComplexNormalForm K A (coefficient u) τ)))

-- Diagnostic real-factor bridge.
--
-- This surface is retained because it is useful for a real-valued reduction,
-- but it is *not* the canonical Hermitian Fourier route: in general
-- `Re (a * b)` does not factor as `Re a * Re b`.  Consequently a concrete
-- C³ implementation should not attempt to inhabit this record merely from
-- bilinearity, reality, and incompressibility.  The authoritative next bridge
-- must keep the wave-dot and mode-pair factors complex through the six-term
-- cancellation, and apply `realPart` only at the end.  Keeping this record
-- explicitly diagnostic prevents that invalid factorisation from silently
-- becoming the physical conservation proof.
record SixTermRealPartAtomBridge
    (K : Algebra.ExactOrderedCommutativeRing)
    (A : FiniteComplexFourierAuthority K) (M : Nat)
    (u : FiniteFourierNSState K A M) (τ : Lattice.LatticeTriad) : Set₁ where
  field
    pA qA rA pB qB rB pC qC rC : Scalar.Scalar (Algebra.orderedScalar K)
    pairAB pairAC pairBC : Scalar.Scalar (Algebra.orderedScalar K)

    relations : Cancel.SixTermTriadRelations K
      pA qA rA pB qB rB pC qC rC

    firstOccurrence :
      Scalar.neg (Algebra.orderedScalar K) (realPart A
        (orderedModalComplexTerm K A (coefficient u) (Lattice.triadCycle τ))) ≡
      Scalar._*_ (Algebra.orderedScalar K) qA pairBC
    secondOccurrence :
      Scalar.neg (Algebra.orderedScalar K) (realPart A
        (orderedModalComplexTerm K A (coefficient u)
          (Lattice.triadSwap (Lattice.triadCycle τ)))) ≡
      Scalar._*_ (Algebra.orderedScalar K) pB pairAC
    thirdOccurrence :
      Scalar.neg (Algebra.orderedScalar K) (realPart A
        (orderedModalComplexTerm K A (coefficient u) (triadCycleTwice τ))) ≡
      Scalar._*_ (Algebra.orderedScalar K) rB pairAC
    fourthOccurrence :
      Scalar.neg (Algebra.orderedScalar K) (realPart A
        (orderedModalComplexTerm K A (coefficient u)
          (Lattice.triadSwap (triadCycleTwice τ)))) ≡
      Scalar._*_ (Algebra.orderedScalar K) qC pairAB
    fifthOccurrence :
      Scalar.neg (Algebra.orderedScalar K)
        (realPart A (orderedModalComplexTerm K A (coefficient u) τ)) ≡
      Scalar._*_ (Algebra.orderedScalar K) pC pairAB
    sixthOccurrence :
      Scalar.neg (Algebra.orderedScalar K) (realPart A
        (orderedModalComplexTerm K A (coefficient u) (Lattice.triadSwap τ))) ≡
      Scalar._*_ (Algebra.orderedScalar K) rA pairBC

open SixTermRealPartAtomBridge public

sixTermComplexNormalFormRealPartZero :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  SixTermRealPartAtomBridge K A M u τ →
  realPart A (sixTermComplexNormalForm K A (coefficient u) τ) ≡
  Scalar.zero (Algebra.orderedScalar K)
sixTermComplexNormalFormRealPartZero K A M u τ B =
  trans
    (realPartSixTermComplexNormalForm K A (coefficient u) τ)
    (trans atomsToNumerator
      (Cancel.sixTermConvectionCancellation K
        (pA B) (qA B) (rA B) (pB B) (qB B) (rB B) (pC B) (qC B) (rC B)
        (pairAB B) (pairAC B) (pairBC B) (relations B)))
  where
  S = Algebra.orderedScalar K
  a₁ = Scalar.neg S (realPart A
    (orderedModalComplexTerm K A (coefficient u) (Lattice.triadCycle τ)))
  a₂ = Scalar.neg S (realPart A
    (orderedModalComplexTerm K A (coefficient u)
      (Lattice.triadSwap (Lattice.triadCycle τ))))
  a₃ = Scalar.neg S (realPart A
    (orderedModalComplexTerm K A (coefficient u) (triadCycleTwice τ)))
  a₄ = Scalar.neg S (realPart A
    (orderedModalComplexTerm K A (coefficient u)
      (Lattice.triadSwap (triadCycleTwice τ))))
  a₅ = Scalar.neg S (realPart A (orderedModalComplexTerm K A (coefficient u) τ))
  a₆ = Scalar.neg S (realPart A
    (orderedModalComplexTerm K A (coefficient u) (Lattice.triadSwap τ)))
  atomsToNumerator :
    uniformModalTransferSumNoLeray K A (coefficient u) τ ≡
    Cancel.sixTermConvectionNumerator K
      (pA B) (qA B) (rA B) (pB B) (qB B) (rB B) (pC B) (qC B) (rC B)
      (pairAB B) (pairAC B) (pairBC B)
  atomsToNumerator = trans
    (Algebra.addAssociative K
      (Scalar._+_ S a₁ a₂) (Scalar._+_ S a₃ a₄) (Scalar._+_ S a₅ a₆))
    (cong₂ (Scalar._+_ S)
      (cong₂ (Scalar._+_ S) (firstOccurrence B) (secondOccurrence B))
      (cong₂ (Scalar._+_ S)
        (cong₂ (Scalar._+_ S) (thirdOccurrence B) (fourthOccurrence B))
        (cong₂ (Scalar._+_ S) (fifthOccurrence B) (sixthOccurrence B))))

-- This is the live Navier--Stokes theorem.  The triple above is now a
-- concrete diagonal-aware Fourier/Leray expression; the record has no
-- fallback field from which conservation could be assumed.
record PhysicalModalTriadTransferConservation
    (K : Algebra.ExactOrderedCommutativeRing)
    (A : FiniteComplexFourierAuthority K) (M : Nat)
    (u : FiniteFourierNSState K A M) : Set₁ where
  field
    conserves : (τ : Lattice.LatticeTriad) →
      Lattice.zeroSum? τ ≡ true →
      Scalar._+_ (Algebra.orderedScalar K)
        (Scalar._+_ (Algebra.orderedScalar K)
          (transferP (physicalModalTransferTriple K A (coefficient u) τ))
          (transferQ (physicalModalTransferTriple K A (coefficient u) τ)))
        (transferR (physicalModalTransferTriple K A (coefficient u) τ)) ≡
      Scalar.zero (Algebra.orderedScalar K)

open PhysicalModalTriadTransferConservation public

physicalModalTriadTransferConservationFromAtoms :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) →
  ((τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
    SixTermRealPartAtomBridge K A M u τ) →
  PhysicalModalTriadTransferConservation K A M u
physicalModalTriadTransferConservationFromAtoms K A M u atoms = record
  { conserves = λ τ zeroSum →
      trans
        (threeTransferSumRealNormalForm K A M u τ)
        (sixTermComplexNormalFormRealPartZero K A M u τ (atoms τ zeroSum))
  }

-- The preceding constructor is intentionally diagnostic-only for the reason
-- documented above.  It must not be used as evidence that the concrete
-- Hermitian Fourier transfer conserves energy.  The live physical theorem is
-- the forthcoming complex multilinear bridge followed by `realPart`.
realFactorAtomBridgePhysicalClosed : Bool
realFactorAtomBridgePhysicalClosed = false

------------------------------------------------------------------------
-- Complex multilinear cancellation.
--
-- The physical Hermitian route keeps every wave-dot and mode-pair factor in
-- `Complex`.  For a zero-sum triad the six occurrences have three natural
-- pairs: occurrences 1+6 have the `u_q` wave-dot factor, 2+3 the `u_r`
-- factor, and 4+5 the `u_p` factor.  Each pair vanishes after using the
-- zero-sum wavevector relation together with the corresponding divergence
-- constraint.  This record deliberately exposes those *local* factorizations
-- and the purely additive regrouping.  It does not contain a conservation
-- field or a final six-term-zero field.
--
-- A concrete C^3/Leray authority must derive these fields from complex
-- bilinearity, Hermitian/reality transport, p + q + r = 0, and
-- k . u_k = 0.  Keeping that construction separate is fail-closed: the
-- theorem below is a genuine complex cancellation once this local algebra is
-- inhabited, but the current abstract Fourier authority has no concrete C^3
-- implementation yet.
------------------------------------------------------------------------

record SixTermComplexFactorization
    (K : Algebra.ExactOrderedCommutativeRing)
    (A : FiniteComplexFourierAuthority K) (M : Nat)
    (u : FiniteFourierNSState K A M) (τ : Lattice.LatticeTriad) : Set₁ where
  field
    complexAddZeroLeft :
      (z : Complex A) → _+ᶜ_ A (zeroComplex A) z ≡ z
    complexAddZeroRight :
      (z : Complex A) → _+ᶜ_ A z (zeroComplex A) ≡ z

    -- The displayed grouping is just additive reassociation/permutation of
    -- the literal six-term normal form.  Naming it separately keeps the
    -- three local Fourier cancellations below readable.
    groupedByWaveDotFactor :
      sixTermComplexNormalForm K A (coefficient u) τ ≡
      _+ᶜ_ A
        (_+ᶜ_ A
          (_+ᶜ_ A
            (FiniteComplexFourierAuthority.-ᶜ_ A
              (orderedModalComplexTerm K A (coefficient u)
                (Lattice.triadCycle τ)))
            (FiniteComplexFourierAuthority.-ᶜ_ A
              (orderedModalComplexTerm K A (coefficient u)
                (Lattice.triadSwap τ))))
          (_+ᶜ_ A
            (FiniteComplexFourierAuthority.-ᶜ_ A
              (orderedModalComplexTerm K A (coefficient u)
                (Lattice.triadSwap (Lattice.triadCycle τ))))
            (FiniteComplexFourierAuthority.-ᶜ_ A
              (orderedModalComplexTerm K A (coefficient u)
                (triadCycleTwice τ)))) )
        (_+ᶜ_ A
          (FiniteComplexFourierAuthority.-ᶜ_ A
            (orderedModalComplexTerm K A (coefficient u)
              (Lattice.triadSwap (triadCycleTwice τ))))
          (FiniteComplexFourierAuthority.-ᶜ_ A
            (orderedModalComplexTerm K A (coefficient u) τ)) )

    -- The three equations are the local complex cancellations.  Their
    -- intended derivations respectively use
    -- (r + p) . u_q = - q . u_q = 0,
    -- (q + p) . u_r = - r . u_r = 0, and
    -- (r + q) . u_p = - p . u_p = 0.
    qFactorPairZero :
      _+ᶜ_ A
        (FiniteComplexFourierAuthority.-ᶜ_ A
          (orderedModalComplexTerm K A (coefficient u)
            (Lattice.triadCycle τ)))
        (FiniteComplexFourierAuthority.-ᶜ_ A
          (orderedModalComplexTerm K A (coefficient u)
            (Lattice.triadSwap τ))) ≡ zeroComplex A
    rFactorPairZero :
      _+ᶜ_ A
        (FiniteComplexFourierAuthority.-ᶜ_ A
          (orderedModalComplexTerm K A (coefficient u)
            (Lattice.triadSwap (Lattice.triadCycle τ))))
        (FiniteComplexFourierAuthority.-ᶜ_ A
          (orderedModalComplexTerm K A (coefficient u)
            (triadCycleTwice τ))) ≡ zeroComplex A
    pFactorPairZero :
      _+ᶜ_ A
        (FiniteComplexFourierAuthority.-ᶜ_ A
          (orderedModalComplexTerm K A (coefficient u)
            (Lattice.triadSwap (triadCycleTwice τ))))
        (FiniteComplexFourierAuthority.-ᶜ_ A
          (orderedModalComplexTerm K A (coefficient u) τ)) ≡ zeroComplex A

open SixTermComplexFactorization public

sixTermComplexNormalFormZeroFromFactorization :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  SixTermComplexFactorization K A M u τ →
  sixTermComplexNormalForm K A (coefficient u) τ ≡ zeroComplex A
sixTermComplexNormalFormZeroFromFactorization K A M u τ F =
  trans
    (groupedByWaveDotFactor F)
    (trans
      (cong₂ (_+ᶜ_ A)
        (cong₂ (_+ᶜ_ A)
          (qFactorPairZero F)
          (rFactorPairZero F))
        (pFactorPairZero F))
      (trans
        (cong (λ x → _+ᶜ_ A x (zeroComplex A))
          (complexAddZeroLeft F (zeroComplex A)))
        (complexAddZeroLeft F (zeroComplex A))))

sixTermComplexNormalFormRealPartZeroFromFactorization :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  SixTermComplexFactorization K A M u τ →
  realPart A (sixTermComplexNormalForm K A (coefficient u) τ) ≡
  Scalar.zero (Algebra.orderedScalar K)
sixTermComplexNormalFormRealPartZeroFromFactorization K A M u τ F =
  trans
    (cong (realPart A)
      (sixTermComplexNormalFormZeroFromFactorization K A M u τ F))
    (realPartZero A)

-- This is the canonical physical constructor once the concrete complex C^3
-- factorization above is supplied.  Unlike the diagnostic real-factor route,
-- it never factors a real part of a complex product.
physicalModalTriadTransferConservationFromComplexFactorization :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) →
  ((τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
    SixTermComplexFactorization K A M u τ) →
  PhysicalModalTriadTransferConservation K A M u
physicalModalTriadTransferConservationFromComplexFactorization K A M u factors =
  record
    { conserves = λ τ zeroSum →
        trans
          (threeTransferSumRealNormalForm K A M u τ)
          (sixTermComplexNormalFormRealPartZeroFromFactorization K A M u τ
            (factors τ zeroSum))
    }

complexSixTermFactorizationPhysicalClosed : Bool
complexSixTermFactorizationPhysicalClosed = false

------------------------------------------------------------------------
-- Hermitian-safe six-term cancellation fallback.
--
-- A Hermitian energy calculation need not make the three local complex
-- pairs literal additive inverses.  The natural relation can instead be
-- `B-reverse = - conjugate B-forward`, which is enough only after applying
-- `realPart`.  This is therefore a convention-generic fallback interface.
-- The *current* corrected Fourier convention targets literal complex pair
-- cancellation, so `SixTermComplexFactorization` remains the canonical
-- physical route.  That stronger fact still has to be derived symbolically
-- from the local C^3 laws before it can close the physical gate.
--
-- The three pair expressions are ordered by their common wave-dot factor:
-- q, r, and p respectively.  The first field is deliberately an equality
-- only after `realPart`; it is where additive reassociation and the
-- Hermitian reversal are allowed to do their work without asserting that the
-- six-term complex sum itself is zero.
------------------------------------------------------------------------

qHermitianPair :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Complex A
qHermitianPair K A u τ = _+ᶜ_ A
  (FiniteComplexFourierAuthority.-ᶜ_ A
    (orderedModalComplexTerm K A u (Lattice.triadCycle τ)))
  (FiniteComplexFourierAuthority.-ᶜ_ A
    (orderedModalComplexTerm K A u (Lattice.triadSwap τ)))

qHermitianForward :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Complex A
qHermitianForward K A u τ = FiniteComplexFourierAuthority.-ᶜ_ A
  (orderedModalComplexTerm K A u (Lattice.triadCycle τ))

qHermitianReverse :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Complex A
qHermitianReverse K A u τ = FiniteComplexFourierAuthority.-ᶜ_ A
  (orderedModalComplexTerm K A u (Lattice.triadSwap τ))

rHermitianPair :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Complex A
rHermitianPair K A u τ = _+ᶜ_ A
  (FiniteComplexFourierAuthority.-ᶜ_ A
    (orderedModalComplexTerm K A u
      (Lattice.triadSwap (Lattice.triadCycle τ))))
  (FiniteComplexFourierAuthority.-ᶜ_ A
    (orderedModalComplexTerm K A u (triadCycleTwice τ)))

rHermitianForward :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Complex A
rHermitianForward K A u τ = FiniteComplexFourierAuthority.-ᶜ_ A
  (orderedModalComplexTerm K A u
    (Lattice.triadSwap (Lattice.triadCycle τ)))

rHermitianReverse :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Complex A
rHermitianReverse K A u τ = FiniteComplexFourierAuthority.-ᶜ_ A
  (orderedModalComplexTerm K A u (triadCycleTwice τ))

pHermitianPair :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Complex A
pHermitianPair K A u τ = _+ᶜ_ A
  (FiniteComplexFourierAuthority.-ᶜ_ A
    (orderedModalComplexTerm K A u
      (Lattice.triadSwap (triadCycleTwice τ))))
  (FiniteComplexFourierAuthority.-ᶜ_ A
    (orderedModalComplexTerm K A u τ))

pHermitianForward :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Complex A
pHermitianForward K A u τ = FiniteComplexFourierAuthority.-ᶜ_ A
  (orderedModalComplexTerm K A u
    (Lattice.triadSwap (triadCycleTwice τ)))

pHermitianReverse :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (u : Lattice.LatticeMode3 → Vec3C A) → (τ : Lattice.LatticeTriad) →
  Complex A
pHermitianReverse K A u τ = FiniteComplexFourierAuthority.-ᶜ_ A
  (orderedModalComplexTerm K A u τ)

qHermitianPairZeroFromLocalAlgebra :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) →
  (W : FiniteTriadWaveDotAlgebra K A) →
  (P : FiniteComplexProductNegationAlgebra K A) →
  (τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
  qHermitianPair K A (coefficient u) τ ≡ zeroComplex A
qHermitianPairZeroFromLocalAlgebra K A M u W P
  (Lattice.mkLatticeTriad p q r) zeroSum =
  trans expandedPair
    (negatedScaledPairZero K A W P
      (complexI A)
      (waveDot A r (coefficient u q))
      (waveDot A p (coefficient u q))
      (innerC A (coefficient u (Lattice.modeNeg p)) (coefficient u r))
      (innerC A (coefficient u (Lattice.modeNeg r)) (coefficient u p))
      (leftDotRightEqNegOutDotRight K A W (coefficient u)
        (Lattice.mkLatticeTriad p q r) zeroSum (divergenceFree u q))
      (negativeModePairingSymmetric K A M u r p))
  where
  expandedPair :
    qHermitianPair K A (coefficient u) (Lattice.mkLatticeTriad p q r) ≡
    _+ᶜ_ A
      (FiniteComplexFourierAuthority.-ᶜ_ A
        (_*ᶜ_ A
          (_*ᶜ_ A (complexI A) (waveDot A r (coefficient u q)))
          (innerC A (coefficient u (Lattice.modeNeg p)) (coefficient u r))))
      (FiniteComplexFourierAuthority.-ᶜ_ A
        (_*ᶜ_ A
          (_*ᶜ_ A (complexI A) (waveDot A p (coefficient u q)))
          (innerC A (coefficient u (Lattice.modeNeg r)) (coefficient u p))) )
  expandedPair =
    cong₂ (_+ᶜ_ A)
      (cong (FiniteComplexFourierAuthority.-ᶜ_ A)
        (orderedModalComplexTermExpansion K A (coefficient u)
          (Lattice.mkLatticeTriad q r p)))
      (cong (FiniteComplexFourierAuthority.-ᶜ_ A)
        (orderedModalComplexTermExpansion K A (coefficient u)
          (Lattice.mkLatticeTriad q p r)))

rHermitianPairZeroFromLocalAlgebra :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) →
  (W : FiniteTriadWaveDotAlgebra K A) →
  (P : FiniteComplexProductNegationAlgebra K A) →
  (τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
  rHermitianPair K A (coefficient u) τ ≡ zeroComplex A
rHermitianPairZeroFromLocalAlgebra K A M u W P
  (Lattice.mkLatticeTriad p q r) zeroSum =
  trans expandedPair
    (negatedScaledPairZero K A W P
      (complexI A)
      (waveDot A q (coefficient u r))
      (waveDot A p (coefficient u r))
      (innerC A (coefficient u (Lattice.modeNeg p)) (coefficient u q))
      (innerC A (coefficient u (Lattice.modeNeg q)) (coefficient u p))
      (leftDotOutEqNegRightDotOut K A W (coefficient u)
        (Lattice.mkLatticeTriad p q r) zeroSum (divergenceFree u r))
      (sym (negativeModePairingSymmetric K A M u p q)))
  where
  expandedPair :
    rHermitianPair K A (coefficient u) (Lattice.mkLatticeTriad p q r) ≡
    _+ᶜ_ A
      (FiniteComplexFourierAuthority.-ᶜ_ A
        (_*ᶜ_ A
          (_*ᶜ_ A (complexI A) (waveDot A q (coefficient u r)))
          (innerC A (coefficient u (Lattice.modeNeg p)) (coefficient u q))))
      (FiniteComplexFourierAuthority.-ᶜ_ A
        (_*ᶜ_ A
          (_*ᶜ_ A (complexI A) (waveDot A p (coefficient u r)))
          (innerC A (coefficient u (Lattice.modeNeg q)) (coefficient u p))) )
  expandedPair =
    cong₂ (_+ᶜ_ A)
      (cong (FiniteComplexFourierAuthority.-ᶜ_ A)
        (orderedModalComplexTermExpansion K A (coefficient u)
          (Lattice.mkLatticeTriad r q p)))
      (cong (FiniteComplexFourierAuthority.-ᶜ_ A)
        (orderedModalComplexTermExpansion K A (coefficient u)
          (Lattice.mkLatticeTriad r p q)))

pHermitianPairZeroFromLocalAlgebra :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) →
  (W : FiniteTriadWaveDotAlgebra K A) →
  (P : FiniteComplexProductNegationAlgebra K A) →
  (τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
  pHermitianPair K A (coefficient u) τ ≡ zeroComplex A
pHermitianPairZeroFromLocalAlgebra K A M u W P
  (Lattice.mkLatticeTriad p q r) zeroSum =
  trans expandedPair
    (negatedScaledPairZero K A W P
      (complexI A)
      (waveDot A r (coefficient u p))
      (waveDot A q (coefficient u p))
      (innerC A (coefficient u (Lattice.modeNeg q)) (coefficient u r))
      (innerC A (coefficient u (Lattice.modeNeg r)) (coefficient u q))
      (rightDotLeftEqNegOutDotLeft K A W (coefficient u)
        (Lattice.mkLatticeTriad p q r) zeroSum (divergenceFree u p))
      (sym (negativeModePairingSymmetric K A M u q r)))
  where
  expandedPair :
    pHermitianPair K A (coefficient u) (Lattice.mkLatticeTriad p q r) ≡
    _+ᶜ_ A
      (FiniteComplexFourierAuthority.-ᶜ_ A
        (_*ᶜ_ A
          (_*ᶜ_ A (complexI A) (waveDot A r (coefficient u p)))
          (innerC A (coefficient u (Lattice.modeNeg q)) (coefficient u r))))
      (FiniteComplexFourierAuthority.-ᶜ_ A
        (_*ᶜ_ A
          (_*ᶜ_ A (complexI A) (waveDot A q (coefficient u p)))
          (innerC A (coefficient u (Lattice.modeNeg r)) (coefficient u q))) )
  expandedPair =
    cong₂ (_+ᶜ_ A)
      (cong (FiniteComplexFourierAuthority.-ᶜ_ A)
        (orderedModalComplexTermExpansion K A (coefficient u)
          (Lattice.mkLatticeTriad p r q)))
      (cong (FiniteComplexFourierAuthority.-ᶜ_ A)
        (orderedModalComplexTermExpansion K A (coefficient u)
          (Lattice.mkLatticeTriad p q r)))

-- All nontrivial Fourier content of the strong complex factorization has now
-- been reduced to the three pair-zero lemmas above.  The remaining `grouped`
-- argument is a pure six-summand reassociation/permutation under the additive
-- laws in `W`; it is kept explicit until that generic shuffle is packaged.
physicalSixTermComplexFactorizationFromLocalAlgebra :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) →
  (W : FiniteTriadWaveDotAlgebra K A) →
  (P : FiniteComplexProductNegationAlgebra K A) →
  (τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
  SixTermComplexFactorization K A M u τ
physicalSixTermComplexFactorizationFromLocalAlgebra
  K A M u W P τ zeroSum =
  record
    { complexAddZeroLeft = complexAddZeroLeft W
    ; complexAddZeroRight = λ z →
        trans (complexAddCommutative W z (zeroComplex A))
          (complexAddZeroLeft W z)
    ; groupedByWaveDotFactor = complexAddSixPairShuffle K A W
        (qHermitianForward K A (coefficient u) τ)
        (rHermitianForward K A (coefficient u) τ)
        (rHermitianReverse K A (coefficient u) τ)
        (pHermitianForward K A (coefficient u) τ)
        (pHermitianReverse K A (coefficient u) τ)
        (qHermitianReverse K A (coefficient u) τ)
    ; qFactorPairZero = qHermitianPairZeroFromLocalAlgebra K A M u W P τ zeroSum
    ; rFactorPairZero = rHermitianPairZeroFromLocalAlgebra K A M u W P τ zeroSum
    ; pFactorPairZero = pHermitianPairZeroFromLocalAlgebra K A M u W P τ zeroSum
    }

-- The exact finite Fourier triad-conservation theorem, conditional only on
-- the explicit C3/additive authorities.  There is no caller-supplied
-- conservation witness, no real-part factorisation, and no leftover
-- six-term regrouping premise.
physicalModalTriadTransferConservationFromLocalAlgebra :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) →
  (W : FiniteTriadWaveDotAlgebra K A) →
  (P : FiniteComplexProductNegationAlgebra K A) →
  PhysicalModalTriadTransferConservation K A M u
physicalModalTriadTransferConservationFromLocalAlgebra K A M u W P =
  physicalModalTriadTransferConservationFromComplexFactorization K A M u
    (λ τ zeroSum →
      physicalSixTermComplexFactorizationFromLocalAlgebra
        K A M u W P τ zeroSum)

-- The exact scalar consequence used for a Hermitian reversal.  This is the
-- only place where the real ordered-ring authority enters the cancellation
-- route: `Re (B - conjugate B) = 0`.  It avoids the invalid stronger claim
-- that `B - conjugate B` is always the zero complex scalar.
negativeConjugatePairRealPartZero :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) →
  (forward reverse : Complex A) →
  reverse ≡ FiniteComplexFourierAuthority.-ᶜ_ A
    (conjugate A forward) →
  realPart A (_+ᶜ_ A forward reverse) ≡
  Scalar.zero (Algebra.orderedScalar K)
negativeConjugatePairRealPartZero K A forward reverse reverseLaw =
  trans
    (realPartAdd A forward reverse)
    (trans
      (cong (λ x → Scalar._+_ S (realPart A forward) x)
        (trans
          (cong (realPart A) reverseLaw)
          (trans
            (realPartNeg A (conjugate A forward))
            (cong (Scalar.neg S) (realPartConjugate A forward)))))
      (trans
        (Algebra.addCommutative K (realPart A forward)
          (Scalar.neg S (realPart A forward)))
        (Algebra.addInverseLeft K (realPart A forward))))
  where
  S = Algebra.orderedScalar K

record SixTermHermitianRealPartFactorization
    (K : Algebra.ExactOrderedCommutativeRing)
    (A : FiniteComplexFourierAuthority K) (M : Nat)
    (u : FiniteFourierNSState K A M) (τ : Lattice.LatticeTriad) : Set₁ where
  field
    -- The equality is stated at the energy-relevant real level.  A concrete
    -- proof should derive it by wave-dot linearity, reality transport, and
    -- Hermitian symmetry; it is not a conservation axiom.
    realPartGroupedByHermitianPairs :
      realPart A (sixTermComplexNormalForm K A (coefficient u) τ) ≡
      Scalar._+_ (Algebra.orderedScalar K)
        (Scalar._+_ (Algebra.orderedScalar K)
          (realPart A (qHermitianPair K A (coefficient u) τ))
          (realPart A (rHermitianPair K A (coefficient u) τ)))
        (realPart A (pHermitianPair K A (coefficient u) τ))

    -- These are the three genuine local Fourier obligations.  They are
    -- intentionally stated as negative-conjugate relations, not as complex
    -- zero identities and not as pre-cancelled real parts.
    qPairReverseIsNegativeConjugate :
      qHermitianReverse K A (coefficient u) τ ≡
      FiniteComplexFourierAuthority.-ᶜ_ A
        (conjugate A (qHermitianForward K A (coefficient u) τ))
    rPairReverseIsNegativeConjugate :
      rHermitianReverse K A (coefficient u) τ ≡
      FiniteComplexFourierAuthority.-ᶜ_ A
        (conjugate A (rHermitianForward K A (coefficient u) τ))
    pPairReverseIsNegativeConjugate :
      pHermitianReverse K A (coefficient u) τ ≡
      FiniteComplexFourierAuthority.-ᶜ_ A
        (conjugate A (pHermitianForward K A (coefficient u) τ))

open SixTermHermitianRealPartFactorization public

-- The concrete Fourier proof will supply the four local rewrites below:
-- additive regrouping at the real-part level and one negative-conjugate law
-- for each pair.  Packaging them here prevents later consumers from
-- accidentally replacing those laws by a bare conservation assumption.
physicalSixTermHermitianFactorization :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  realPart A (sixTermComplexNormalForm K A (coefficient u) τ) ≡
  Scalar._+_ (Algebra.orderedScalar K)
    (Scalar._+_ (Algebra.orderedScalar K)
      (realPart A (qHermitianPair K A (coefficient u) τ))
      (realPart A (rHermitianPair K A (coefficient u) τ)))
    (realPart A (pHermitianPair K A (coefficient u) τ)) →
  qHermitianReverse K A (coefficient u) τ ≡
  FiniteComplexFourierAuthority.-ᶜ_ A
    (conjugate A (qHermitianForward K A (coefficient u) τ)) →
  rHermitianReverse K A (coefficient u) τ ≡
  FiniteComplexFourierAuthority.-ᶜ_ A
    (conjugate A (rHermitianForward K A (coefficient u) τ)) →
  pHermitianReverse K A (coefficient u) τ ≡
  FiniteComplexFourierAuthority.-ᶜ_ A
    (conjugate A (pHermitianForward K A (coefficient u) τ)) →
  SixTermHermitianRealPartFactorization K A M u τ
physicalSixTermHermitianFactorization K A M u τ grouped qSkew rSkew pSkew =
  record
    { realPartGroupedByHermitianPairs = grouped
    ; qPairReverseIsNegativeConjugate = qSkew
    ; rPairReverseIsNegativeConjugate = rSkew
    ; pPairReverseIsNegativeConjugate = pSkew
    }

sixTermComplexNormalFormRealPartZeroFromHermitianPairs :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) → (τ : Lattice.LatticeTriad) →
  SixTermHermitianRealPartFactorization K A M u τ →
  realPart A (sixTermComplexNormalForm K A (coefficient u) τ) ≡
  Scalar.zero (Algebra.orderedScalar K)
sixTermComplexNormalFormRealPartZeroFromHermitianPairs K A M u τ H =
  trans
    (realPartGroupedByHermitianPairs H)
    (trans
      (cong₂ (Scalar._+_ S)
        (cong₂ (Scalar._+_ S)
          (negativeConjugatePairRealPartZero K A
            (qHermitianForward K A (coefficient u) τ)
            (qHermitianReverse K A (coefficient u) τ)
            (qPairReverseIsNegativeConjugate H))
          (negativeConjugatePairRealPartZero K A
            (rHermitianForward K A (coefficient u) τ)
            (rHermitianReverse K A (coefficient u) τ)
            (rPairReverseIsNegativeConjugate H)))
        (negativeConjugatePairRealPartZero K A
          (pHermitianForward K A (coefficient u) τ)
          (pHermitianReverse K A (coefficient u) τ)
          (pPairReverseIsNegativeConjugate H)))
      (trans
        (cong (λ x → Scalar._+_ S x (Scalar.zero S))
          (Algebra.addZeroLeft K (Scalar.zero S)))
        (Algebra.addZeroLeft K (Scalar.zero S))))
  where
  S = Algebra.orderedScalar K

-- This fallback constructor is appropriate only for a convention where the
-- three local pairs are provably negative-conjugate but not literal negatives.
-- It is not the canonical constructor for the present Fourier definitions;
-- see `physicalModalTriadTransferConservationFromComplexFactorization`.
physicalModalTriadTransferConservationFromHermitianPairs :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) →
  ((τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
    SixTermHermitianRealPartFactorization K A M u τ) →
  PhysicalModalTriadTransferConservation K A M u
physicalModalTriadTransferConservationFromHermitianPairs K A M u pairs =
  record
    { conserves = λ τ zeroSum →
        trans
          (threeTransferSumRealNormalForm K A M u τ)
          (sixTermComplexNormalFormRealPartZeroFromHermitianPairs K A M u τ
            (pairs τ zeroSum))
    }

-- A concrete C^3 implementation still has to derive the real-part grouping
-- and the three negative-conjugate pair laws.  Until then, this is a
-- fail-closed physical theorem surface rather than an inhabited NS theorem.
hermitianPairCancellationPhysicalClosed : Bool
hermitianPairCancellationPhysicalClosed = false

modalTriadTransferFromPhysicalConservation :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) →
  PhysicalModalTriadTransferConservation K A M u →
  (τ : Lattice.LatticeTriad) → Lattice.zeroSum? τ ≡ true →
  ModalTriadTransfer (Algebra.orderedScalar K) τ
modalTriadTransferFromPhysicalConservation K A M u C τ zeroSum = record
  { transferLeft = transferP triple
  ; transferRight = transferQ triple
  ; transferOut = transferR triple
  ; conservation = conserves C τ zeroSum
  }
  where
  triple = physicalModalTransferTriple K A (coefficient u) τ

-- The locally derived cancellation theorem now supplies the physical energy
-- lane on its proper dependent carrier.  This is intentionally *not* a
-- total `TriadTransferField`: a non-zero-sum labelled triple has no Fourier
-- modal-transfer semantics in this construction.
physicalZeroSumTriadTransferFieldFromLocalAlgebra :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  (u : FiniteFourierNSState K A M) →
  (W : FiniteTriadWaveDotAlgebra K A) →
  (P : FiniteComplexProductNegationAlgebra K A) →
  Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)
physicalZeroSumTriadTransferFieldFromLocalAlgebra K A M u W P σ =
  modalTriadTransferFromPhysicalConservation K A M u C
    (Energy.triad σ) (Energy.zeroSum σ)
  where
  C = physicalModalTriadTransferConservationFromLocalAlgebra K A M u W P

formalWeightedEnergyDerivative :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M →
  FiniteFourierNSState K A M →
  Scalar.Scalar (Algebra.orderedScalar K)
formalWeightedEnergyDerivative K A M z u =
  Energy.sumScalarList (Algebra.orderedScalar K)
    (terms (Sector.cutoffModes M))
  where
  terms : List Lattice.LatticeMode3 → List (Scalar.Scalar (Algebra.orderedScalar K))
  terms [] = []
  terms (k ∷ ks) =
    Scalar._*_ (Algebra.orderedScalar K) (Energy.weight z k)
      (realPart A (innerC A (coefficient u k) (velocityDot u k))) ∷
    terms ks

formalWeightedViscousDissipation :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (A : FiniteComplexFourierAuthority K) → (M : Nat) →
  Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M →
  FiniteFourierNSState K A M →
  Scalar.Scalar (Algebra.orderedScalar K)
formalWeightedViscousDissipation K A M z u =
  Energy.sumScalarList (Algebra.orderedScalar K)
    (terms (Sector.cutoffModes M))
  where
  S = Algebra.orderedScalar K
  terms : List Lattice.LatticeMode3 → List (Scalar.Scalar S)
  terms [] = []
  terms (k ∷ ks) =
    Scalar._*_ S (viscosity u)
      (Scalar._*_ S (Energy.weight z k)
        (Scalar._*_ S (modeSquaredNorm u k)
          (normSq A (coefficient u k)))) ∷
    terms ks

finiteComplexFourierDynamicsClosed : Bool
finiteComplexFourierDynamicsClosed = false
