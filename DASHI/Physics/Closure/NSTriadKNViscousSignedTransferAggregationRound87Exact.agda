module DASHI.Physics.Closure.NSTriadKNViscousSignedTransferAggregationRound87Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND87 / SIGNED AGGREGATION OF THE VISCOUS TRIAD MARGIN
--
-- The packet transfer q_K is a signed real Fourier pairing.  Therefore a
-- negative viscous coefficient on every selected HH->low triad does NOT by
-- itself imply a negative weighted aggregate from q_K>0: negative triad
-- transfer can reverse a termwise inequality.
--
-- The exact repair is to centre the geometric coefficient c_t at a uniform
-- negative baseline -M:
--
--   sum_t c_t tau_t
--     = -M sum_t tau_t + sum_t (c_t+M) tau_t.
--
-- The first term is the desired viscous margin.  The second term is the exact
-- signed-transfer residual.  If every tau_t is nonnegative and c_t<=-M, the
-- residual is nonpositive and the margin follows.  Without sign control on the
-- tau_t, it is a genuine remainder and must be bounded from the actual packet
-- transfer geometry.
--
-- An exact two-atom counterexample makes the logical point sharp:
--
--   c=(-1,-4), tau=(2,-1), M=1.
--
-- The total transfer is +1 and both coefficients are <=-1, but the weighted
-- sum is +2.  Thus positive aggregate transfer alone is insufficient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; -_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

record ViscousTransferAtom : Set where
  constructor viscous-transfer-atom
  field
    coefficient transfer : ℚ

open ViscousTransferAtom public

sumBy : (ViscousTransferAtom → ℚ) → List ViscousTransferAtom → ℚ
sumBy value [] = 0ℚ
sumBy value (atom ∷ atoms) = value atom + sumBy value atoms

totalTransfer : List ViscousTransferAtom → ℚ
totalTransfer = sumBy transfer

weightedTransfer : List ViscousTransferAtom → ℚ
weightedTransfer = sumBy (λ atom → coefficient atom * transfer atom)

centredResidual : ℚ → List ViscousTransferAtom → ℚ
centredResidual margin =
  sumBy (λ atom → (coefficient atom + margin) * transfer atom)

centredAggregationIdentity : ∀ margin atoms →
  weightedTransfer atoms
  ≡ (- margin) * totalTransfer atoms + centredResidual margin atoms
centredAggregationIdentity margin [] = solve [ margin ]
centredAggregationIdentity margin (atom ∷ atoms)
  rewrite centredAggregationIdentity margin atoms =
  solve
    ( margin ∷ coefficient atom ∷ transfer atom
    ∷ totalTransfer atoms ∷ centredResidual margin atoms ∷ [])

record NonnegativeUniformMarginAtom (margin : ℚ) : Set where
  constructor nonnegative-margin-atom
  field
    atom : ViscousTransferAtom
    transferNonnegative : 0ℚ ≤ transfer atom
    coefficientBelowBaseline : coefficient atom ≤ - margin

open NonnegativeUniformMarginAtom public

residualAtomNonpositive : ∀ {margin} →
  (entry : NonnegativeUniformMarginAtom margin) →
  (coefficient (atom entry) + margin) * transfer (atom entry) ≤ 0ℚ
residualAtomNonpositive {margin} entry =
  let
    c = coefficient (atom entry)
    t = transfer (atom entry)
    cPlusMNonpositive : c + margin ≤ 0ℚ
    cPlusMNonpositive =
      let raw = ℚP.+-mono-≤ (coefficientBelowBaseline entry) ℚP.≤-refl
      in subst (λ lhs → lhs ≤ 0ℚ) (solve (c ∷ margin ∷ [])) raw
    multiplied : (c + margin) * t ≤ 0ℚ * t
    multiplied =
      let instance tNN = nonNegative (transferNonnegative entry)
      in ℚP.*-monoʳ-≤-nonNeg t cPlusMNonpositive
  in
  subst (λ rhs → (c + margin) * t ≤ rhs) (solve [ t ]) multiplied

uniformEntriesResidualNonpositive : ∀ {margin} entries →
  sumBy
    (λ entry →
      (coefficient (atom entry) + margin) * transfer (atom entry))
    entries
  ≤ 0ℚ
uniformEntriesResidualNonpositive [] = ℚP.≤-refl
uniformEntriesResidualNonpositive (entry ∷ entries) =
  let tail = uniformEntriesResidualNonpositive entries
      added = ℚP.+-mono-≤ (residualAtomNonpositive entry) tail
  in subst (λ rhs →
      (coefficient (atom entry) + _)* transfer (atom entry)
        + sumBy
          (λ e → (coefficient (atom e) + _) * transfer (atom e)) entries
      ≤ rhs)
      (solve []) added

------------------------------------------------------------------------
-- Minimal exact countermodel to aggregate positivity.
------------------------------------------------------------------------

counterFirst counterSecond : ViscousTransferAtom
counterFirst = viscous-transfer-atom (- 1ℚ) (Int.+ 2)
counterSecond = viscous-transfer-atom (- (Int.+ 4)) (- 1ℚ)

counterAtoms : List ViscousTransferAtom
counterAtoms = counterFirst ∷ counterSecond ∷ []

counterTotalTransferPositive : totalTransfer counterAtoms ≡ 1ℚ
counterTotalTransferPositive = solve []

counterFirstCoefficientBelowMinusOne : coefficient counterFirst ≡ - 1ℚ
counterFirstCoefficientBelowMinusOne = refl

counterSecondCoefficientBelowMinusOne : coefficient counterSecond ≡ - (Int.+ 4)
counterSecondCoefficientBelowMinusOne = refl

counterWeightedTransferPositive : weightedTransfer counterAtoms ≡ Int.+ 2
counterWeightedTransferPositive = solve []

counterCentredResidual : centredResidual 1ℚ counterAtoms ≡ Int.+ 3
counterCentredResidual = solve []

round87UniformNegativeTriadCoefficientPlusPositiveAggregateImpliesNegativeWeightedSum : Bool
round87UniformNegativeTriadCoefficientPlusPositiveAggregateImpliesNegativeWeightedSum = false

round87SignedTransferResidualIdentifiedExactly : Bool
round87SignedTransferResidualIdentifiedExactly = true

round87PerTriadNonnegativeTransferWouldCloseViscousAggregation : Bool
round87PerTriadNonnegativeTransferWouldCloseViscousAggregation = true

round87SignedTransferResidualIdentifiedExactlyIsTrue :
  round87SignedTransferResidualIdentifiedExactly ≡ true
round87SignedTransferResidualIdentifiedExactlyIsTrue = refl

round87UniformNegativeTriadCoefficientPlusPositiveAggregateImpliesNegativeWeightedSumIsFalse :
  round87UniformNegativeTriadCoefficientPlusPositiveAggregateImpliesNegativeWeightedSum ≡ false
round87UniformNegativeTriadCoefficientPlusPositiveAggregateImpliesNegativeWeightedSumIsFalse = refl
