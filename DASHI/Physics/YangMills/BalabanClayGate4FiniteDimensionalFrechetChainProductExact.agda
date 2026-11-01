module DASHI.Physics.YangMills.BalabanClayGate4FiniteDimensionalFrechetChainProductExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact finite-dimensional first-order calculus.
--
-- Jean-Luc Guermond,
-- "Banach and Hilbert Spaces: Linear Mappings", Chapter 7 lecture notes,
-- Texas A&M University (2017). No DOI recorded.
-- Relationship: the Fréchet chain rule and higher-order chain formulas.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
-- Relationship: smooth matrix multiplication, exponential and logarithm on
-- finite-dimensional Lie-group charts.
--
-- Rather than treating the CMP109 product/chain rule as a physical axiom, this
-- module records exact increment expansions.  Composition computes the full
-- remainder
--
--   Dg(f(x))[R_f] + R_g(f(x), Df[R] + R_f),
--
-- and a bilinear product has the exact quadratic remainder delta-left times
-- delta-right.  The only remaining analytic input is that the displayed
-- remainders are little-o in the selected finite-dimensional norm.
------------------------------------------------------------------------

record AdditiveCarrier (Carrier : Set) : Set₁ where
  field
    zero : Carrier
    add : Carrier → Carrier → Carrier
    addAssociative : ∀ left middle right →
      add (add left middle) right ≡ add left (add middle right)

open AdditiveCarrier public

record ExactFirstOrderExpansion
    {Domain Codomain : Set}
    (domain : AdditiveCarrier Domain)
    (codomain : AdditiveCarrier Codomain) : Set₁ where
  field
    function : Domain → Codomain
    derivative : Domain → Domain → Codomain
    remainder : Domain → Domain → Codomain

    derivativeAdditive : ∀ point left right →
      derivative point (add domain left right)
      ≡ add codomain
          (derivative point left)
          (derivative point right)

    incrementExpansion : ∀ point increment →
      function (add domain point increment)
      ≡ add codomain
          (function point)
          (add codomain
            (derivative point increment)
            (remainder point increment))

open ExactFirstOrderExpansion public

composedDerivative :
  ∀ {Domain Middle Codomain}
    {domain : AdditiveCarrier Domain}
    {middle : AdditiveCarrier Middle}
    {codomain : AdditiveCarrier Codomain} →
  ExactFirstOrderExpansion domain middle →
  ExactFirstOrderExpansion middle codomain →
  Domain → Domain → Codomain
composedDerivative inner outer point increment =
  derivative outer (function inner point)
    (derivative inner point increment)

composedRemainder :
  ∀ {Domain Middle Codomain}
    {domain : AdditiveCarrier Domain}
    {middle : AdditiveCarrier Middle}
    {codomain : AdditiveCarrier Codomain} →
  ExactFirstOrderExpansion domain middle →
  ExactFirstOrderExpansion middle codomain →
  Domain → Domain → Codomain
composedRemainder {middle = middle} {codomain = codomain}
    inner outer point increment =
  add codomain
    (derivative outer (function inner point)
      (remainder inner point increment))
    (remainder outer (function inner point)
      (add middle
        (derivative inner point increment)
        (remainder inner point increment)))

composeExactFirstOrderExpansion :
  ∀ {Domain Middle Codomain}
    {domain : AdditiveCarrier Domain}
    {middle : AdditiveCarrier Middle}
    {codomain : AdditiveCarrier Codomain} →
  ExactFirstOrderExpansion domain middle →
  ExactFirstOrderExpansion middle codomain →
  ExactFirstOrderExpansion domain codomain
composeExactFirstOrderExpansion
    {domain = domain} {middle = middle} {codomain = codomain}
    inner outer = record
  { function = λ point → function outer (function inner point)
  ; derivative = composedDerivative inner outer
  ; remainder = composedRemainder inner outer
  ; derivativeAdditive = λ point left right →
      trans
        (cong
          (derivative outer (function inner point))
          (derivativeAdditive inner point left right))
        (derivativeAdditive outer
          (function inner point)
          (derivative inner point left)
          (derivative inner point right))
  ; incrementExpansion = λ point increment →
      trans
        (cong (function outer)
          (incrementExpansion inner point increment))
        (trans
          (incrementExpansion outer
            (function inner point)
            (add middle
              (derivative inner point increment)
              (remainder inner point increment)))
          (cong
            (add codomain (function outer (function inner point)))
            (trans
              (cong
                (λ selectedDerivative →
                  add codomain selectedDerivative
                    (remainder outer (function inner point)
                      (add middle
                        (derivative inner point increment)
                        (remainder inner point increment))))
                (derivativeAdditive outer
                  (function inner point)
                  (derivative inner point increment)
                  (remainder inner point increment)))
              (addAssociative codomain
                (derivative outer (function inner point)
                  (derivative inner point increment))
                (derivative outer (function inner point)
                  (remainder inner point increment))
                (remainder outer (function inner point)
                  (add middle
                    (derivative inner point increment)
                    (remainder inner point increment)))))))
  }

------------------------------------------------------------------------
-- Exact bilinear product rule.
------------------------------------------------------------------------

record BilinearProductAlgebra (Carrier : Set) : Set₁ where
  field
    additive : AdditiveCarrier Carrier
    multiply : Carrier → Carrier → Carrier

    leftDistributes : ∀ left middle right →
      multiply left (add additive middle right)
      ≡ add additive
          (multiply left middle)
          (multiply left right)

    rightDistributes : ∀ left middle right →
      multiply (add additive left middle) right
      ≡ add additive
          (multiply left right)
          (multiply middle right)

open BilinearProductAlgebra public

productDerivative :
  ∀ {Carrier}
    (algebra : BilinearProductAlgebra Carrier) →
  Carrier → Carrier → Carrier → Carrier → Carrier
productDerivative algebra left right leftIncrement rightIncrement =
  add (additive algebra)
    (multiply algebra left rightIncrement)
    (multiply algebra leftIncrement right)

productQuadraticRemainder :
  ∀ {Carrier}
    (algebra : BilinearProductAlgebra Carrier) →
  Carrier → Carrier → Carrier
productQuadraticRemainder algebra leftIncrement rightIncrement =
  multiply algebra leftIncrement rightIncrement

bilinearProductIncrementExpansion :
  ∀ {Carrier}
    (algebra : BilinearProductAlgebra Carrier)
    left right leftIncrement rightIncrement →
  multiply algebra
    (add (additive algebra) left leftIncrement)
    (add (additive algebra) right rightIncrement)
  ≡ add (additive algebra)
      (multiply algebra left right)
      (add (additive algebra)
        (productDerivative algebra
          left right leftIncrement rightIncrement)
        (productQuadraticRemainder algebra
          leftIncrement rightIncrement))
bilinearProductIncrementExpansion algebra left right leftIncrement rightIncrement =
  trans
    (rightDistributes algebra left leftIncrement
      (add (additive algebra) right rightIncrement))
    (trans
      (cong₂ (add (additive algebra))
        (leftDistributes algebra left right rightIncrement)
        (leftDistributes algebra leftIncrement right rightIncrement))
      (trans
        (addAssociative (additive algebra)
          (multiply algebra left right)
          (multiply algebra left rightIncrement)
          (add (additive algebra)
            (multiply algebra leftIncrement right)
            (multiply algebra leftIncrement rightIncrement)))
        (cong
          (add (additive algebra) (multiply algebra left right))
          (sym
            (addAssociative (additive algebra)
              (multiply algebra left rightIncrement)
              (multiply algebra leftIncrement right)
              (multiply algebra leftIncrement rightIncrement))))))

record FrechetRemainderMeaning
    (Domain Codomain Bound : Set)
    (domain : AdditiveCarrier Domain)
    (codomain : AdditiveCarrier Codomain)
    (expansion : ExactFirstOrderExpansion domain codomain) : Set₁ where
  field
    domainNorm : Domain → Bound
    codomainNorm : Codomain → Bound
    LittleOAtZero : (Domain → Codomain) → Set

    remainderLittleO : ∀ point →
      LittleOAtZero (remainder expansion point)

open FrechetRemainderMeaning public

exactFrechetChainRemainderLevel : ProofLevel
exactFrechetChainRemainderLevel = machineChecked

exactBilinearProductRemainderLevel : ProofLevel
exactBilinearProductRemainderLevel = machineChecked

finiteDimensionalFrechetChainRuleLevel : ProofLevel
finiteDimensionalFrechetChainRuleLevel = standardImported

physicalCMP109ComponentRemainderLittleOInputsLevel : ProofLevel
physicalCMP109ComponentRemainderLittleOInputsLevel = conditional

physicalCMP109MatrixProductBilinearityInputsLevel : ProofLevel
physicalCMP109MatrixProductBilinearityInputsLevel = conditional
