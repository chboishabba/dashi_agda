module DASHI.Cognition.PNF.GenericExpectedFibreRateExact where

------------------------------------------------------------------------
-- FINITE CONDITIONAL / FIBRE-LOCAL EXPECTED RATE
--
-- PNF fixes the admissible future quotient first.  Once each coarse fibre has
-- a local representation cost, ordinary finite expectation determines the
-- average extra rate.  This is deliberately a finite exact precursor of
-- conditional entropy, not a Shannon coding theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

record FibreRateAtom : Set where
  constructor fibreRateAtom
  field
    mass : ℚ
    localRate : ℚ
    massNonnegative : 0ℚ ≤ mass
    localRateNonnegative : 0ℚ ≤ localRate

open FibreRateAtom public

expectedAtomRate : FibreRateAtom → ℚ
expectedAtomRate atom = mass atom * localRate atom

totalMass : List FibreRateAtom → ℚ
totalMass [] = 0ℚ
totalMass (atom ∷ atoms) = mass atom + totalMass atoms

expectedResidualRate : List FibreRateAtom → ℚ
expectedResidualRate [] = 0ℚ
expectedResidualRate (atom ∷ atoms) =
  expectedAtomRate atom + expectedResidualRate atoms

record NormalizedFiniteFibreLaw : Set where
  constructor normalizedFiniteFibreLaw
  field
    fibres : List FibreRateAtom
    normalized : totalMass fibres ≡ 1ℚ

open NormalizedFiniteFibreLaw public

------------------------------------------------------------------------
-- Constant-rate specialization over an arbitrary finite probability list.
------------------------------------------------------------------------

record ProbabilityAtom : Set where
  constructor probabilityAtom
  field
    probabilityMass : ℚ
    probabilityNonnegative : 0ℚ ≤ probabilityMass

open ProbabilityAtom public

probabilityTotal : List ProbabilityAtom → ℚ
probabilityTotal [] = 0ℚ
probabilityTotal (a ∷ as) = probabilityMass a + probabilityTotal as

constantRateExpectation : ℚ → List ProbabilityAtom → ℚ
constantRateExpectation r [] = 0ℚ
constantRateExpectation r (a ∷ as) =
  probabilityMass a * r + constantRateExpectation r as

constantRateFactors : (r : ℚ) (atoms : List ProbabilityAtom) →
  constantRateExpectation r atoms ≡ probabilityTotal atoms * r
constantRateFactors r [] = solve-∀
constantRateFactors r (a ∷ as)
  rewrite constantRateFactors r as = solve-∀

normalizedConstantRateIsRate :
  (r : ℚ) (atoms : List ProbabilityAtom) →
  probabilityTotal atoms ≡ 1ℚ →
  constantRateExpectation r atoms ≡ r
normalizedConstantRateIsRate r atoms normalizedMass
  rewrite constantRateFactors r atoms | normalizedMass = solve-∀

------------------------------------------------------------------------
-- Fibre-local sparsity: a zero-rate fibre contributes exactly zero regardless
-- of its probability mass.
------------------------------------------------------------------------

zeroRateContribution : (p : ℚ) → p * 0ℚ ≡ 0ℚ
zeroRateContribution p = solve-∀

------------------------------------------------------------------------
-- Three-fibre specialization.  This strictly generalizes the signed-zero
-- 0/1/0 calculation: any normalized coarse law may carry arbitrary local
-- rates, and the oriented-zero widths recover exactly the zero-fibre mass.
------------------------------------------------------------------------

record ThreeFibreRateLaw : Set where
  constructor threeFibreRateLaw
  field
    negativeMass zeroMass positiveMass : ℚ
    negativeRate zeroRate positiveRate : ℚ
    normalized3 : negativeMass + zeroMass + positiveMass ≡ 1ℚ

open ThreeFibreRateLaw public

expectedThreeFibreRate : ThreeFibreRateLaw → ℚ
expectedThreeFibreRate law =
  negativeMass law * negativeRate law
  + zeroMass law * zeroRate law
  + positiveMass law * positiveRate law

orientedZeroNormalizedExpectedRate :
  (negativeMass zeroMass positiveMass : ℚ) →
  (norm : negativeMass + zeroMass + positiveMass ≡ 1ℚ) →
  expectedThreeFibreRate
    (threeFibreRateLaw
      negativeMass zeroMass positiveMass
      0ℚ 1ℚ 0ℚ
      norm) ≡ zeroMass
orientedZeroNormalizedExpectedRate negativeMass zeroMass positiveMass norm = solve-∀

------------------------------------------------------------------------
-- Boundary: these are expected fixed local widths.  Prefix-code optimality and
-- H(Q_future | Y_coarse) require a logarithm / coding theorem not asserted here.
------------------------------------------------------------------------
