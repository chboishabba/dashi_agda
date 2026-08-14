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
-- If every fibre uses the same rate r, expectation recovers r after
-- normalization.  The theorem is finite and exact over rationals.
------------------------------------------------------------------------

setRate : ℚ → FibreRateAtom → FibreRateAtom
setRate r atom = fibreRateAtom
  (mass atom) r (massNonnegative atom) (localRateNonnegative atom)

-- Rather than requiring an order proof for arbitrary replacement rates, use a
-- separate mass-only carrier for the constant-rate theorem.
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
normalizedConstantRateIsRate r atoms normalized
  rewrite constantRateFactors r atoms | normalized = solve-∀

------------------------------------------------------------------------
-- Fibre-local sparsity: a zero-rate fibre contributes exactly zero regardless
-- of its probability mass.
------------------------------------------------------------------------

zeroRateContribution : (p : ℚ) → p * 0ℚ ≡ 0ℚ
zeroRateContribution p = solve-∀

------------------------------------------------------------------------
-- Three-fibre specialization.  This strictly generalizes the signed-zero
-- 0/1/0 calculation: any law with local rates r-, r0, r+ has expectation
-- p- r- + p0 r0 + p+ r+.
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

orientedZeroRateIdentity :
  (negativeMass zeroMass positiveMass : ℚ) →
  expectedThreeFibreRate
    (threeFibreRateLaw
      negativeMass zeroMass positiveMass
      0ℚ 1ℚ 0ℚ
      solve-∀)
  ≡ zeroMass
orientedZeroRateIdentity negativeMass zeroMass positiveMass = solve-∀

------------------------------------------------------------------------
-- The preceding constructor requires normalization, so its fully generic
-- variables cannot inhabit it.  The proof-facing normalized form follows.
------------------------------------------------------------------------

orientedZeroNormalizedExpectedRate :
  (negativeMass zeroMass positiveMass : ℚ) →
  negativeMass + zeroMass + positiveMass ≡ 1ℚ →
  expectedThreeFibreRate
    (threeFibreRateLaw
      negativeMass zeroMass positiveMass
      0ℚ 1ℚ 0ℚ
      _) ≡ zeroMass
orientedZeroNormalizedExpectedRate negativeMass zeroMass positiveMass norm = solve-∀

------------------------------------------------------------------------
-- Boundary: these are expected fixed local widths.  Prefix-code optimality and
-- H(Q_future | Y_coarse) require a logarithm / coding theorem not asserted here.
------------------------------------------------------------------------
