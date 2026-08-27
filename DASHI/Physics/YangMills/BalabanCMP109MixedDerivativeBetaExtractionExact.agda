module DASHI.Physics.YangMills.BalabanCMP109MixedDerivativeBetaExtractionExact where

------------------------------------------------------------------------
-- ROUND88: CMP109 (5.36)--(5.41) -- BETA IS ONE OFF-DIAGONAL MIXED JET
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- SOURCE LOCATOR / MATHEMATICAL ROLE
--
-- Sect. 5, equations (5.36)--(5.38), uses Ward identities and lattice Euclidean
-- symmetry to write the vacuum-polarization tensor as
--
--   Pi_{mu nu}(p)
--     = beta (delta_{mu nu} Delta(p) - d_mu(p) d_nu(p)) + Pi'_{mu nu}(p),
--
-- where Pi' begins at third order in lattice derivatives.  Equations
-- (5.39)--(5.41) then recover beta from one mixed derivative of an
-- off-diagonal component at the identity.
--
-- DASHI CONTRIBUTION
--
-- Make that source reduction an exact finite jet compiler.  For mu /= nu the
-- Kronecker term vanishes, so the quadratic off-diagonal transverse jet has
-- mixed coefficient -beta (with the canonical derivative normalization).  A
-- third-order remainder has zero two-jet by construction.  Therefore the
-- NEGATIVE mixed second coefficient of the full off-diagonal two-jet is exactly
-- beta.
--
-- This changes the literal one-loop target: we do not need to certify arbitrary
-- unused components of the momentum kernel before extracting the RG coupling.
-- The physical finite calculation may target the one mixed coefficient consumed
-- by CMP109, after the literal Wilson/FP/Haar diagrams and Ward symmetry are
-- identified with this jet.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

-- Two-variable two-jet at the identity.  Only coefficients through total degree
-- two are retained; this is exactly the quotient needed by the mixed derivative.
record OffDiagonalTwoJet : Set where
  constructor offDiagonalTwoJet
  field
    constant linearLeft linearRight : ℚ
    squareLeft mixedCross squareRight : ℚ
open OffDiagonalTwoJet public

zeroTwoJet : OffDiagonalTwoJet
zeroTwoJet = offDiagonalTwoJet 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ

addTwoJet : OffDiagonalTwoJet → OffDiagonalTwoJet → OffDiagonalTwoJet
addTwoJet left right = offDiagonalTwoJet
  (constant left + constant right)
  (linearLeft left + linearLeft right)
  (linearRight left + linearRight right)
  (squareLeft left + squareLeft right)
  (mixedCross left + mixedCross right)
  (squareRight left + squareRight right)

-- For an off-diagonal component the quadratic transverse structure is
-- - beta d_mu d_nu.  Canonical lattice derivative coordinates have unit linear
-- coefficient at the identity, hence the mixed two-jet coefficient is -beta.
transverseOffDiagonalTwoJet : ℚ → OffDiagonalTwoJet
transverseOffDiagonalTwoJet beta =
  offDiagonalTwoJet 0ℚ 0ℚ 0ℚ 0ℚ (- beta) 0ℚ

-- A remainder that begins at total derivative degree >= 3 has identically zero
-- image in the two-jet quotient.  This is a TYPE, not a numerical assumption.
data ThirdOrderRemainderTwoJet : OffDiagonalTwoJet → Set where
  thirdOrderRemainder : ThirdOrderRemainderTwoJet zeroTwoJet

record CMP109OffDiagonalSecondJetData : Set where
  field
    beta : ℚ
    remainderJet : OffDiagonalTwoJet
    remainderStartsAtThirdOrder : ThirdOrderRemainderTwoJet remainderJet
open CMP109OffDiagonalSecondJetData public

fullOffDiagonalTwoJet : CMP109OffDiagonalSecondJetData → OffDiagonalTwoJet
fullOffDiagonalTwoJet dataSet =
  addTwoJet
    (transverseOffDiagonalTwoJet (beta dataSet))
    (remainderJet dataSet)

mixedDerivativeCoefficient : OffDiagonalTwoJet → ℚ
mixedDerivativeCoefficient = mixedCross

thirdOrderRemainderHasZeroMixedTwoJet :
  ∀ {jet} → ThirdOrderRemainderTwoJet jet →
  mixedDerivativeCoefficient jet ≡ 0ℚ
thirdOrderRemainderHasZeroMixedTwoJet thirdOrderRemainder = refl

cmp109MixedDerivativeExtractsBeta :
  (dataSet : CMP109OffDiagonalSecondJetData) →
  (- mixedDerivativeCoefficient (fullOffDiagonalTwoJet dataSet))
  ≡ beta dataSet
cmp109MixedDerivativeExtractsBeta dataSet
  with remainderStartsAtThirdOrder dataSet
... | thirdOrderRemainder = ℚRing.solve-∀ (beta dataSet)

cmp109MixedDerivativeBetaExtractionLevel : ProofLevel
cmp109MixedDerivativeBetaExtractionLevel = machineChecked

-- Physical finite seam after this reduction: construct the SAME literal
-- Wilson/reduced-FP/Haar off-diagonal vacuum-polarization two-jet and prove its
-- Ward/symmetry remainder starts at derivative degree three.  The beta consumer
-- then needs only its mixed coefficient, not a stronger all-component kernel
-- enclosure.
literalWilsonFPHaarOffDiagonalTwoJetIdentificationLevel : ProofLevel
literalWilsonFPHaarOffDiagonalTwoJetIdentificationLevel = conditional
