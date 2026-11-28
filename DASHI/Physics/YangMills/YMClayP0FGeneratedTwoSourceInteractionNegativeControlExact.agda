module DASHI.Physics.YangMills.YMClayP0FGeneratedTwoSourceInteractionNegativeControlExact where

------------------------------------------------------------------------
-- P0.F INDUCED-INTERACTION NEGATIVE CONTROL (FINITE EXACT RATIONAL).
--
-- This is NOT the SU(N) Wilson 4D continuum theory. It is a minimal
-- three-Z2-character lattice-gauge-style toy (two observed characters,
-- one shared interior character) with strictly positive interacting
-- factors; integration is ordinary normalized FINITE Haar averaging.
--
-- For sign characters x,y,z in {+1,-1}, take t=1/2:
--
--   K(x,y,z) = (1+t*x*z)(1+t*y*z).
--
-- After exact interior Haar integration:
--
--   rho_eff(x,y) = 1 + t^2*x*y.
--
-- Fine and coarse partition functions are BOTH 1.
-- Effective X- and Y-moments agree with bare independent Haar (zero),
-- but effective XY-moment and covariance equal 1/4; bare is zero.
-- The induced two-source coefficient does not decrease when repeated
-- at arbitrarily labelled cutoffs. Thus even faithful weighted
-- disintegration + same partition + matching one-point moments do not
-- imply all-three-moment R445 RG decay.
--
-- Further, rho_eff has nonzero 2x2 cross determinant (one), so cannot
-- factor into arbitrary independent one-character bare factors.
-- This is a SOURCE BOUNDARY, not a physical Balaban counterexample.
-- It does NOT determine the genuine SU(N) running coupling or prove/
-- refute Clay E1/D1/D2/N1/G1. No postulates, record assumptions or
-- unsafe --safe claim.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
open import Data.Integer.Base using (+_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (_≢_; cong₂; sym; trans)
open import Data.Empty using (⊥)

half quarter eighth : ℚ
half = (+ 1 / 2)
quarter = (+ 1 / 4)
eighth = (+ 1 / 8)

char : Bool → ℚ
char true = 1ℚ
char false = 0ℚ - 1ℚ

coupling : ℚ
coupling = half

-- True positive factors 1 +/- 1/2 on each selected interior bond.
fineFactor : Bool → Bool → ℚ
fineFactor x z = 1ℚ + coupling * (char x * char z)

-- An INTERACTING source density with the SAME interior z in both
-- factors (not the product of two independent interior Haar kernels).
fineWeight : Bool → Bool → Bool → ℚ
fineWeight x y z = fineFactor x z * fineFactor y z

-- Integral over the genuine shared (two-point) normalized Haar
-- interior, not separate z coordinates for the two factors.
interiorHaar : (Bool → ℚ) → ℚ
interiorHaar f = (f true + f false) * half

coarseHaar : (Bool → Bool → ℚ) → ℚ
coarseHaar f =
  ((f true true + f true false)
     + (f false true + f false false)) * quarter

fineHaar : (Bool → Bool → Bool → ℚ) → ℚ
fineHaar f = coarseHaar (λ x y → interiorHaar (λ z → f x y z))

-- Effective density is FROM original interacting fine weight, not
-- chosen separately to match a desired coarse distribution.
effectiveDensity : Bool → Bool → ℚ
effectiveDensity x y = interiorHaar (fineWeight x y)

bareDensity : Bool → Bool → ℚ
bareDensity x y = 1ℚ

effectiveTT : effectiveDensity true true ≡ (+ 5 / 4)
effectiveTT = ℚRing.solve-∀

effectiveTF : effectiveDensity true false ≡ (+ 3 / 4)
effectiveTF = ℚRing.solve-∀

effectiveFT : effectiveDensity false true ≡ (+ 3 / 4)
effectiveFT = ℚRing.solve-∀

effectiveFF : effectiveDensity false false ≡ (+ 5 / 4)
effectiveFF = ℚRing.solve-∀

-- Direct genuine fine => effective source partition identification:
-- the same interior Haar integral occurs definitionally on both sides.
finePartitionEqualsEffectivePartition :
  fineHaar fineWeight ≡ coarseHaar effectiveDensity
finePartitionEqualsEffectivePartition = refl

finePartitionIsOne : fineHaar fineWeight ≡ 1ℚ
finePartitionIsOne = ℚRing.solve-∀

effectivePartitionIsOne :
  coarseHaar effectiveDensity ≡ 1ℚ
effectivePartitionIsOne = ℚRing.solve-∀

barePartitionIsOne : coarseHaar bareDensity ≡ 1ℚ
barePartitionIsOne = ℚRing.solve-∀

-- Literal signed source characters and their product: three distinct
-- coarse tests F, G, FG on the SAME effective and bare finite law.
leftTest rightTest pairTest : Bool → Bool → ℚ
leftTest x y = char x
rightTest x y = char y
pairTest x y = char x * char y

fineMarkedMoment : (Bool → Bool → ℚ) → ℚ
fineMarkedMoment f =
  fineHaar (λ x y z → fineWeight x y z * f x y)

effectiveMoment : (Bool → Bool → ℚ) → ℚ
effectiveMoment f =
  coarseHaar (λ x y → effectiveDensity x y * f x y)

bareMoment : (Bool → Bool → ℚ) → ℚ
bareMoment f = coarseHaar (λ x y → bareDensity x y * f x y)

-- Arbitrary coupled marked tests are preserved by interior Haar
-- averaging. This is the finite analogue of the real F18/F19 source
-- transport, not a replacement for that source's proof.
fineMarkedMomentEqualsEffectiveMoment :
  (f : Bool → Bool → ℚ) →
  fineMarkedMoment f ≡ effectiveMoment f
fineMarkedMomentEqualsEffectiveMoment f = ℚRing.solve-∀

effectiveLeftMomentZero : effectiveMoment leftTest ≡ 0ℚ
effectiveLeftMomentZero = ℚRing.solve-∀

bareLeftMomentZero : bareMoment leftTest ≡ 0ℚ
bareLeftMomentZero = ℚRing.solve-∀

effectiveRightMomentZero : effectiveMoment rightTest ≡ 0ℚ
effectiveRightMomentZero = ℚRing.solve-∀

bareRightMomentZero : bareMoment rightTest ≡ 0ℚ
bareRightMomentZero = ℚRing.solve-∀

effectivePairMomentQuarter : effectiveMoment pairTest ≡ quarter
effectivePairMomentQuarter = ℚRing.solve-∀

barePairMomentZero : bareMoment pairTest ≡ 0ℚ
barePairMomentZero = ℚRing.solve-∀

-- The exact third RG moment error survives even though the two
-- first moment errors both vanish and both partitions equal one.
originalThreeMomentMismatchAtPair :
  effectiveMoment pairTest - bareMoment pairTest ≡ quarter
originalThreeMomentMismatchAtPair = ℚRing.solve-∀

effectiveConnectedCovariance : ℚ
effectiveConnectedCovariance =
  effectiveMoment pairTest
  - (effectiveMoment leftTest * effectiveMoment rightTest)

bareConnectedCovariance : ℚ
bareConnectedCovariance =
  bareMoment pairTest
  - (bareMoment leftTest * bareMoment rightTest)

sourceCovarianceDifferenceQuarter :
  effectiveConnectedCovariance - bareConnectedCovariance ≡ quarter
sourceCovarianceDifferenceQuarter = ℚRing.solve-∀

-- The induced two-character interaction cannot be rewritten as a
-- product of arbitrary independent one-character bare weights.
effectiveCrossDeterminant :
  (effectiveDensity true true * effectiveDensity false false)
  - (effectiveDensity true false * effectiveDensity false true)
    ≡ 1ℚ
effectiveCrossDeterminant = ℚRing.solve-∀

factorizedCrossDeterminantZero :
  (aPlus aMinus bPlus bMinus : ℚ) →
  ((aPlus * bPlus) * (aMinus * bMinus))
  - ((aPlus * bMinus) * (aMinus * bPlus))
    ≡ 0ℚ
factorizedCrossDeterminantZero ap am bp bm = ℚRing.solve-∀

oneNotZero : 1ℚ ≢ 0ℚ
oneNotZero ()

noIndependentBareFactorization :
  (aPlus aMinus bPlus bMinus : ℚ) →
  effectiveDensity true true ≡ aPlus * bPlus →
  effectiveDensity true false ≡ aPlus * bMinus →
  effectiveDensity false true ≡ aMinus * bPlus →
  effectiveDensity false false ≡ aMinus * bMinus →
  ⊥
noIndependentBareFactorization ap am bp bm eqTT eqTF eqFT eqFF =
  oneNotZero
    (trans
      (sym effectiveCrossDeterminant)
      (trans
        (cong₂ _-_
          (cong₂ _*_ eqTT eqFF)
          (cong₂ _*_ eqTF eqFT))
        (factorizedCrossDeterminantZero ap am bp bm)))

-- Mere relabelling of the finite model by a cutoff does not produce
-- UV decay. A physical RG estimate must use actual Wilson dynamics.
sameNondecayingPairErrorAtEveryFormalCutoff :
  (stage : Nat) →
  effectiveMoment pairTest - bareMoment pairTest ≡ quarter
sameNondecayingPairErrorAtEveryFormalCutoff stage =
  originalThreeMomentMismatchAtPair
