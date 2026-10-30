module DASHI.Foundations.PolynomialC3S3RationalCharacterAlgebraExact where

-- Thin SAME-CARRIER adapter. Existing rational C2 projector mathematics belongs
-- to DASHI.Biology.MoonshineOrbifoldSectorProjectorExact (and historical
-- finite-group representation theory). This file owns only the eleven-orbit
-- reflection instantiation. No reassignment of prior DASHI/Ibrahim ownership.
-- Source-written; Agda kernel verification pending; TOE import owner retained.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; -_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Foundations.PolynomialC3S3TwentySevenOrbitQuotientExact as Q
import DASHI.Foundations.PolynomialVandermondeOrbitParityIntertwinerExact as Parity
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Biology.MoonshineOrbifoldSectorProjectorExact as Existing

Field11ℚ : Set
Field11ℚ = Q.Orbit11 → ℚ

reflect : Field11ℚ → Field11ℚ
reflect f o = f (Q.reflectionOn11 o)

reflectInvolutive : (f : Field11ℚ) (o : Q.Orbit11) →
  reflect (reflect f) o ≡ f o
reflectInvolutive f o = cong f (Q.reflection11Involutive o)

-- Construct the actual pair that the established rational C2 projector
-- already operates upon. No duplicate addition/subtraction/ring proof.
reflectionPair : Field11ℚ → Q.Orbit11 → Existing.RationalPair
reflectionPair f o =
  Existing.pair (f o) (f (Q.reflectionOn11 o))

positiveProjectionAt : Field11ℚ → Q.Orbit11 → ℚ
positiveProjectionAt f o =
  Existing.first (Existing.positiveProjection (reflectionPair f o))

negativeProjectionAt : Field11ℚ → Q.Orbit11 → ℚ
negativeProjectionAt f o =
  Existing.first (Existing.negativeProjection (reflectionPair f o))

-- Reuses the ACTUAL prior rational-solver theorem, not an equivalent
-- source-written arithmetic reimplementation.
reflectionPositiveNegativeReconstruct :
  (f : Field11ℚ) (o : Q.Orbit11) →
  positiveProjectionAt f o + negativeProjectionAt f o
  ≡ f o
reflectionPositiveNegativeReconstruct f o =
  Existing.positivePlusNegativeFirst (reflectionPair f o)

-- Reflection exchanges the two coordinates of this prior-owned pair.
reflectionPairSwap :
  (f : Field11ℚ) (o : Q.Orbit11) →
  reflectionPair f (Q.reflectionOn11 o)
    ≡ Existing.swap (reflectionPair f o)
reflectionPairSwap f o
  rewrite Q.reflection11Involutive o = Agda.Builtin.Equality.refl

-- Stronger SAME-CARRIER consequences of the original Moonshine pair laws.
-- No duplicate rational arithmetic: the positive/negative parts below are
-- literally the inherited orbifold projections on the orbit-reflection pair.

positiveReflectionInvariant :
  (f : Field11ℚ) (o : Q.Orbit11) →
  positiveProjectionAt f (Q.reflectionOn11 o) ≡ positiveProjectionAt f o
positiveReflectionInvariant f o =
  trans
    (cong (λ pair → Existing.first (Existing.positiveProjection pair))
      (reflectionPairSwap f o))
    (Existing.positiveProjectionSwapInvariantFirst (reflectionPair f o))

negativeReflectionOdd :
  (f : Field11ℚ) (o : Q.Orbit11) →
  negativeProjectionAt f (Q.reflectionOn11 o)
    ≡ - negativeProjectionAt f o
negativeReflectionOdd f o =
  trans
    (cong (λ pair → Existing.first (Existing.negativeProjection pair))
      (reflectionPairSwap f o))
    (Existing.negativeProjectionSwapOddFirst (reflectionPair f o))

-- The 11-orbit positive projector is an actual idempotent, not merely a
-- sign-labelled residue. This is obtained by transport of the ORIGINAL
-- two-coordinate rational projection's idempotence law.

positiveReflectionPair :
  (f : Field11ℚ) (o : Q.Orbit11) →
  reflectionPair (positiveProjectionAt f) o
    ≡ Existing.positiveProjection (reflectionPair f o)
positiveReflectionPair f o
  rewrite positiveReflectionInvariant f o = Agda.Builtin.Equality.refl

positiveProjectionAtIdempotent :
  (f : Field11ℚ) (o : Q.Orbit11) →
  positiveProjectionAt (positiveProjectionAt f) o ≡ positiveProjectionAt f o
positiveProjectionAtIdempotent f o =
  trans
    (cong (λ pair → Existing.first (Existing.positiveProjection pair))
      (positiveReflectionPair f o))
    (Existing.positiveProjectionIdempotentFirst (reflectionPair f o))

------------------------------------------------------------------------
-- Video-to-repository exact SAME SIGN CHARACTER, SAME RATIONAL FIELD.
-- Pull back the *original* S3 conjugacy action to the 11-orbit field
-- and project it by the prior-owned rational C2 sector operators.
-- Reuse original moonshine projector equations: do not copy ring
-- algebra or promote an 11-orbit field to an actual Monster module.
------------------------------------------------------------------------

s3OnRationalField :
  Perm.TriPermutation → Field11ℚ → Field11ℚ
s3OnRationalField p f o =
  f (Parity.fullS3ActionOnEleven p o)

positiveField : Field11ℚ → Field11ℚ
positiveField = positiveProjectionAt

negativeField : Field11ℚ → Field11ℚ
negativeField = negativeProjectionAt

ifParity : Perm.TriPermutation → Field11ℚ → Q.Orbit11 → ℚ
ifParity Perm.permIdentity f o = f o
ifParity Perm.permRotate f o = f o
ifParity Perm.permRotate2 f o = f o
ifParity Perm.permSwapLowMid f o = reflect f o
ifParity Perm.permSwapLowHigh f o = reflect f o
ifParity Perm.permSwapMidHigh f o = reflect f o

-- Definitional SAME-PAIR transport: applying reflection to the
-- input field and then selecting the orbit is definitionally the
-- original field at the reflected orbit. This is *not* the
-- positiveReflectionInvariant theorem itself; the two need trans.
positiveFieldReflectTransport :
  (f : Field11ℚ) (o : Q.Orbit11) →
  positiveField (reflect f) o ≡
  positiveField f (Q.reflectionOn11 o)
positiveFieldReflectTransport f o = refl

negativeFieldReflectTransport :
  (f : Field11ℚ) (o : Q.Orbit11) →
  negativeField (reflect f) o ≡
  negativeField f (Q.reflectionOn11 o)
negativeFieldReflectTransport f o = refl

positiveIntertwinesS3Parity :
  (p : Perm.TriPermutation) (f : Field11ℚ) (o : Q.Orbit11) →
  positiveField (s3OnRationalField p f) o ≡ positiveField f o
positiveIntertwinesS3Parity Perm.permIdentity f o = refl
positiveIntertwinesS3Parity Perm.permRotate f o = refl
positiveIntertwinesS3Parity Perm.permRotate2 f o = refl
positiveIntertwinesS3Parity Perm.permSwapLowMid f o =
  trans (positiveFieldReflectTransport f o) (positiveReflectionInvariant f o)
positiveIntertwinesS3Parity Perm.permSwapLowHigh f o =
  trans (positiveFieldReflectTransport f o) (positiveReflectionInvariant f o)
positiveIntertwinesS3Parity Perm.permSwapMidHigh f o =
  trans (positiveFieldReflectTransport f o) (positiveReflectionInvariant f o)

negativeIntertwinesS3Parity :
  (p : Perm.TriPermutation) (f : Field11ℚ) (o : Q.Orbit11) →
  negativeField (s3OnRationalField p f) o ≡
  Parity.signedRational (Parity.permutationParity p) (negativeField f o)
negativeIntertwinesS3Parity Perm.permIdentity f o = refl
negativeIntertwinesS3Parity Perm.permRotate f o = refl
negativeIntertwinesS3Parity Perm.permRotate2 f o = refl
negativeIntertwinesS3Parity Perm.permSwapLowMid f o =
  trans (negativeFieldReflectTransport f o) (negativeReflectionOdd f o)
negativeIntertwinesS3Parity Perm.permSwapLowHigh f o =
  trans (negativeFieldReflectTransport f o) (negativeReflectionOdd f o)
negativeIntertwinesS3Parity Perm.permSwapMidHigh f o =
  trans (negativeFieldReflectTransport f o) (negativeReflectionOdd f o)

-- Compare to Parity.vandermondeIntertwinesSign:
-- both arrows use identical S3 -> C2 and its action by +/-1
-- on ℚ; the underlying object carriers remain DIFFERENT.
-- The adapter is an actual imported same-carrier morphism, not
-- a new invented Moonshine/Vandermonde equality.

s3OnRationalFieldFactorsThroughParity :
  (p : Perm.TriPermutation) (f : Field11ℚ) (o : Q.Orbit11) →
  s3OnRationalField p f o ≡ ifParity p f o
s3OnRationalFieldFactorsThroughParity Perm.permIdentity f o = refl
s3OnRationalFieldFactorsThroughParity Perm.permRotate f o = refl
s3OnRationalFieldFactorsThroughParity Perm.permRotate2 f o = refl
s3OnRationalFieldFactorsThroughParity Perm.permSwapLowMid f o = refl
s3OnRationalFieldFactorsThroughParity Perm.permSwapLowHigh f o = refl
s3OnRationalFieldFactorsThroughParity Perm.permSwapMidHigh f o = refl
