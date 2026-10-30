module DASHI.Foundations.PolynomialC3S3OrbitSamplingProjectionExact where

-- NESTED ORBIT-SAMPLING RETRACTIONS ON ACTUAL 27-TRIT FIELDS.
-- Classical finite group actions; actual 11/7 canonical representatives
-- originate in existing ternary seven-shape and new #1414 11-orbit owner.
--
-- P_C3(f)(x) = f(rep11(class11 x))
-- P_S3(f)(x) = f(rep7(shapeClass x))
--
-- Both are pointwise idempotent, invariant, and compatible:
-- P_C3 P_S3 = P_S3 P_C3 = P_S3.
-- This is a representative-sampling projector, NOT the Fourier
-- group-average over C3 or S3; it needs no division, works on trits.
-- Source-written Agda, kernel pending. No Monster/sonic/wild claim.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Foundations.PolynomialC3S3TwentySevenOrbitQuotientExact as Q
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape

projectC3 : Q.Field27 → Q.Field27
projectC3 f x =
  f (Q.representative11 (Q.classify11 x))

projectS3 : Q.Field27 → Q.Field27
projectS3 f x =
  f (Shape.shapeRepresentative (Shape.shapeClass x))

projectC3Idempotent :
  (f : Q.Field27) (x : Q.Code27) →
  projectC3 (projectC3 f) x ≡ projectC3 f x
projectC3Idempotent f x =
  cong (λ o → f (Q.representative11 o))
    (Q.classifyRepresentative11 (Q.classify11 x))

projectS3Idempotent :
  (f : Q.Field27) (x : Q.Code27) →
  projectS3 (projectS3 f) x ≡ projectS3 f x
projectS3Idempotent f x =
  cong (λ shape → f (Shape.shapeRepresentative shape))
    (Shape.representativeHasDeclaredShape (Shape.shapeClass x))

projectC3Invariant :
  (f : Q.Field27) (x : Q.Code27) →
  projectC3 f (Shape.conjugateCode Shape.permRotate x)
    ≡ projectC3 f x
projectC3Invariant f x =
  Q.inflate11C3Invariant
    (λ o → f (Q.representative11 o)) x

projectS3Invariant :
  (f : Q.Field27) (p : Shape.TriPermutation) (x : Q.Code27) →
  projectS3 f (Shape.conjugateCode p x) ≡ projectS3 f x
projectS3Invariant f p x =
  Q.inflate7To27S3Invariant
    (λ shape → f (Shape.shapeRepresentative shape)) p x

projectC3FixesInvariant :
  (f : Q.Field27) →
  ((x : Q.Code27) →
    f (Shape.conjugateCode Shape.permRotate x) ≡ f x) →
  (x : Q.Code27) → projectC3 f x ≡ f x
projectC3FixesInvariant f inv x =
  sym (Q.everyC3InvariantFieldDescends f inv x)

projectS3FixesInvariant :
  (f : Q.Field27) →
  ((p : Shape.TriPermutation) (x : Q.Code27) →
    f (Shape.conjugateCode p x) ≡ f x) →
  (x : Q.Code27) → projectS3 f x ≡ f x
projectS3FixesInvariant f inv x =
  sym (Q.everyS3InvariantFieldDescends f inv x)

shapeOfRepresentative11 :
  (o : Q.Orbit11) →
  Shape.shapeClass (Q.representative11 o) ≡ Q.mergeToSeven o
shapeOfRepresentative11 o =
  trans (Q.classificationFactors (Q.representative11 o))
    (cong Q.mergeToSeven (Q.classifyRepresentative11 o))

-- A concrete compatibility choice: the original seven-shape
-- representatives are also the chosen representatives for their
-- selected eleven-orbit classes. Source proof is seven cases.
chosenSevenRepresentativeIsElevenRepresentative :
  (shape : Shape.ShapeOrbit7) →
  Q.representative11 (Q.sevenSection shape) ≡
    Shape.shapeRepresentative shape
chosenSevenRepresentativeIsElevenRepresentative Shape.identityShape = refl
chosenSevenRepresentativeIsElevenRepresentative Shape.threeCycleShape = refl
chosenSevenRepresentativeIsElevenRepresentative Shape.transpositionShape = refl
chosenSevenRepresentativeIsElevenRepresentative Shape.constantShape = refl
chosenSevenRepresentativeIsElevenRepresentative Shape.rank2OneFixedShape = refl
chosenSevenRepresentativeIsElevenRepresentative Shape.rank2TwoFixedShape = refl
chosenSevenRepresentativeIsElevenRepresentative Shape.rank2TwoCycleShape = refl

projectC3AfterS3IsS3 :
  (f : Q.Field27) (x : Q.Code27) →
  projectC3 (projectS3 f) x ≡ projectS3 f x
projectC3AfterS3IsS3 f x =
  cong (λ shape → f (Shape.shapeRepresentative shape))
    (trans (shapeOfRepresentative11 (Q.classify11 x))
      (sym (Q.classificationFactors x)))

projectS3AfterC3IsS3 :
  (f : Q.Field27) (x : Q.Code27) →
  projectS3 (projectC3 f) x ≡ projectS3 f x
projectS3AfterC3IsS3 f x =
  cong f
    (chosenSevenRepresentativeIsElevenRepresentative
      (Shape.shapeClass x))

-- Two-sided absorption means the lower seven-field projection
-- is a genuine retract of the eleven-field projection's range,
-- with the ORIGINAL seven-shape classifier, not the unrelated
-- output-phase normalized "seven nonunits".

------------------------------------------------------------------------
-- O78: POLYMORPHIC SAME-CARRIER ORBIT-SAMPLING RETRACTIONS.
--
-- Reuses the precise original 27-code S3/C3 quotient, chosen canonical
-- representatives and the trit sampling owner above. The proof does not
-- inspect the value carrier; hence it applies to rational fields too.
-- This is NOT Reynolds averaging: sampling one chosen representative
-- is generally neither canonical nor an invariant inner-product map.
-- Classical finite group actions (Dixon--Mortimer); DASHI owns these
-- concrete representative choices and the adapter, kernel pending.
------------------------------------------------------------------------

projectC3Any :
  ∀ {A : Set} → (Q.Code27 → A) → Q.Code27 → A
projectC3Any f x =
  f (Q.representative11 (Q.classify11 x))

projectS3Any :
  ∀ {A : Set} → (Q.Code27 → A) → Q.Code27 → A
projectS3Any f x =
  f (Shape.shapeRepresentative (Shape.shapeClass x))

projectC3AnyIdempotent :
  ∀ {A : Set} (f : Q.Code27 → A) (x : Q.Code27) →
  projectC3Any (projectC3Any f) x ≡ projectC3Any f x
projectC3AnyIdempotent f x =
  cong (λ o → f (Q.representative11 o))
    (Q.classifyRepresentative11 (Q.classify11 x))

projectS3AnyIdempotent :
  ∀ {A : Set} (f : Q.Code27 → A) (x : Q.Code27) →
  projectS3Any (projectS3Any f) x ≡ projectS3Any f x
projectS3AnyIdempotent f x =
  cong (λ shape → f (Shape.shapeRepresentative shape))
    (Shape.representativeHasDeclaredShape (Shape.shapeClass x))

projectC3AnyInvariant :
  ∀ {A : Set} (f : Q.Code27 → A) (x : Q.Code27) →
  projectC3Any f (Shape.conjugateCode Shape.permRotate x) ≡
  projectC3Any f x
projectC3AnyInvariant f x =
  cong (λ o → f (Q.representative11 o))
    (Q.classify11CycleInvariant x)

projectS3AnyInvariant :
  ∀ {A : Set} (f : Q.Code27 → A)
  (p : Shape.TriPermutation) (x : Q.Code27) →
  projectS3Any f (Shape.conjugateCode p x) ≡
  projectS3Any f x
projectS3AnyInvariant f p x =
  cong (λ shape → f (Shape.shapeRepresentative shape))
    (Q.shapeClassInvariant p x)

projectS3AnyFixesInvariant :
  ∀ {A : Set} (f : Q.Code27 → A) →
  ((p : Shape.TriPermutation) (x : Q.Code27) →
    f (Shape.conjugateCode p x) ≡ f x) →
  (x : Q.Code27) → projectS3Any f x ≡ f x
projectS3AnyFixesInvariant f invariant x
  with Shape.canonicalOrbitWitness x
... | Shape.orbitWitness p eq =
  sym (trans (cong f eq)
    (invariant p (Shape.shapeRepresentative (Shape.shapeClass x))))

projectC3AnyAfterS3Any :
  ∀ {A : Set} (f : Q.Code27 → A) (x : Q.Code27) →
  projectC3Any (projectS3Any f) x ≡ projectS3Any f x
projectC3AnyAfterS3Any f x =
  cong (λ shape → f (Shape.shapeRepresentative shape))
    (trans (shapeOfRepresentative11 (Q.classify11 x))
      (sym (Q.classificationFactors x)))

projectS3AnyAfterC3Any :
  ∀ {A : Set} (f : Q.Code27 → A) (x : Q.Code27) →
  projectS3Any (projectC3Any f) x ≡ projectS3Any f x
projectS3AnyAfterC3Any f x =
  cong f (chosenSevenRepresentativeIsElevenRepresentative
    (Shape.shapeClass x))

-- Original trit-specific definitions remain the canonical public owners;
-- these equalities certify that the generic versions instantiate them.
projectC3AnyMatchesOriginal :
  (f : Q.Field27) (x : Q.Code27) →
  projectC3Any f x ≡ projectC3 f x
projectC3AnyMatchesOriginal f x = refl

projectS3AnyMatchesOriginal :
  (f : Q.Field27) (x : Q.Code27) →
  projectS3Any f x ≡ projectS3 f x
projectS3AnyMatchesOriginal f x = refl
