module DASHI.Foundations.PolynomialC3S3OrbitFieldVectorAtlasExact where

-- Finite-source, lossless code charts for ternary orbit fields.
-- 7 = S3 shapes; 11 = C3 conjugacy orbits; 27 = unary trit maps.
-- The vector is a specified choice of ordering of the orbit classes.
-- It is NOT an S3-invariant canonical ordering or Monster identity.
-- Prior owners: RecursiveFibreTower, seven-shape conjugacy, 27 quotient.
-- New pointwise inverse proofs are source-written; kernel pending.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base using (Vec; []; _∷_)
import Data.Vec.Base as Vec
import Data.Fin.Base as Fin
import Base369 as Base
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape
import DASHI.Foundations.PolynomialC3S3TwentySevenOrbitQuotientExact as Q

index7 : Shape.ShapeOrbit7 → Fin.Fin 7
index7 Shape.identityShape =  Fin.zero
index7 Shape.threeCycleShape = Fin.suc (Fin.zero)
index7 Shape.transpositionShape = Fin.suc (Fin.suc (Fin.zero))
index7 Shape.constantShape = Fin.suc (Fin.suc (Fin.suc (Fin.zero)))
index7 Shape.rank2OneFixedShape = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))
index7 Shape.rank2TwoFixedShape = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))
index7 Shape.rank2TwoCycleShape = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))

index11 : Q.Orbit11 → Fin.Fin 11
index11 Q.identityOrbit =  Fin.zero
index11 Q.cycleForwardOrbit = Fin.suc (Fin.zero)
index11 Q.cycleBackwardOrbit = Fin.suc (Fin.suc (Fin.zero))
index11 Q.transpositionOrbit = Fin.suc (Fin.suc (Fin.suc (Fin.zero)))
index11 Q.constantOrbit = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))
index11 Q.rank2OneFixedA = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))
index11 Q.rank2OneFixedB = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))
index11 Q.rank2TwoFixedA = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))
index11 Q.rank2TwoFixedB = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))
index11 Q.rank2TwoCycleA = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))
index11 Q.rank2TwoCycleB = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))

index27 : Q.Code27 → Fin.Fin 27
index27 (Base.tri-low , (Base.tri-low , Base.tri-low)) =  Fin.zero
index27 (Base.tri-low , (Base.tri-low , Base.tri-mid)) = Fin.suc (Fin.zero)
index27 (Base.tri-low , (Base.tri-low , Base.tri-high)) = Fin.suc (Fin.suc (Fin.zero))
index27 (Base.tri-low , (Base.tri-mid , Base.tri-low)) = Fin.suc (Fin.suc (Fin.suc (Fin.zero)))
index27 (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))
index27 (Base.tri-low , (Base.tri-mid , Base.tri-high)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))
index27 (Base.tri-low , (Base.tri-high , Base.tri-low)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))
index27 (Base.tri-low , (Base.tri-high , Base.tri-mid)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))
index27 (Base.tri-low , (Base.tri-high , Base.tri-high)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))
index27 (Base.tri-mid , (Base.tri-low , Base.tri-low)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))
index27 (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))
index27 (Base.tri-mid , (Base.tri-low , Base.tri-high)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))
index27 (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))
index27 (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))
index27 (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))
index27 (Base.tri-mid , (Base.tri-high , Base.tri-low)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))
index27 (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))
index27 (Base.tri-mid , (Base.tri-high , Base.tri-high)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))
index27 (Base.tri-high , (Base.tri-low , Base.tri-low)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))
index27 (Base.tri-high , (Base.tri-low , Base.tri-mid)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))
index27 (Base.tri-high , (Base.tri-low , Base.tri-high)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))))
index27 (Base.tri-high , (Base.tri-mid , Base.tri-low)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))))
index27 (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))))))
index27 (Base.tri-high , (Base.tri-mid , Base.tri-high)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))))))
index27 (Base.tri-high , (Base.tri-high , Base.tri-low)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))))))))
index27 (Base.tri-high , (Base.tri-high , Base.tri-mid)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))))))))
index27 (Base.tri-high , (Base.tri-high , Base.tri-high)) = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))))))))))

encode7 : Q.Field7 → Vec Base.TriTruth 7
encode7 f = f Shape.identityShape ∷ f Shape.threeCycleShape ∷ f Shape.transpositionShape ∷ f Shape.constantShape ∷ f Shape.rank2OneFixedShape ∷ f Shape.rank2TwoFixedShape ∷ f Shape.rank2TwoCycleShape ∷ []

decode7 : Vec Base.TriTruth 7 → Q.Field7
decode7 values s = Vec.lookup values (index7 s)

encode11 : Q.Field11 → Vec Base.TriTruth 11
encode11 f = f Q.identityOrbit ∷ f Q.cycleForwardOrbit ∷ f Q.cycleBackwardOrbit ∷ f Q.transpositionOrbit ∷ f Q.constantOrbit ∷ f Q.rank2OneFixedA ∷ f Q.rank2OneFixedB ∷ f Q.rank2TwoFixedA ∷ f Q.rank2TwoFixedB ∷ f Q.rank2TwoCycleA ∷ f Q.rank2TwoCycleB ∷ []

decode11 : Vec Base.TriTruth 11 → Q.Field11
decode11 values o = Vec.lookup values (index11 o)

encode27 : Q.Field27 → Vec Base.TriTruth 27
encode27 f = f (Base.tri-low , (Base.tri-low , Base.tri-low)) ∷
  f (Base.tri-low , (Base.tri-low , Base.tri-mid)) ∷
  f (Base.tri-low , (Base.tri-low , Base.tri-high)) ∷
  f (Base.tri-low , (Base.tri-mid , Base.tri-low)) ∷
  f (Base.tri-low , (Base.tri-mid , Base.tri-mid)) ∷
  f (Base.tri-low , (Base.tri-mid , Base.tri-high)) ∷
  f (Base.tri-low , (Base.tri-high , Base.tri-low)) ∷
  f (Base.tri-low , (Base.tri-high , Base.tri-mid)) ∷
  f (Base.tri-low , (Base.tri-high , Base.tri-high)) ∷
  f (Base.tri-mid , (Base.tri-low , Base.tri-low)) ∷
  f (Base.tri-mid , (Base.tri-low , Base.tri-mid)) ∷
  f (Base.tri-mid , (Base.tri-low , Base.tri-high)) ∷
  f (Base.tri-mid , (Base.tri-mid , Base.tri-low)) ∷
  f (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) ∷
  f (Base.tri-mid , (Base.tri-mid , Base.tri-high)) ∷
  f (Base.tri-mid , (Base.tri-high , Base.tri-low)) ∷
  f (Base.tri-mid , (Base.tri-high , Base.tri-mid)) ∷
  f (Base.tri-mid , (Base.tri-high , Base.tri-high)) ∷
  f (Base.tri-high , (Base.tri-low , Base.tri-low)) ∷
  f (Base.tri-high , (Base.tri-low , Base.tri-mid)) ∷
  f (Base.tri-high , (Base.tri-low , Base.tri-high)) ∷
  f (Base.tri-high , (Base.tri-mid , Base.tri-low)) ∷
  f (Base.tri-high , (Base.tri-mid , Base.tri-mid)) ∷
  f (Base.tri-high , (Base.tri-mid , Base.tri-high)) ∷
  f (Base.tri-high , (Base.tri-high , Base.tri-low)) ∷
  f (Base.tri-high , (Base.tri-high , Base.tri-mid)) ∷
  f (Base.tri-high , (Base.tri-high , Base.tri-high)) ∷ []

decode27 : Vec Base.TriTruth 27 → Q.Field27
decode27 values x = Vec.lookup values (index27 x)

decodeEncode7Pointwise :
  (f : Q.Field7) (s : Shape.ShapeOrbit7) →
  decode7 (encode7 f) s ≡ f s
decodeEncode7Pointwise f Shape.identityShape = refl
decodeEncode7Pointwise f Shape.threeCycleShape = refl
decodeEncode7Pointwise f Shape.transpositionShape = refl
decodeEncode7Pointwise f Shape.constantShape = refl
decodeEncode7Pointwise f Shape.rank2OneFixedShape = refl
decodeEncode7Pointwise f Shape.rank2TwoFixedShape = refl
decodeEncode7Pointwise f Shape.rank2TwoCycleShape = refl

decodeEncode11Pointwise :
  (f : Q.Field11) (o : Q.Orbit11) →
  decode11 (encode11 f) o ≡ f o
decodeEncode11Pointwise f Q.identityOrbit = refl
decodeEncode11Pointwise f Q.cycleForwardOrbit = refl
decodeEncode11Pointwise f Q.cycleBackwardOrbit = refl
decodeEncode11Pointwise f Q.transpositionOrbit = refl
decodeEncode11Pointwise f Q.constantOrbit = refl
decodeEncode11Pointwise f Q.rank2OneFixedA = refl
decodeEncode11Pointwise f Q.rank2OneFixedB = refl
decodeEncode11Pointwise f Q.rank2TwoFixedA = refl
decodeEncode11Pointwise f Q.rank2TwoFixedB = refl
decodeEncode11Pointwise f Q.rank2TwoCycleA = refl
decodeEncode11Pointwise f Q.rank2TwoCycleB = refl

decodeEncode27Pointwise :
  (f : Q.Field27) (x : Q.Code27) →
  decode27 (encode27 f) x ≡ f x
decodeEncode27Pointwise f (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
decodeEncode27Pointwise f (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
decodeEncode27Pointwise f (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
decodeEncode27Pointwise f (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
decodeEncode27Pointwise f (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
decodeEncode27Pointwise f (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
decodeEncode27Pointwise f (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
decodeEncode27Pointwise f (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
decodeEncode27Pointwise f (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
decodeEncode27Pointwise f (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
decodeEncode27Pointwise f (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
decodeEncode27Pointwise f (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
decodeEncode27Pointwise f (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
decodeEncode27Pointwise f (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
decodeEncode27Pointwise f (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
decodeEncode27Pointwise f (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
decodeEncode27Pointwise f (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
decodeEncode27Pointwise f (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
decodeEncode27Pointwise f (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
decodeEncode27Pointwise f (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
decodeEncode27Pointwise f (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
decodeEncode27Pointwise f (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
decodeEncode27Pointwise f (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
decodeEncode27Pointwise f (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
decodeEncode27Pointwise f (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
decodeEncode27Pointwise f (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
decodeEncode27Pointwise f (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl

encodeDecode7 :
  (v : Vec Base.TriTruth 7) → encode7 (decode7 v) ≡ v
encodeDecode7 (v0 ∷ v1 ∷ v2 ∷ v3 ∷ v4 ∷ v5 ∷ v6 ∷ []) = refl

encodeDecode11 :
  (v : Vec Base.TriTruth 11) → encode11 (decode11 v) ≡ v
encodeDecode11 (v0 ∷ v1 ∷ v2 ∷ v3 ∷ v4 ∷ v5 ∷ v6 ∷ v7 ∷ v8 ∷ v9 ∷ v10 ∷ []) = refl

encodeDecode27 :
  (v : Vec Base.TriTruth 27) → encode27 (decode27 v) ≡ v
encodeDecode27 (v0 ∷ v1 ∷ v2 ∷ v3 ∷ v4 ∷ v5 ∷ v6 ∷ v7 ∷ v8 ∷ v9 ∷ v10 ∷ v11 ∷ v12 ∷ v13 ∷ v14 ∷ v15 ∷ v16 ∷ v17 ∷ v18 ∷ v19 ∷ v20 ∷ v21 ∷ v22 ∷ v23 ∷ v24 ∷ v25 ∷ v26 ∷ []) = refl

-- Actual carrier charts above justify applying the standard
-- |Vec T n|=|T|^n count. Numeric normalization is independent:
sevenFieldsAre2187 : Tower.pow 3 7 ≡ 2187
sevenFieldsAre2187 = refl

elevenFieldsAre177147 : Tower.pow 3 11 ≡ 177147
elevenFieldsAre177147 = refl

twentySevenFieldsAre7625597484987 :
  Tower.pow 3 27 ≡ 7625597484987
twentySevenFieldsAre7625597484987 = refl

-- All three are bijections up to pointwise equality (no funext axiom).
-- The enumerated orbit order is an explicit CHOICE of a basis.
