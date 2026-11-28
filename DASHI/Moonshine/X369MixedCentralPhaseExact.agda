module DASHI.Moonshine.X369MixedCentralPhaseExact where

-- Constructive CRT on phase coordinates, classical mathematics.
-- DASHI source weld: retain both local central phases. Not a group
-- identification of different prime-power extraspecial groups.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as Future

data B : Set where b0 b1 : B
data T : Set where t0 t1 t2 : T
data Six : Set where s0 s1 s2 s3 s4 s5 : Six

combine : B → T → Six
combine b0 t0 = s0
combine b0 t1 = s4
combine b0 t2 = s2
combine b1 t0 = s3
combine b1 t1 = s1
combine b1 t2 = s5

binary : Six → B
binary s0 = b0
binary s1 = b1
binary s2 = b0
binary s3 = b1
binary s4 = b0
binary s5 = b1

ternary : Six → T
ternary s0 = t0
ternary s1 = t1
ternary s2 = t2
ternary s3 = t0
ternary s4 = t1
ternary s5 = t2

addB : B → B → B
addB b0 b0 = b0
addB b0 b1 = b1
addB b1 b0 = b1
addB b1 b1 = b0

mulB : B → B → B
mulB b0 b0 = b0
mulB b0 b1 = b0
mulB b1 b0 = b0
mulB b1 b1 = b1

addT : T → T → T
addT t0 t0 = t0
addT t0 t1 = t1
addT t0 t2 = t2
addT t1 t0 = t1
addT t1 t1 = t2
addT t1 t2 = t0
addT t2 t0 = t2
addT t2 t1 = t0
addT t2 t2 = t1

mulT : T → T → T
mulT t0 t0 = t0
mulT t0 t1 = t0
mulT t0 t2 = t0
mulT t1 t0 = t0
mulT t1 t1 = t1
mulT t1 t2 = t2
mulT t2 t0 = t0
mulT t2 t1 = t2
mulT t2 t2 = t1

add6 : Six → Six → Six
add6 s0 s0 = s0
add6 s0 s1 = s1
add6 s0 s2 = s2
add6 s0 s3 = s3
add6 s0 s4 = s4
add6 s0 s5 = s5
add6 s1 s0 = s1
add6 s1 s1 = s2
add6 s1 s2 = s3
add6 s1 s3 = s4
add6 s1 s4 = s5
add6 s1 s5 = s0
add6 s2 s0 = s2
add6 s2 s1 = s3
add6 s2 s2 = s4
add6 s2 s3 = s5
add6 s2 s4 = s0
add6 s2 s5 = s1
add6 s3 s0 = s3
add6 s3 s1 = s4
add6 s3 s2 = s5
add6 s3 s3 = s0
add6 s3 s4 = s1
add6 s3 s5 = s2
add6 s4 s0 = s4
add6 s4 s1 = s5
add6 s4 s2 = s0
add6 s4 s3 = s1
add6 s4 s4 = s2
add6 s4 s5 = s3
add6 s5 s0 = s5
add6 s5 s1 = s0
add6 s5 s2 = s1
add6 s5 s3 = s2
add6 s5 s4 = s3
add6 s5 s5 = s4

mul6 : Six → Six → Six
mul6 s0 s0 = s0
mul6 s0 s1 = s0
mul6 s0 s2 = s0
mul6 s0 s3 = s0
mul6 s0 s4 = s0
mul6 s0 s5 = s0
mul6 s1 s0 = s0
mul6 s1 s1 = s1
mul6 s1 s2 = s2
mul6 s1 s3 = s3
mul6 s1 s4 = s4
mul6 s1 s5 = s5
mul6 s2 s0 = s0
mul6 s2 s1 = s2
mul6 s2 s2 = s4
mul6 s2 s3 = s0
mul6 s2 s4 = s2
mul6 s2 s5 = s4
mul6 s3 s0 = s0
mul6 s3 s1 = s3
mul6 s3 s2 = s0
mul6 s3 s3 = s3
mul6 s3 s4 = s0
mul6 s3 s5 = s3
mul6 s4 s0 = s0
mul6 s4 s1 = s4
mul6 s4 s2 = s2
mul6 s4 s3 = s0
mul6 s4 s4 = s4
mul6 s4 s5 = s2
mul6 s5 s0 = s0
mul6 s5 s1 = s5
mul6 s5 s2 = s4
mul6 s5 s3 = s3
mul6 s5 s4 = s2
mul6 s5 s5 = s1

phaseReopens : (x : Six) → combine (binary x) (ternary x) ≡ x
phaseReopens s0 = refl
phaseReopens s1 = refl
phaseReopens s2 = refl
phaseReopens s3 = refl
phaseReopens s4 = refl
phaseReopens s5 = refl

binaryReopens : (b : B) (t : T) → binary (combine b t) ≡ b
binaryReopens b0 t0 = refl
binaryReopens b0 t1 = refl
binaryReopens b0 t2 = refl
binaryReopens b1 t0 = refl
binaryReopens b1 t1 = refl
binaryReopens b1 t2 = refl

ternaryReopens : (b : B) (t : T) → ternary (combine b t) ≡ t
ternaryReopens b0 t0 = refl
ternaryReopens b0 t1 = refl
ternaryReopens b0 t2 = refl
ternaryReopens b1 t0 = refl
ternaryReopens b1 t1 = refl
ternaryReopens b1 t2 = refl

binaryAdd : (x y : Six) → binary (add6 x y) ≡ addB (binary x) (binary y)
binaryAdd s0 s0 = refl
binaryAdd s0 s1 = refl
binaryAdd s0 s2 = refl
binaryAdd s0 s3 = refl
binaryAdd s0 s4 = refl
binaryAdd s0 s5 = refl
binaryAdd s1 s0 = refl
binaryAdd s1 s1 = refl
binaryAdd s1 s2 = refl
binaryAdd s1 s3 = refl
binaryAdd s1 s4 = refl
binaryAdd s1 s5 = refl
binaryAdd s2 s0 = refl
binaryAdd s2 s1 = refl
binaryAdd s2 s2 = refl
binaryAdd s2 s3 = refl
binaryAdd s2 s4 = refl
binaryAdd s2 s5 = refl
binaryAdd s3 s0 = refl
binaryAdd s3 s1 = refl
binaryAdd s3 s2 = refl
binaryAdd s3 s3 = refl
binaryAdd s3 s4 = refl
binaryAdd s3 s5 = refl
binaryAdd s4 s0 = refl
binaryAdd s4 s1 = refl
binaryAdd s4 s2 = refl
binaryAdd s4 s3 = refl
binaryAdd s4 s4 = refl
binaryAdd s4 s5 = refl
binaryAdd s5 s0 = refl
binaryAdd s5 s1 = refl
binaryAdd s5 s2 = refl
binaryAdd s5 s3 = refl
binaryAdd s5 s4 = refl
binaryAdd s5 s5 = refl

ternaryAdd : (x y : Six) → ternary (add6 x y) ≡ addT (ternary x) (ternary y)
ternaryAdd s0 s0 = refl
ternaryAdd s0 s1 = refl
ternaryAdd s0 s2 = refl
ternaryAdd s0 s3 = refl
ternaryAdd s0 s4 = refl
ternaryAdd s0 s5 = refl
ternaryAdd s1 s0 = refl
ternaryAdd s1 s1 = refl
ternaryAdd s1 s2 = refl
ternaryAdd s1 s3 = refl
ternaryAdd s1 s4 = refl
ternaryAdd s1 s5 = refl
ternaryAdd s2 s0 = refl
ternaryAdd s2 s1 = refl
ternaryAdd s2 s2 = refl
ternaryAdd s2 s3 = refl
ternaryAdd s2 s4 = refl
ternaryAdd s2 s5 = refl
ternaryAdd s3 s0 = refl
ternaryAdd s3 s1 = refl
ternaryAdd s3 s2 = refl
ternaryAdd s3 s3 = refl
ternaryAdd s3 s4 = refl
ternaryAdd s3 s5 = refl
ternaryAdd s4 s0 = refl
ternaryAdd s4 s1 = refl
ternaryAdd s4 s2 = refl
ternaryAdd s4 s3 = refl
ternaryAdd s4 s4 = refl
ternaryAdd s4 s5 = refl
ternaryAdd s5 s0 = refl
ternaryAdd s5 s1 = refl
ternaryAdd s5 s2 = refl
ternaryAdd s5 s3 = refl
ternaryAdd s5 s4 = refl
ternaryAdd s5 s5 = refl

binaryMul : (x y : Six) → binary (mul6 x y) ≡ mulB (binary x) (binary y)
binaryMul s0 s0 = refl
binaryMul s0 s1 = refl
binaryMul s0 s2 = refl
binaryMul s0 s3 = refl
binaryMul s0 s4 = refl
binaryMul s0 s5 = refl
binaryMul s1 s0 = refl
binaryMul s1 s1 = refl
binaryMul s1 s2 = refl
binaryMul s1 s3 = refl
binaryMul s1 s4 = refl
binaryMul s1 s5 = refl
binaryMul s2 s0 = refl
binaryMul s2 s1 = refl
binaryMul s2 s2 = refl
binaryMul s2 s3 = refl
binaryMul s2 s4 = refl
binaryMul s2 s5 = refl
binaryMul s3 s0 = refl
binaryMul s3 s1 = refl
binaryMul s3 s2 = refl
binaryMul s3 s3 = refl
binaryMul s3 s4 = refl
binaryMul s3 s5 = refl
binaryMul s4 s0 = refl
binaryMul s4 s1 = refl
binaryMul s4 s2 = refl
binaryMul s4 s3 = refl
binaryMul s4 s4 = refl
binaryMul s4 s5 = refl
binaryMul s5 s0 = refl
binaryMul s5 s1 = refl
binaryMul s5 s2 = refl
binaryMul s5 s3 = refl
binaryMul s5 s4 = refl
binaryMul s5 s5 = refl

ternaryMul : (x y : Six) → ternary (mul6 x y) ≡ mulT (ternary x) (ternary y)
ternaryMul s0 s0 = refl
ternaryMul s0 s1 = refl
ternaryMul s0 s2 = refl
ternaryMul s0 s3 = refl
ternaryMul s0 s4 = refl
ternaryMul s0 s5 = refl
ternaryMul s1 s0 = refl
ternaryMul s1 s1 = refl
ternaryMul s1 s2 = refl
ternaryMul s1 s3 = refl
ternaryMul s1 s4 = refl
ternaryMul s1 s5 = refl
ternaryMul s2 s0 = refl
ternaryMul s2 s1 = refl
ternaryMul s2 s2 = refl
ternaryMul s2 s3 = refl
ternaryMul s2 s4 = refl
ternaryMul s2 s5 = refl
ternaryMul s3 s0 = refl
ternaryMul s3 s1 = refl
ternaryMul s3 s2 = refl
ternaryMul s3 s3 = refl
ternaryMul s3 s4 = refl
ternaryMul s3 s5 = refl
ternaryMul s4 s0 = refl
ternaryMul s4 s1 = refl
ternaryMul s4 s2 = refl
ternaryMul s4 s3 = refl
ternaryMul s4 s4 = refl
ternaryMul s4 s5 = refl
ternaryMul s5 s0 = refl
ternaryMul s5 s1 = refl
ternaryMul s5 s2 = refl
ternaryMul s5 s3 = refl
ternaryMul s5 s4 = refl
ternaryMul s5 s5 = refl

-- One shared Heisenberg pair. Full six-pair phase is the sum of
-- these terms, plus the six retained binary-only terms.
mixedCentral : Six → Six → Six → Six → Six
mixedCentral z w a d = add6 (add6 z w) (mul6 a d)

binaryCentral : (z w a d : Six) →
  binary (mixedCentral z w a d) ≡
  addB (addB (binary z) (binary w)) (mulB (binary a) (binary d))
binaryCentral z w a d
  rewrite binaryAdd (add6 z w) (mul6 a d)
        | binaryAdd z w | binaryMul a d = refl

ternaryCentral : (z w a d : Six) →
  ternary (mixedCentral z w a d) ≡
  addT (addT (ternary z) (ternary w)) (mulT (ternary a) (ternary d))
ternaryCentral z w a d
  rewrite ternaryAdd (add6 z w) (mul6 a d)
        | ternaryAdd z w | ternaryMul a d = refl

binaryOnlyPhase : B → Six
binaryOnlyPhase x = combine x t0

binaryOnlyPreserved : (x : B) → binary (binaryOnlyPhase x) ≡ x
binaryOnlyPreserved x = binaryReopens x t0

binaryOnlyTernaryInvisible : (x : B) → ternary (binaryOnlyPhase x) ≡ t0
binaryOnlyTernaryInvisible x = ternaryReopens x t0
