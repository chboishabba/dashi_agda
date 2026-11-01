-- MoonshineEarn: perf primes (7,11,23) earn moonshine (47,59,71)
-- via FRACTRAN fractions 47/23, 59/7, 71/11 in 3 steps.
module MoonshineEarn where

open import Data.Nat.Base using (_+_; _*_; _/_; _%_; NonZero; nonZero) renaming (ℕ to Nat)
open import Agda.Builtin.Equality

-- Perf counter primes
perf-product : 7 * 11 * 23 ≡ 1771
perf-product = refl

-- Moonshine kernel
moonshine-product : 47 * 59 * 71 ≡ 196883
moonshine-product = refl

-- Step 1: 47/23 fires on 1771
step1 : 1771 / 23 * 47 ≡ 3619
step1 = refl

-- Step 2: 59/7 fires on 3619
step2 : 3619 / 7 * 59 ≡ 30503
step2 = refl

-- Step 3: 71/11 fires on 30503
step3 : 30503 / 11 * 71 ≡ 196883
step3 = refl

-- Full chain
chain : (((7 * 11 * 23) / 23 * 47) / 7 * 59) / 11 * 71 ≡ 196883
chain = refl

-- Observer
observer : 47 * 59 * 71 + 1 ≡ 196884
observer = refl

-- Earned primes: 196884 mod {47,59,71} = 1
res47 : 196884 % 47 ≡ 1
res47 = refl

res59 : 196884 % 59 ≡ 1
res59 = refl

res71 : 196884 % 71 ≡ 1
res71 = refl

-- Full perf state preserved
full-earn : (((4 * 27 * 7 * 11 * 23) / 23 * 47) / 7 * 59) / 11 * 71 ≡ 4 * 27 * 47 * 59 * 71
full-earn = refl
