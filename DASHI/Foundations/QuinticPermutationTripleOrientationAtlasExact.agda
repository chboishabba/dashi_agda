module DASHI.Foundations.QuinticPermutationTripleOrientationAtlasExact where

------------------------------------------------------------------------
-- EXPLICIT FINITE 120 = 60 x 2 CHART OVER THE ORDERED 5-ROOT CARRIER.
--
-- Classical S5/A5 combinatorics (Galois/Jordan; Dixon--Mortimer).
-- Every ordered injective triple from five root labels has exactly two
-- completions to a full five-permutation. Exactly ONE of the two
-- completions is EVEN. Hence the 60 even permutations biject with
-- the 5*4*3 = 60 ordered distinct triples, by their first three images.
--
-- Full 120-case and 60-case literal tables. Constructor elimination proves
-- both round trips. This is a CARRIER bijection and an action chart; it is
-- NOT a group isomorphism to a 60-state cyclic group, nor a Galois theorem.
-- The parity labels arise from the exact inversion-count permutation parity.
--
-- Source-written / Agda kernel pending. Source generator and independent
-- finite Python regression are not substitutes for actual Agda type check.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Empty using (⊥)

data Point5 : Set where
  point0 point1 point2 point3 point4 : Point5

data Permutation5 : Set where
  perm01234
    perm01243
    perm01324
    perm01342
    perm01423
    perm01432
    perm02134
    perm02143
    perm02314
    perm02341
    perm02413
    perm02431
    perm03124
    perm03142
    perm03214
    perm03241
    perm03412
    perm03421
    perm04123
    perm04132
    perm04213
    perm04231
    perm04312
    perm04321
    perm10234
    perm10243
    perm10324
    perm10342
    perm10423
    perm10432
    perm12034
    perm12043
    perm12304
    perm12340
    perm12403
    perm12430
    perm13024
    perm13042
    perm13204
    perm13240
    perm13402
    perm13420
    perm14023
    perm14032
    perm14203
    perm14230
    perm14302
    perm14320
    perm20134
    perm20143
    perm20314
    perm20341
    perm20413
    perm20431
    perm21034
    perm21043
    perm21304
    perm21340
    perm21403
    perm21430
    perm23014
    perm23041
    perm23104
    perm23140
    perm23401
    perm23410
    perm24013
    perm24031
    perm24103
    perm24130
    perm24301
    perm24310
    perm30124
    perm30142
    perm30214
    perm30241
    perm30412
    perm30421
    perm31024
    perm31042
    perm31204
    perm31240
    perm31402
    perm31420
    perm32014
    perm32041
    perm32104
    perm32140
    perm32401
    perm32410
    perm34012
    perm34021
    perm34102
    perm34120
    perm34201
    perm34210
    perm40123
    perm40132
    perm40213
    perm40231
    perm40312
    perm40321
    perm41023
    perm41032
    perm41203
    perm41230
    perm41302
    perm41320
    perm42013
    perm42031
    perm42103
    perm42130
    perm42301
    perm42310
    perm43012
    perm43021
    perm43102
    perm43120
    perm43201
    perm43210 : Permutation5

data DistinctTriple5 : Set where
  triple012
    triple013
    triple014
    triple021
    triple023
    triple024
    triple031
    triple032
    triple034
    triple041
    triple042
    triple043
    triple102
    triple103
    triple104
    triple120
    triple123
    triple124
    triple130
    triple132
    triple134
    triple140
    triple142
    triple143
    triple201
    triple203
    triple204
    triple210
    triple213
    triple214
    triple230
    triple231
    triple234
    triple240
    triple241
    triple243
    triple301
    triple302
    triple304
    triple310
    triple312
    triple314
    triple320
    triple321
    triple324
    triple340
    triple341
    triple342
    triple401
    triple402
    triple403
    triple410
    triple412
    triple413
    triple420
    triple421
    triple423
    triple430
    triple431
    triple432 : DistinctTriple5

data Orientation2 : Set where
  evenChoice oddChoice : Orientation2

-- Actual permutation images, not an unexplained 120-label bijection.
applyPermutation5 : Permutation5 → Point5 → Point5
applyPermutation5 perm01234 point0 = point0
applyPermutation5 perm01234 point1 = point1
applyPermutation5 perm01234 point2 = point2
applyPermutation5 perm01234 point3 = point3
applyPermutation5 perm01234 point4 = point4
applyPermutation5 perm01243 point0 = point0
applyPermutation5 perm01243 point1 = point1
applyPermutation5 perm01243 point2 = point2
applyPermutation5 perm01243 point3 = point4
applyPermutation5 perm01243 point4 = point3
applyPermutation5 perm01324 point0 = point0
applyPermutation5 perm01324 point1 = point1
applyPermutation5 perm01324 point2 = point3
applyPermutation5 perm01324 point3 = point2
applyPermutation5 perm01324 point4 = point4
applyPermutation5 perm01342 point0 = point0
applyPermutation5 perm01342 point1 = point1
applyPermutation5 perm01342 point2 = point3
applyPermutation5 perm01342 point3 = point4
applyPermutation5 perm01342 point4 = point2
applyPermutation5 perm01423 point0 = point0
applyPermutation5 perm01423 point1 = point1
applyPermutation5 perm01423 point2 = point4
applyPermutation5 perm01423 point3 = point2
applyPermutation5 perm01423 point4 = point3
applyPermutation5 perm01432 point0 = point0
applyPermutation5 perm01432 point1 = point1
applyPermutation5 perm01432 point2 = point4
applyPermutation5 perm01432 point3 = point3
applyPermutation5 perm01432 point4 = point2
applyPermutation5 perm02134 point0 = point0
applyPermutation5 perm02134 point1 = point2
applyPermutation5 perm02134 point2 = point1
applyPermutation5 perm02134 point3 = point3
applyPermutation5 perm02134 point4 = point4
applyPermutation5 perm02143 point0 = point0
applyPermutation5 perm02143 point1 = point2
applyPermutation5 perm02143 point2 = point1
applyPermutation5 perm02143 point3 = point4
applyPermutation5 perm02143 point4 = point3
applyPermutation5 perm02314 point0 = point0
applyPermutation5 perm02314 point1 = point2
applyPermutation5 perm02314 point2 = point3
applyPermutation5 perm02314 point3 = point1
applyPermutation5 perm02314 point4 = point4
applyPermutation5 perm02341 point0 = point0
applyPermutation5 perm02341 point1 = point2
applyPermutation5 perm02341 point2 = point3
applyPermutation5 perm02341 point3 = point4
applyPermutation5 perm02341 point4 = point1
applyPermutation5 perm02413 point0 = point0
applyPermutation5 perm02413 point1 = point2
applyPermutation5 perm02413 point2 = point4
applyPermutation5 perm02413 point3 = point1
applyPermutation5 perm02413 point4 = point3
applyPermutation5 perm02431 point0 = point0
applyPermutation5 perm02431 point1 = point2
applyPermutation5 perm02431 point2 = point4
applyPermutation5 perm02431 point3 = point3
applyPermutation5 perm02431 point4 = point1
applyPermutation5 perm03124 point0 = point0
applyPermutation5 perm03124 point1 = point3
applyPermutation5 perm03124 point2 = point1
applyPermutation5 perm03124 point3 = point2
applyPermutation5 perm03124 point4 = point4
applyPermutation5 perm03142 point0 = point0
applyPermutation5 perm03142 point1 = point3
applyPermutation5 perm03142 point2 = point1
applyPermutation5 perm03142 point3 = point4
applyPermutation5 perm03142 point4 = point2
applyPermutation5 perm03214 point0 = point0
applyPermutation5 perm03214 point1 = point3
applyPermutation5 perm03214 point2 = point2
applyPermutation5 perm03214 point3 = point1
applyPermutation5 perm03214 point4 = point4
applyPermutation5 perm03241 point0 = point0
applyPermutation5 perm03241 point1 = point3
applyPermutation5 perm03241 point2 = point2
applyPermutation5 perm03241 point3 = point4
applyPermutation5 perm03241 point4 = point1
applyPermutation5 perm03412 point0 = point0
applyPermutation5 perm03412 point1 = point3
applyPermutation5 perm03412 point2 = point4
applyPermutation5 perm03412 point3 = point1
applyPermutation5 perm03412 point4 = point2
applyPermutation5 perm03421 point0 = point0
applyPermutation5 perm03421 point1 = point3
applyPermutation5 perm03421 point2 = point4
applyPermutation5 perm03421 point3 = point2
applyPermutation5 perm03421 point4 = point1
applyPermutation5 perm04123 point0 = point0
applyPermutation5 perm04123 point1 = point4
applyPermutation5 perm04123 point2 = point1
applyPermutation5 perm04123 point3 = point2
applyPermutation5 perm04123 point4 = point3
applyPermutation5 perm04132 point0 = point0
applyPermutation5 perm04132 point1 = point4
applyPermutation5 perm04132 point2 = point1
applyPermutation5 perm04132 point3 = point3
applyPermutation5 perm04132 point4 = point2
applyPermutation5 perm04213 point0 = point0
applyPermutation5 perm04213 point1 = point4
applyPermutation5 perm04213 point2 = point2
applyPermutation5 perm04213 point3 = point1
applyPermutation5 perm04213 point4 = point3
applyPermutation5 perm04231 point0 = point0
applyPermutation5 perm04231 point1 = point4
applyPermutation5 perm04231 point2 = point2
applyPermutation5 perm04231 point3 = point3
applyPermutation5 perm04231 point4 = point1
applyPermutation5 perm04312 point0 = point0
applyPermutation5 perm04312 point1 = point4
applyPermutation5 perm04312 point2 = point3
applyPermutation5 perm04312 point3 = point1
applyPermutation5 perm04312 point4 = point2
applyPermutation5 perm04321 point0 = point0
applyPermutation5 perm04321 point1 = point4
applyPermutation5 perm04321 point2 = point3
applyPermutation5 perm04321 point3 = point2
applyPermutation5 perm04321 point4 = point1
applyPermutation5 perm10234 point0 = point1
applyPermutation5 perm10234 point1 = point0
applyPermutation5 perm10234 point2 = point2
applyPermutation5 perm10234 point3 = point3
applyPermutation5 perm10234 point4 = point4
applyPermutation5 perm10243 point0 = point1
applyPermutation5 perm10243 point1 = point0
applyPermutation5 perm10243 point2 = point2
applyPermutation5 perm10243 point3 = point4
applyPermutation5 perm10243 point4 = point3
applyPermutation5 perm10324 point0 = point1
applyPermutation5 perm10324 point1 = point0
applyPermutation5 perm10324 point2 = point3
applyPermutation5 perm10324 point3 = point2
applyPermutation5 perm10324 point4 = point4
applyPermutation5 perm10342 point0 = point1
applyPermutation5 perm10342 point1 = point0
applyPermutation5 perm10342 point2 = point3
applyPermutation5 perm10342 point3 = point4
applyPermutation5 perm10342 point4 = point2
applyPermutation5 perm10423 point0 = point1
applyPermutation5 perm10423 point1 = point0
applyPermutation5 perm10423 point2 = point4
applyPermutation5 perm10423 point3 = point2
applyPermutation5 perm10423 point4 = point3
applyPermutation5 perm10432 point0 = point1
applyPermutation5 perm10432 point1 = point0
applyPermutation5 perm10432 point2 = point4
applyPermutation5 perm10432 point3 = point3
applyPermutation5 perm10432 point4 = point2
applyPermutation5 perm12034 point0 = point1
applyPermutation5 perm12034 point1 = point2
applyPermutation5 perm12034 point2 = point0
applyPermutation5 perm12034 point3 = point3
applyPermutation5 perm12034 point4 = point4
applyPermutation5 perm12043 point0 = point1
applyPermutation5 perm12043 point1 = point2
applyPermutation5 perm12043 point2 = point0
applyPermutation5 perm12043 point3 = point4
applyPermutation5 perm12043 point4 = point3
applyPermutation5 perm12304 point0 = point1
applyPermutation5 perm12304 point1 = point2
applyPermutation5 perm12304 point2 = point3
applyPermutation5 perm12304 point3 = point0
applyPermutation5 perm12304 point4 = point4
applyPermutation5 perm12340 point0 = point1
applyPermutation5 perm12340 point1 = point2
applyPermutation5 perm12340 point2 = point3
applyPermutation5 perm12340 point3 = point4
applyPermutation5 perm12340 point4 = point0
applyPermutation5 perm12403 point0 = point1
applyPermutation5 perm12403 point1 = point2
applyPermutation5 perm12403 point2 = point4
applyPermutation5 perm12403 point3 = point0
applyPermutation5 perm12403 point4 = point3
applyPermutation5 perm12430 point0 = point1
applyPermutation5 perm12430 point1 = point2
applyPermutation5 perm12430 point2 = point4
applyPermutation5 perm12430 point3 = point3
applyPermutation5 perm12430 point4 = point0
applyPermutation5 perm13024 point0 = point1
applyPermutation5 perm13024 point1 = point3
applyPermutation5 perm13024 point2 = point0
applyPermutation5 perm13024 point3 = point2
applyPermutation5 perm13024 point4 = point4
applyPermutation5 perm13042 point0 = point1
applyPermutation5 perm13042 point1 = point3
applyPermutation5 perm13042 point2 = point0
applyPermutation5 perm13042 point3 = point4
applyPermutation5 perm13042 point4 = point2
applyPermutation5 perm13204 point0 = point1
applyPermutation5 perm13204 point1 = point3
applyPermutation5 perm13204 point2 = point2
applyPermutation5 perm13204 point3 = point0
applyPermutation5 perm13204 point4 = point4
applyPermutation5 perm13240 point0 = point1
applyPermutation5 perm13240 point1 = point3
applyPermutation5 perm13240 point2 = point2
applyPermutation5 perm13240 point3 = point4
applyPermutation5 perm13240 point4 = point0
applyPermutation5 perm13402 point0 = point1
applyPermutation5 perm13402 point1 = point3
applyPermutation5 perm13402 point2 = point4
applyPermutation5 perm13402 point3 = point0
applyPermutation5 perm13402 point4 = point2
applyPermutation5 perm13420 point0 = point1
applyPermutation5 perm13420 point1 = point3
applyPermutation5 perm13420 point2 = point4
applyPermutation5 perm13420 point3 = point2
applyPermutation5 perm13420 point4 = point0
applyPermutation5 perm14023 point0 = point1
applyPermutation5 perm14023 point1 = point4
applyPermutation5 perm14023 point2 = point0
applyPermutation5 perm14023 point3 = point2
applyPermutation5 perm14023 point4 = point3
applyPermutation5 perm14032 point0 = point1
applyPermutation5 perm14032 point1 = point4
applyPermutation5 perm14032 point2 = point0
applyPermutation5 perm14032 point3 = point3
applyPermutation5 perm14032 point4 = point2
applyPermutation5 perm14203 point0 = point1
applyPermutation5 perm14203 point1 = point4
applyPermutation5 perm14203 point2 = point2
applyPermutation5 perm14203 point3 = point0
applyPermutation5 perm14203 point4 = point3
applyPermutation5 perm14230 point0 = point1
applyPermutation5 perm14230 point1 = point4
applyPermutation5 perm14230 point2 = point2
applyPermutation5 perm14230 point3 = point3
applyPermutation5 perm14230 point4 = point0
applyPermutation5 perm14302 point0 = point1
applyPermutation5 perm14302 point1 = point4
applyPermutation5 perm14302 point2 = point3
applyPermutation5 perm14302 point3 = point0
applyPermutation5 perm14302 point4 = point2
applyPermutation5 perm14320 point0 = point1
applyPermutation5 perm14320 point1 = point4
applyPermutation5 perm14320 point2 = point3
applyPermutation5 perm14320 point3 = point2
applyPermutation5 perm14320 point4 = point0
applyPermutation5 perm20134 point0 = point2
applyPermutation5 perm20134 point1 = point0
applyPermutation5 perm20134 point2 = point1
applyPermutation5 perm20134 point3 = point3
applyPermutation5 perm20134 point4 = point4
applyPermutation5 perm20143 point0 = point2
applyPermutation5 perm20143 point1 = point0
applyPermutation5 perm20143 point2 = point1
applyPermutation5 perm20143 point3 = point4
applyPermutation5 perm20143 point4 = point3
applyPermutation5 perm20314 point0 = point2
applyPermutation5 perm20314 point1 = point0
applyPermutation5 perm20314 point2 = point3
applyPermutation5 perm20314 point3 = point1
applyPermutation5 perm20314 point4 = point4
applyPermutation5 perm20341 point0 = point2
applyPermutation5 perm20341 point1 = point0
applyPermutation5 perm20341 point2 = point3
applyPermutation5 perm20341 point3 = point4
applyPermutation5 perm20341 point4 = point1
applyPermutation5 perm20413 point0 = point2
applyPermutation5 perm20413 point1 = point0
applyPermutation5 perm20413 point2 = point4
applyPermutation5 perm20413 point3 = point1
applyPermutation5 perm20413 point4 = point3
applyPermutation5 perm20431 point0 = point2
applyPermutation5 perm20431 point1 = point0
applyPermutation5 perm20431 point2 = point4
applyPermutation5 perm20431 point3 = point3
applyPermutation5 perm20431 point4 = point1
applyPermutation5 perm21034 point0 = point2
applyPermutation5 perm21034 point1 = point1
applyPermutation5 perm21034 point2 = point0
applyPermutation5 perm21034 point3 = point3
applyPermutation5 perm21034 point4 = point4
applyPermutation5 perm21043 point0 = point2
applyPermutation5 perm21043 point1 = point1
applyPermutation5 perm21043 point2 = point0
applyPermutation5 perm21043 point3 = point4
applyPermutation5 perm21043 point4 = point3
applyPermutation5 perm21304 point0 = point2
applyPermutation5 perm21304 point1 = point1
applyPermutation5 perm21304 point2 = point3
applyPermutation5 perm21304 point3 = point0
applyPermutation5 perm21304 point4 = point4
applyPermutation5 perm21340 point0 = point2
applyPermutation5 perm21340 point1 = point1
applyPermutation5 perm21340 point2 = point3
applyPermutation5 perm21340 point3 = point4
applyPermutation5 perm21340 point4 = point0
applyPermutation5 perm21403 point0 = point2
applyPermutation5 perm21403 point1 = point1
applyPermutation5 perm21403 point2 = point4
applyPermutation5 perm21403 point3 = point0
applyPermutation5 perm21403 point4 = point3
applyPermutation5 perm21430 point0 = point2
applyPermutation5 perm21430 point1 = point1
applyPermutation5 perm21430 point2 = point4
applyPermutation5 perm21430 point3 = point3
applyPermutation5 perm21430 point4 = point0
applyPermutation5 perm23014 point0 = point2
applyPermutation5 perm23014 point1 = point3
applyPermutation5 perm23014 point2 = point0
applyPermutation5 perm23014 point3 = point1
applyPermutation5 perm23014 point4 = point4
applyPermutation5 perm23041 point0 = point2
applyPermutation5 perm23041 point1 = point3
applyPermutation5 perm23041 point2 = point0
applyPermutation5 perm23041 point3 = point4
applyPermutation5 perm23041 point4 = point1
applyPermutation5 perm23104 point0 = point2
applyPermutation5 perm23104 point1 = point3
applyPermutation5 perm23104 point2 = point1
applyPermutation5 perm23104 point3 = point0
applyPermutation5 perm23104 point4 = point4
applyPermutation5 perm23140 point0 = point2
applyPermutation5 perm23140 point1 = point3
applyPermutation5 perm23140 point2 = point1
applyPermutation5 perm23140 point3 = point4
applyPermutation5 perm23140 point4 = point0
applyPermutation5 perm23401 point0 = point2
applyPermutation5 perm23401 point1 = point3
applyPermutation5 perm23401 point2 = point4
applyPermutation5 perm23401 point3 = point0
applyPermutation5 perm23401 point4 = point1
applyPermutation5 perm23410 point0 = point2
applyPermutation5 perm23410 point1 = point3
applyPermutation5 perm23410 point2 = point4
applyPermutation5 perm23410 point3 = point1
applyPermutation5 perm23410 point4 = point0
applyPermutation5 perm24013 point0 = point2
applyPermutation5 perm24013 point1 = point4
applyPermutation5 perm24013 point2 = point0
applyPermutation5 perm24013 point3 = point1
applyPermutation5 perm24013 point4 = point3
applyPermutation5 perm24031 point0 = point2
applyPermutation5 perm24031 point1 = point4
applyPermutation5 perm24031 point2 = point0
applyPermutation5 perm24031 point3 = point3
applyPermutation5 perm24031 point4 = point1
applyPermutation5 perm24103 point0 = point2
applyPermutation5 perm24103 point1 = point4
applyPermutation5 perm24103 point2 = point1
applyPermutation5 perm24103 point3 = point0
applyPermutation5 perm24103 point4 = point3
applyPermutation5 perm24130 point0 = point2
applyPermutation5 perm24130 point1 = point4
applyPermutation5 perm24130 point2 = point1
applyPermutation5 perm24130 point3 = point3
applyPermutation5 perm24130 point4 = point0
applyPermutation5 perm24301 point0 = point2
applyPermutation5 perm24301 point1 = point4
applyPermutation5 perm24301 point2 = point3
applyPermutation5 perm24301 point3 = point0
applyPermutation5 perm24301 point4 = point1
applyPermutation5 perm24310 point0 = point2
applyPermutation5 perm24310 point1 = point4
applyPermutation5 perm24310 point2 = point3
applyPermutation5 perm24310 point3 = point1
applyPermutation5 perm24310 point4 = point0
applyPermutation5 perm30124 point0 = point3
applyPermutation5 perm30124 point1 = point0
applyPermutation5 perm30124 point2 = point1
applyPermutation5 perm30124 point3 = point2
applyPermutation5 perm30124 point4 = point4
applyPermutation5 perm30142 point0 = point3
applyPermutation5 perm30142 point1 = point0
applyPermutation5 perm30142 point2 = point1
applyPermutation5 perm30142 point3 = point4
applyPermutation5 perm30142 point4 = point2
applyPermutation5 perm30214 point0 = point3
applyPermutation5 perm30214 point1 = point0
applyPermutation5 perm30214 point2 = point2
applyPermutation5 perm30214 point3 = point1
applyPermutation5 perm30214 point4 = point4
applyPermutation5 perm30241 point0 = point3
applyPermutation5 perm30241 point1 = point0
applyPermutation5 perm30241 point2 = point2
applyPermutation5 perm30241 point3 = point4
applyPermutation5 perm30241 point4 = point1
applyPermutation5 perm30412 point0 = point3
applyPermutation5 perm30412 point1 = point0
applyPermutation5 perm30412 point2 = point4
applyPermutation5 perm30412 point3 = point1
applyPermutation5 perm30412 point4 = point2
applyPermutation5 perm30421 point0 = point3
applyPermutation5 perm30421 point1 = point0
applyPermutation5 perm30421 point2 = point4
applyPermutation5 perm30421 point3 = point2
applyPermutation5 perm30421 point4 = point1
applyPermutation5 perm31024 point0 = point3
applyPermutation5 perm31024 point1 = point1
applyPermutation5 perm31024 point2 = point0
applyPermutation5 perm31024 point3 = point2
applyPermutation5 perm31024 point4 = point4
applyPermutation5 perm31042 point0 = point3
applyPermutation5 perm31042 point1 = point1
applyPermutation5 perm31042 point2 = point0
applyPermutation5 perm31042 point3 = point4
applyPermutation5 perm31042 point4 = point2
applyPermutation5 perm31204 point0 = point3
applyPermutation5 perm31204 point1 = point1
applyPermutation5 perm31204 point2 = point2
applyPermutation5 perm31204 point3 = point0
applyPermutation5 perm31204 point4 = point4
applyPermutation5 perm31240 point0 = point3
applyPermutation5 perm31240 point1 = point1
applyPermutation5 perm31240 point2 = point2
applyPermutation5 perm31240 point3 = point4
applyPermutation5 perm31240 point4 = point0
applyPermutation5 perm31402 point0 = point3
applyPermutation5 perm31402 point1 = point1
applyPermutation5 perm31402 point2 = point4
applyPermutation5 perm31402 point3 = point0
applyPermutation5 perm31402 point4 = point2
applyPermutation5 perm31420 point0 = point3
applyPermutation5 perm31420 point1 = point1
applyPermutation5 perm31420 point2 = point4
applyPermutation5 perm31420 point3 = point2
applyPermutation5 perm31420 point4 = point0
applyPermutation5 perm32014 point0 = point3
applyPermutation5 perm32014 point1 = point2
applyPermutation5 perm32014 point2 = point0
applyPermutation5 perm32014 point3 = point1
applyPermutation5 perm32014 point4 = point4
applyPermutation5 perm32041 point0 = point3
applyPermutation5 perm32041 point1 = point2
applyPermutation5 perm32041 point2 = point0
applyPermutation5 perm32041 point3 = point4
applyPermutation5 perm32041 point4 = point1
applyPermutation5 perm32104 point0 = point3
applyPermutation5 perm32104 point1 = point2
applyPermutation5 perm32104 point2 = point1
applyPermutation5 perm32104 point3 = point0
applyPermutation5 perm32104 point4 = point4
applyPermutation5 perm32140 point0 = point3
applyPermutation5 perm32140 point1 = point2
applyPermutation5 perm32140 point2 = point1
applyPermutation5 perm32140 point3 = point4
applyPermutation5 perm32140 point4 = point0
applyPermutation5 perm32401 point0 = point3
applyPermutation5 perm32401 point1 = point2
applyPermutation5 perm32401 point2 = point4
applyPermutation5 perm32401 point3 = point0
applyPermutation5 perm32401 point4 = point1
applyPermutation5 perm32410 point0 = point3
applyPermutation5 perm32410 point1 = point2
applyPermutation5 perm32410 point2 = point4
applyPermutation5 perm32410 point3 = point1
applyPermutation5 perm32410 point4 = point0
applyPermutation5 perm34012 point0 = point3
applyPermutation5 perm34012 point1 = point4
applyPermutation5 perm34012 point2 = point0
applyPermutation5 perm34012 point3 = point1
applyPermutation5 perm34012 point4 = point2
applyPermutation5 perm34021 point0 = point3
applyPermutation5 perm34021 point1 = point4
applyPermutation5 perm34021 point2 = point0
applyPermutation5 perm34021 point3 = point2
applyPermutation5 perm34021 point4 = point1
applyPermutation5 perm34102 point0 = point3
applyPermutation5 perm34102 point1 = point4
applyPermutation5 perm34102 point2 = point1
applyPermutation5 perm34102 point3 = point0
applyPermutation5 perm34102 point4 = point2
applyPermutation5 perm34120 point0 = point3
applyPermutation5 perm34120 point1 = point4
applyPermutation5 perm34120 point2 = point1
applyPermutation5 perm34120 point3 = point2
applyPermutation5 perm34120 point4 = point0
applyPermutation5 perm34201 point0 = point3
applyPermutation5 perm34201 point1 = point4
applyPermutation5 perm34201 point2 = point2
applyPermutation5 perm34201 point3 = point0
applyPermutation5 perm34201 point4 = point1
applyPermutation5 perm34210 point0 = point3
applyPermutation5 perm34210 point1 = point4
applyPermutation5 perm34210 point2 = point2
applyPermutation5 perm34210 point3 = point1
applyPermutation5 perm34210 point4 = point0
applyPermutation5 perm40123 point0 = point4
applyPermutation5 perm40123 point1 = point0
applyPermutation5 perm40123 point2 = point1
applyPermutation5 perm40123 point3 = point2
applyPermutation5 perm40123 point4 = point3
applyPermutation5 perm40132 point0 = point4
applyPermutation5 perm40132 point1 = point0
applyPermutation5 perm40132 point2 = point1
applyPermutation5 perm40132 point3 = point3
applyPermutation5 perm40132 point4 = point2
applyPermutation5 perm40213 point0 = point4
applyPermutation5 perm40213 point1 = point0
applyPermutation5 perm40213 point2 = point2
applyPermutation5 perm40213 point3 = point1
applyPermutation5 perm40213 point4 = point3
applyPermutation5 perm40231 point0 = point4
applyPermutation5 perm40231 point1 = point0
applyPermutation5 perm40231 point2 = point2
applyPermutation5 perm40231 point3 = point3
applyPermutation5 perm40231 point4 = point1
applyPermutation5 perm40312 point0 = point4
applyPermutation5 perm40312 point1 = point0
applyPermutation5 perm40312 point2 = point3
applyPermutation5 perm40312 point3 = point1
applyPermutation5 perm40312 point4 = point2
applyPermutation5 perm40321 point0 = point4
applyPermutation5 perm40321 point1 = point0
applyPermutation5 perm40321 point2 = point3
applyPermutation5 perm40321 point3 = point2
applyPermutation5 perm40321 point4 = point1
applyPermutation5 perm41023 point0 = point4
applyPermutation5 perm41023 point1 = point1
applyPermutation5 perm41023 point2 = point0
applyPermutation5 perm41023 point3 = point2
applyPermutation5 perm41023 point4 = point3
applyPermutation5 perm41032 point0 = point4
applyPermutation5 perm41032 point1 = point1
applyPermutation5 perm41032 point2 = point0
applyPermutation5 perm41032 point3 = point3
applyPermutation5 perm41032 point4 = point2
applyPermutation5 perm41203 point0 = point4
applyPermutation5 perm41203 point1 = point1
applyPermutation5 perm41203 point2 = point2
applyPermutation5 perm41203 point3 = point0
applyPermutation5 perm41203 point4 = point3
applyPermutation5 perm41230 point0 = point4
applyPermutation5 perm41230 point1 = point1
applyPermutation5 perm41230 point2 = point2
applyPermutation5 perm41230 point3 = point3
applyPermutation5 perm41230 point4 = point0
applyPermutation5 perm41302 point0 = point4
applyPermutation5 perm41302 point1 = point1
applyPermutation5 perm41302 point2 = point3
applyPermutation5 perm41302 point3 = point0
applyPermutation5 perm41302 point4 = point2
applyPermutation5 perm41320 point0 = point4
applyPermutation5 perm41320 point1 = point1
applyPermutation5 perm41320 point2 = point3
applyPermutation5 perm41320 point3 = point2
applyPermutation5 perm41320 point4 = point0
applyPermutation5 perm42013 point0 = point4
applyPermutation5 perm42013 point1 = point2
applyPermutation5 perm42013 point2 = point0
applyPermutation5 perm42013 point3 = point1
applyPermutation5 perm42013 point4 = point3
applyPermutation5 perm42031 point0 = point4
applyPermutation5 perm42031 point1 = point2
applyPermutation5 perm42031 point2 = point0
applyPermutation5 perm42031 point3 = point3
applyPermutation5 perm42031 point4 = point1
applyPermutation5 perm42103 point0 = point4
applyPermutation5 perm42103 point1 = point2
applyPermutation5 perm42103 point2 = point1
applyPermutation5 perm42103 point3 = point0
applyPermutation5 perm42103 point4 = point3
applyPermutation5 perm42130 point0 = point4
applyPermutation5 perm42130 point1 = point2
applyPermutation5 perm42130 point2 = point1
applyPermutation5 perm42130 point3 = point3
applyPermutation5 perm42130 point4 = point0
applyPermutation5 perm42301 point0 = point4
applyPermutation5 perm42301 point1 = point2
applyPermutation5 perm42301 point2 = point3
applyPermutation5 perm42301 point3 = point0
applyPermutation5 perm42301 point4 = point1
applyPermutation5 perm42310 point0 = point4
applyPermutation5 perm42310 point1 = point2
applyPermutation5 perm42310 point2 = point3
applyPermutation5 perm42310 point3 = point1
applyPermutation5 perm42310 point4 = point0
applyPermutation5 perm43012 point0 = point4
applyPermutation5 perm43012 point1 = point3
applyPermutation5 perm43012 point2 = point0
applyPermutation5 perm43012 point3 = point1
applyPermutation5 perm43012 point4 = point2
applyPermutation5 perm43021 point0 = point4
applyPermutation5 perm43021 point1 = point3
applyPermutation5 perm43021 point2 = point0
applyPermutation5 perm43021 point3 = point2
applyPermutation5 perm43021 point4 = point1
applyPermutation5 perm43102 point0 = point4
applyPermutation5 perm43102 point1 = point3
applyPermutation5 perm43102 point2 = point1
applyPermutation5 perm43102 point3 = point0
applyPermutation5 perm43102 point4 = point2
applyPermutation5 perm43120 point0 = point4
applyPermutation5 perm43120 point1 = point3
applyPermutation5 perm43120 point2 = point1
applyPermutation5 perm43120 point3 = point2
applyPermutation5 perm43120 point4 = point0
applyPermutation5 perm43201 point0 = point4
applyPermutation5 perm43201 point1 = point3
applyPermutation5 perm43201 point2 = point2
applyPermutation5 perm43201 point3 = point0
applyPermutation5 perm43201 point4 = point1
applyPermutation5 perm43210 point0 = point4
applyPermutation5 perm43210 point1 = point3
applyPermutation5 perm43210 point2 = point2
applyPermutation5 perm43210 point3 = point1
applyPermutation5 perm43210 point4 = point0

tripleCoordinates :
  DistinctTriple5 → Point5 × (Point5 × Point5)
tripleCoordinates triple012 = point0 , (point1 , point2)
tripleCoordinates triple013 = point0 , (point1 , point3)
tripleCoordinates triple014 = point0 , (point1 , point4)
tripleCoordinates triple021 = point0 , (point2 , point1)
tripleCoordinates triple023 = point0 , (point2 , point3)
tripleCoordinates triple024 = point0 , (point2 , point4)
tripleCoordinates triple031 = point0 , (point3 , point1)
tripleCoordinates triple032 = point0 , (point3 , point2)
tripleCoordinates triple034 = point0 , (point3 , point4)
tripleCoordinates triple041 = point0 , (point4 , point1)
tripleCoordinates triple042 = point0 , (point4 , point2)
tripleCoordinates triple043 = point0 , (point4 , point3)
tripleCoordinates triple102 = point1 , (point0 , point2)
tripleCoordinates triple103 = point1 , (point0 , point3)
tripleCoordinates triple104 = point1 , (point0 , point4)
tripleCoordinates triple120 = point1 , (point2 , point0)
tripleCoordinates triple123 = point1 , (point2 , point3)
tripleCoordinates triple124 = point1 , (point2 , point4)
tripleCoordinates triple130 = point1 , (point3 , point0)
tripleCoordinates triple132 = point1 , (point3 , point2)
tripleCoordinates triple134 = point1 , (point3 , point4)
tripleCoordinates triple140 = point1 , (point4 , point0)
tripleCoordinates triple142 = point1 , (point4 , point2)
tripleCoordinates triple143 = point1 , (point4 , point3)
tripleCoordinates triple201 = point2 , (point0 , point1)
tripleCoordinates triple203 = point2 , (point0 , point3)
tripleCoordinates triple204 = point2 , (point0 , point4)
tripleCoordinates triple210 = point2 , (point1 , point0)
tripleCoordinates triple213 = point2 , (point1 , point3)
tripleCoordinates triple214 = point2 , (point1 , point4)
tripleCoordinates triple230 = point2 , (point3 , point0)
tripleCoordinates triple231 = point2 , (point3 , point1)
tripleCoordinates triple234 = point2 , (point3 , point4)
tripleCoordinates triple240 = point2 , (point4 , point0)
tripleCoordinates triple241 = point2 , (point4 , point1)
tripleCoordinates triple243 = point2 , (point4 , point3)
tripleCoordinates triple301 = point3 , (point0 , point1)
tripleCoordinates triple302 = point3 , (point0 , point2)
tripleCoordinates triple304 = point3 , (point0 , point4)
tripleCoordinates triple310 = point3 , (point1 , point0)
tripleCoordinates triple312 = point3 , (point1 , point2)
tripleCoordinates triple314 = point3 , (point1 , point4)
tripleCoordinates triple320 = point3 , (point2 , point0)
tripleCoordinates triple321 = point3 , (point2 , point1)
tripleCoordinates triple324 = point3 , (point2 , point4)
tripleCoordinates triple340 = point3 , (point4 , point0)
tripleCoordinates triple341 = point3 , (point4 , point1)
tripleCoordinates triple342 = point3 , (point4 , point2)
tripleCoordinates triple401 = point4 , (point0 , point1)
tripleCoordinates triple402 = point4 , (point0 , point2)
tripleCoordinates triple403 = point4 , (point0 , point3)
tripleCoordinates triple410 = point4 , (point1 , point0)
tripleCoordinates triple412 = point4 , (point1 , point2)
tripleCoordinates triple413 = point4 , (point1 , point3)
tripleCoordinates triple420 = point4 , (point2 , point0)
tripleCoordinates triple421 = point4 , (point2 , point1)
tripleCoordinates triple423 = point4 , (point2 , point3)
tripleCoordinates triple430 = point4 , (point3 , point0)
tripleCoordinates triple431 = point4 , (point3 , point1)
tripleCoordinates triple432 = point4 , (point3 , point2)

toTripleOrientation :
  Permutation5 → DistinctTriple5 × Orientation2
toTripleOrientation perm01234 = triple012 , evenChoice
toTripleOrientation perm01243 = triple012 , oddChoice
toTripleOrientation perm01324 = triple013 , oddChoice
toTripleOrientation perm01342 = triple013 , evenChoice
toTripleOrientation perm01423 = triple014 , evenChoice
toTripleOrientation perm01432 = triple014 , oddChoice
toTripleOrientation perm02134 = triple021 , oddChoice
toTripleOrientation perm02143 = triple021 , evenChoice
toTripleOrientation perm02314 = triple023 , evenChoice
toTripleOrientation perm02341 = triple023 , oddChoice
toTripleOrientation perm02413 = triple024 , oddChoice
toTripleOrientation perm02431 = triple024 , evenChoice
toTripleOrientation perm03124 = triple031 , evenChoice
toTripleOrientation perm03142 = triple031 , oddChoice
toTripleOrientation perm03214 = triple032 , oddChoice
toTripleOrientation perm03241 = triple032 , evenChoice
toTripleOrientation perm03412 = triple034 , evenChoice
toTripleOrientation perm03421 = triple034 , oddChoice
toTripleOrientation perm04123 = triple041 , oddChoice
toTripleOrientation perm04132 = triple041 , evenChoice
toTripleOrientation perm04213 = triple042 , evenChoice
toTripleOrientation perm04231 = triple042 , oddChoice
toTripleOrientation perm04312 = triple043 , oddChoice
toTripleOrientation perm04321 = triple043 , evenChoice
toTripleOrientation perm10234 = triple102 , oddChoice
toTripleOrientation perm10243 = triple102 , evenChoice
toTripleOrientation perm10324 = triple103 , evenChoice
toTripleOrientation perm10342 = triple103 , oddChoice
toTripleOrientation perm10423 = triple104 , oddChoice
toTripleOrientation perm10432 = triple104 , evenChoice
toTripleOrientation perm12034 = triple120 , evenChoice
toTripleOrientation perm12043 = triple120 , oddChoice
toTripleOrientation perm12304 = triple123 , oddChoice
toTripleOrientation perm12340 = triple123 , evenChoice
toTripleOrientation perm12403 = triple124 , evenChoice
toTripleOrientation perm12430 = triple124 , oddChoice
toTripleOrientation perm13024 = triple130 , oddChoice
toTripleOrientation perm13042 = triple130 , evenChoice
toTripleOrientation perm13204 = triple132 , evenChoice
toTripleOrientation perm13240 = triple132 , oddChoice
toTripleOrientation perm13402 = triple134 , oddChoice
toTripleOrientation perm13420 = triple134 , evenChoice
toTripleOrientation perm14023 = triple140 , evenChoice
toTripleOrientation perm14032 = triple140 , oddChoice
toTripleOrientation perm14203 = triple142 , oddChoice
toTripleOrientation perm14230 = triple142 , evenChoice
toTripleOrientation perm14302 = triple143 , evenChoice
toTripleOrientation perm14320 = triple143 , oddChoice
toTripleOrientation perm20134 = triple201 , evenChoice
toTripleOrientation perm20143 = triple201 , oddChoice
toTripleOrientation perm20314 = triple203 , oddChoice
toTripleOrientation perm20341 = triple203 , evenChoice
toTripleOrientation perm20413 = triple204 , evenChoice
toTripleOrientation perm20431 = triple204 , oddChoice
toTripleOrientation perm21034 = triple210 , oddChoice
toTripleOrientation perm21043 = triple210 , evenChoice
toTripleOrientation perm21304 = triple213 , evenChoice
toTripleOrientation perm21340 = triple213 , oddChoice
toTripleOrientation perm21403 = triple214 , oddChoice
toTripleOrientation perm21430 = triple214 , evenChoice
toTripleOrientation perm23014 = triple230 , evenChoice
toTripleOrientation perm23041 = triple230 , oddChoice
toTripleOrientation perm23104 = triple231 , oddChoice
toTripleOrientation perm23140 = triple231 , evenChoice
toTripleOrientation perm23401 = triple234 , evenChoice
toTripleOrientation perm23410 = triple234 , oddChoice
toTripleOrientation perm24013 = triple240 , oddChoice
toTripleOrientation perm24031 = triple240 , evenChoice
toTripleOrientation perm24103 = triple241 , evenChoice
toTripleOrientation perm24130 = triple241 , oddChoice
toTripleOrientation perm24301 = triple243 , oddChoice
toTripleOrientation perm24310 = triple243 , evenChoice
toTripleOrientation perm30124 = triple301 , oddChoice
toTripleOrientation perm30142 = triple301 , evenChoice
toTripleOrientation perm30214 = triple302 , evenChoice
toTripleOrientation perm30241 = triple302 , oddChoice
toTripleOrientation perm30412 = triple304 , oddChoice
toTripleOrientation perm30421 = triple304 , evenChoice
toTripleOrientation perm31024 = triple310 , evenChoice
toTripleOrientation perm31042 = triple310 , oddChoice
toTripleOrientation perm31204 = triple312 , oddChoice
toTripleOrientation perm31240 = triple312 , evenChoice
toTripleOrientation perm31402 = triple314 , evenChoice
toTripleOrientation perm31420 = triple314 , oddChoice
toTripleOrientation perm32014 = triple320 , oddChoice
toTripleOrientation perm32041 = triple320 , evenChoice
toTripleOrientation perm32104 = triple321 , evenChoice
toTripleOrientation perm32140 = triple321 , oddChoice
toTripleOrientation perm32401 = triple324 , oddChoice
toTripleOrientation perm32410 = triple324 , evenChoice
toTripleOrientation perm34012 = triple340 , evenChoice
toTripleOrientation perm34021 = triple340 , oddChoice
toTripleOrientation perm34102 = triple341 , oddChoice
toTripleOrientation perm34120 = triple341 , evenChoice
toTripleOrientation perm34201 = triple342 , evenChoice
toTripleOrientation perm34210 = triple342 , oddChoice
toTripleOrientation perm40123 = triple401 , evenChoice
toTripleOrientation perm40132 = triple401 , oddChoice
toTripleOrientation perm40213 = triple402 , oddChoice
toTripleOrientation perm40231 = triple402 , evenChoice
toTripleOrientation perm40312 = triple403 , evenChoice
toTripleOrientation perm40321 = triple403 , oddChoice
toTripleOrientation perm41023 = triple410 , oddChoice
toTripleOrientation perm41032 = triple410 , evenChoice
toTripleOrientation perm41203 = triple412 , evenChoice
toTripleOrientation perm41230 = triple412 , oddChoice
toTripleOrientation perm41302 = triple413 , oddChoice
toTripleOrientation perm41320 = triple413 , evenChoice
toTripleOrientation perm42013 = triple420 , evenChoice
toTripleOrientation perm42031 = triple420 , oddChoice
toTripleOrientation perm42103 = triple421 , oddChoice
toTripleOrientation perm42130 = triple421 , evenChoice
toTripleOrientation perm42301 = triple423 , evenChoice
toTripleOrientation perm42310 = triple423 , oddChoice
toTripleOrientation perm43012 = triple430 , oddChoice
toTripleOrientation perm43021 = triple430 , evenChoice
toTripleOrientation perm43102 = triple431 , evenChoice
toTripleOrientation perm43120 = triple431 , oddChoice
toTripleOrientation perm43201 = triple432 , oddChoice
toTripleOrientation perm43210 = triple432 , evenChoice

fromTripleOrientation :
  DistinctTriple5 × Orientation2 → Permutation5
fromTripleOrientation (triple012 , evenChoice) = perm01234
fromTripleOrientation (triple012 , oddChoice) = perm01243
fromTripleOrientation (triple013 , evenChoice) = perm01342
fromTripleOrientation (triple013 , oddChoice) = perm01324
fromTripleOrientation (triple014 , evenChoice) = perm01423
fromTripleOrientation (triple014 , oddChoice) = perm01432
fromTripleOrientation (triple021 , evenChoice) = perm02143
fromTripleOrientation (triple021 , oddChoice) = perm02134
fromTripleOrientation (triple023 , evenChoice) = perm02314
fromTripleOrientation (triple023 , oddChoice) = perm02341
fromTripleOrientation (triple024 , evenChoice) = perm02431
fromTripleOrientation (triple024 , oddChoice) = perm02413
fromTripleOrientation (triple031 , evenChoice) = perm03124
fromTripleOrientation (triple031 , oddChoice) = perm03142
fromTripleOrientation (triple032 , evenChoice) = perm03241
fromTripleOrientation (triple032 , oddChoice) = perm03214
fromTripleOrientation (triple034 , evenChoice) = perm03412
fromTripleOrientation (triple034 , oddChoice) = perm03421
fromTripleOrientation (triple041 , evenChoice) = perm04132
fromTripleOrientation (triple041 , oddChoice) = perm04123
fromTripleOrientation (triple042 , evenChoice) = perm04213
fromTripleOrientation (triple042 , oddChoice) = perm04231
fromTripleOrientation (triple043 , evenChoice) = perm04321
fromTripleOrientation (triple043 , oddChoice) = perm04312
fromTripleOrientation (triple102 , evenChoice) = perm10243
fromTripleOrientation (triple102 , oddChoice) = perm10234
fromTripleOrientation (triple103 , evenChoice) = perm10324
fromTripleOrientation (triple103 , oddChoice) = perm10342
fromTripleOrientation (triple104 , evenChoice) = perm10432
fromTripleOrientation (triple104 , oddChoice) = perm10423
fromTripleOrientation (triple120 , evenChoice) = perm12034
fromTripleOrientation (triple120 , oddChoice) = perm12043
fromTripleOrientation (triple123 , evenChoice) = perm12340
fromTripleOrientation (triple123 , oddChoice) = perm12304
fromTripleOrientation (triple124 , evenChoice) = perm12403
fromTripleOrientation (triple124 , oddChoice) = perm12430
fromTripleOrientation (triple130 , evenChoice) = perm13042
fromTripleOrientation (triple130 , oddChoice) = perm13024
fromTripleOrientation (triple132 , evenChoice) = perm13204
fromTripleOrientation (triple132 , oddChoice) = perm13240
fromTripleOrientation (triple134 , evenChoice) = perm13420
fromTripleOrientation (triple134 , oddChoice) = perm13402
fromTripleOrientation (triple140 , evenChoice) = perm14023
fromTripleOrientation (triple140 , oddChoice) = perm14032
fromTripleOrientation (triple142 , evenChoice) = perm14230
fromTripleOrientation (triple142 , oddChoice) = perm14203
fromTripleOrientation (triple143 , evenChoice) = perm14302
fromTripleOrientation (triple143 , oddChoice) = perm14320
fromTripleOrientation (triple201 , evenChoice) = perm20134
fromTripleOrientation (triple201 , oddChoice) = perm20143
fromTripleOrientation (triple203 , evenChoice) = perm20341
fromTripleOrientation (triple203 , oddChoice) = perm20314
fromTripleOrientation (triple204 , evenChoice) = perm20413
fromTripleOrientation (triple204 , oddChoice) = perm20431
fromTripleOrientation (triple210 , evenChoice) = perm21043
fromTripleOrientation (triple210 , oddChoice) = perm21034
fromTripleOrientation (triple213 , evenChoice) = perm21304
fromTripleOrientation (triple213 , oddChoice) = perm21340
fromTripleOrientation (triple214 , evenChoice) = perm21430
fromTripleOrientation (triple214 , oddChoice) = perm21403
fromTripleOrientation (triple230 , evenChoice) = perm23014
fromTripleOrientation (triple230 , oddChoice) = perm23041
fromTripleOrientation (triple231 , evenChoice) = perm23140
fromTripleOrientation (triple231 , oddChoice) = perm23104
fromTripleOrientation (triple234 , evenChoice) = perm23401
fromTripleOrientation (triple234 , oddChoice) = perm23410
fromTripleOrientation (triple240 , evenChoice) = perm24031
fromTripleOrientation (triple240 , oddChoice) = perm24013
fromTripleOrientation (triple241 , evenChoice) = perm24103
fromTripleOrientation (triple241 , oddChoice) = perm24130
fromTripleOrientation (triple243 , evenChoice) = perm24310
fromTripleOrientation (triple243 , oddChoice) = perm24301
fromTripleOrientation (triple301 , evenChoice) = perm30142
fromTripleOrientation (triple301 , oddChoice) = perm30124
fromTripleOrientation (triple302 , evenChoice) = perm30214
fromTripleOrientation (triple302 , oddChoice) = perm30241
fromTripleOrientation (triple304 , evenChoice) = perm30421
fromTripleOrientation (triple304 , oddChoice) = perm30412
fromTripleOrientation (triple310 , evenChoice) = perm31024
fromTripleOrientation (triple310 , oddChoice) = perm31042
fromTripleOrientation (triple312 , evenChoice) = perm31240
fromTripleOrientation (triple312 , oddChoice) = perm31204
fromTripleOrientation (triple314 , evenChoice) = perm31402
fromTripleOrientation (triple314 , oddChoice) = perm31420
fromTripleOrientation (triple320 , evenChoice) = perm32041
fromTripleOrientation (triple320 , oddChoice) = perm32014
fromTripleOrientation (triple321 , evenChoice) = perm32104
fromTripleOrientation (triple321 , oddChoice) = perm32140
fromTripleOrientation (triple324 , evenChoice) = perm32410
fromTripleOrientation (triple324 , oddChoice) = perm32401
fromTripleOrientation (triple340 , evenChoice) = perm34012
fromTripleOrientation (triple340 , oddChoice) = perm34021
fromTripleOrientation (triple341 , evenChoice) = perm34120
fromTripleOrientation (triple341 , oddChoice) = perm34102
fromTripleOrientation (triple342 , evenChoice) = perm34201
fromTripleOrientation (triple342 , oddChoice) = perm34210
fromTripleOrientation (triple401 , evenChoice) = perm40123
fromTripleOrientation (triple401 , oddChoice) = perm40132
fromTripleOrientation (triple402 , evenChoice) = perm40231
fromTripleOrientation (triple402 , oddChoice) = perm40213
fromTripleOrientation (triple403 , evenChoice) = perm40312
fromTripleOrientation (triple403 , oddChoice) = perm40321
fromTripleOrientation (triple410 , evenChoice) = perm41032
fromTripleOrientation (triple410 , oddChoice) = perm41023
fromTripleOrientation (triple412 , evenChoice) = perm41203
fromTripleOrientation (triple412 , oddChoice) = perm41230
fromTripleOrientation (triple413 , evenChoice) = perm41320
fromTripleOrientation (triple413 , oddChoice) = perm41302
fromTripleOrientation (triple420 , evenChoice) = perm42013
fromTripleOrientation (triple420 , oddChoice) = perm42031
fromTripleOrientation (triple421 , evenChoice) = perm42130
fromTripleOrientation (triple421 , oddChoice) = perm42103
fromTripleOrientation (triple423 , evenChoice) = perm42301
fromTripleOrientation (triple423 , oddChoice) = perm42310
fromTripleOrientation (triple430 , evenChoice) = perm43021
fromTripleOrientation (triple430 , oddChoice) = perm43012
fromTripleOrientation (triple431 , evenChoice) = perm43102
fromTripleOrientation (triple431 , oddChoice) = perm43120
fromTripleOrientation (triple432 , evenChoice) = perm43210
fromTripleOrientation (triple432 , oddChoice) = perm43201

permutationAtlasRoundTrip :
  (p : Permutation5) →
  fromTripleOrientation (toTripleOrientation p) ≡ p
permutationAtlasRoundTrip perm01234 = refl
permutationAtlasRoundTrip perm01243 = refl
permutationAtlasRoundTrip perm01324 = refl
permutationAtlasRoundTrip perm01342 = refl
permutationAtlasRoundTrip perm01423 = refl
permutationAtlasRoundTrip perm01432 = refl
permutationAtlasRoundTrip perm02134 = refl
permutationAtlasRoundTrip perm02143 = refl
permutationAtlasRoundTrip perm02314 = refl
permutationAtlasRoundTrip perm02341 = refl
permutationAtlasRoundTrip perm02413 = refl
permutationAtlasRoundTrip perm02431 = refl
permutationAtlasRoundTrip perm03124 = refl
permutationAtlasRoundTrip perm03142 = refl
permutationAtlasRoundTrip perm03214 = refl
permutationAtlasRoundTrip perm03241 = refl
permutationAtlasRoundTrip perm03412 = refl
permutationAtlasRoundTrip perm03421 = refl
permutationAtlasRoundTrip perm04123 = refl
permutationAtlasRoundTrip perm04132 = refl
permutationAtlasRoundTrip perm04213 = refl
permutationAtlasRoundTrip perm04231 = refl
permutationAtlasRoundTrip perm04312 = refl
permutationAtlasRoundTrip perm04321 = refl
permutationAtlasRoundTrip perm10234 = refl
permutationAtlasRoundTrip perm10243 = refl
permutationAtlasRoundTrip perm10324 = refl
permutationAtlasRoundTrip perm10342 = refl
permutationAtlasRoundTrip perm10423 = refl
permutationAtlasRoundTrip perm10432 = refl
permutationAtlasRoundTrip perm12034 = refl
permutationAtlasRoundTrip perm12043 = refl
permutationAtlasRoundTrip perm12304 = refl
permutationAtlasRoundTrip perm12340 = refl
permutationAtlasRoundTrip perm12403 = refl
permutationAtlasRoundTrip perm12430 = refl
permutationAtlasRoundTrip perm13024 = refl
permutationAtlasRoundTrip perm13042 = refl
permutationAtlasRoundTrip perm13204 = refl
permutationAtlasRoundTrip perm13240 = refl
permutationAtlasRoundTrip perm13402 = refl
permutationAtlasRoundTrip perm13420 = refl
permutationAtlasRoundTrip perm14023 = refl
permutationAtlasRoundTrip perm14032 = refl
permutationAtlasRoundTrip perm14203 = refl
permutationAtlasRoundTrip perm14230 = refl
permutationAtlasRoundTrip perm14302 = refl
permutationAtlasRoundTrip perm14320 = refl
permutationAtlasRoundTrip perm20134 = refl
permutationAtlasRoundTrip perm20143 = refl
permutationAtlasRoundTrip perm20314 = refl
permutationAtlasRoundTrip perm20341 = refl
permutationAtlasRoundTrip perm20413 = refl
permutationAtlasRoundTrip perm20431 = refl
permutationAtlasRoundTrip perm21034 = refl
permutationAtlasRoundTrip perm21043 = refl
permutationAtlasRoundTrip perm21304 = refl
permutationAtlasRoundTrip perm21340 = refl
permutationAtlasRoundTrip perm21403 = refl
permutationAtlasRoundTrip perm21430 = refl
permutationAtlasRoundTrip perm23014 = refl
permutationAtlasRoundTrip perm23041 = refl
permutationAtlasRoundTrip perm23104 = refl
permutationAtlasRoundTrip perm23140 = refl
permutationAtlasRoundTrip perm23401 = refl
permutationAtlasRoundTrip perm23410 = refl
permutationAtlasRoundTrip perm24013 = refl
permutationAtlasRoundTrip perm24031 = refl
permutationAtlasRoundTrip perm24103 = refl
permutationAtlasRoundTrip perm24130 = refl
permutationAtlasRoundTrip perm24301 = refl
permutationAtlasRoundTrip perm24310 = refl
permutationAtlasRoundTrip perm30124 = refl
permutationAtlasRoundTrip perm30142 = refl
permutationAtlasRoundTrip perm30214 = refl
permutationAtlasRoundTrip perm30241 = refl
permutationAtlasRoundTrip perm30412 = refl
permutationAtlasRoundTrip perm30421 = refl
permutationAtlasRoundTrip perm31024 = refl
permutationAtlasRoundTrip perm31042 = refl
permutationAtlasRoundTrip perm31204 = refl
permutationAtlasRoundTrip perm31240 = refl
permutationAtlasRoundTrip perm31402 = refl
permutationAtlasRoundTrip perm31420 = refl
permutationAtlasRoundTrip perm32014 = refl
permutationAtlasRoundTrip perm32041 = refl
permutationAtlasRoundTrip perm32104 = refl
permutationAtlasRoundTrip perm32140 = refl
permutationAtlasRoundTrip perm32401 = refl
permutationAtlasRoundTrip perm32410 = refl
permutationAtlasRoundTrip perm34012 = refl
permutationAtlasRoundTrip perm34021 = refl
permutationAtlasRoundTrip perm34102 = refl
permutationAtlasRoundTrip perm34120 = refl
permutationAtlasRoundTrip perm34201 = refl
permutationAtlasRoundTrip perm34210 = refl
permutationAtlasRoundTrip perm40123 = refl
permutationAtlasRoundTrip perm40132 = refl
permutationAtlasRoundTrip perm40213 = refl
permutationAtlasRoundTrip perm40231 = refl
permutationAtlasRoundTrip perm40312 = refl
permutationAtlasRoundTrip perm40321 = refl
permutationAtlasRoundTrip perm41023 = refl
permutationAtlasRoundTrip perm41032 = refl
permutationAtlasRoundTrip perm41203 = refl
permutationAtlasRoundTrip perm41230 = refl
permutationAtlasRoundTrip perm41302 = refl
permutationAtlasRoundTrip perm41320 = refl
permutationAtlasRoundTrip perm42013 = refl
permutationAtlasRoundTrip perm42031 = refl
permutationAtlasRoundTrip perm42103 = refl
permutationAtlasRoundTrip perm42130 = refl
permutationAtlasRoundTrip perm42301 = refl
permutationAtlasRoundTrip perm42310 = refl
permutationAtlasRoundTrip perm43012 = refl
permutationAtlasRoundTrip perm43021 = refl
permutationAtlasRoundTrip perm43102 = refl
permutationAtlasRoundTrip perm43120 = refl
permutationAtlasRoundTrip perm43201 = refl
permutationAtlasRoundTrip perm43210 = refl

tripleOrientationAtlasRoundTrip :
  (s : DistinctTriple5 × Orientation2) →
  toTripleOrientation (fromTripleOrientation s) ≡ s
tripleOrientationAtlasRoundTrip (triple012 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple012 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple013 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple013 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple014 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple014 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple021 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple021 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple023 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple023 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple024 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple024 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple031 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple031 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple032 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple032 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple034 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple034 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple041 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple041 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple042 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple042 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple043 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple043 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple102 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple102 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple103 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple103 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple104 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple104 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple120 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple120 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple123 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple123 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple124 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple124 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple130 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple130 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple132 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple132 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple134 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple134 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple140 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple140 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple142 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple142 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple143 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple143 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple201 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple201 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple203 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple203 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple204 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple204 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple210 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple210 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple213 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple213 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple214 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple214 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple230 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple230 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple231 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple231 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple234 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple234 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple240 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple240 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple241 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple241 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple243 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple243 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple301 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple301 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple302 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple302 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple304 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple304 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple310 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple310 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple312 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple312 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple314 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple314 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple320 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple320 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple321 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple321 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple324 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple324 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple340 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple340 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple341 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple341 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple342 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple342 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple401 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple401 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple402 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple402 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple403 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple403 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple410 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple410 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple412 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple412 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple413 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple413 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple420 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple420 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple421 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple421 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple423 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple423 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple430 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple430 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple431 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple431 , oddChoice) = refl
tripleOrientationAtlasRoundTrip (triple432 , evenChoice) = refl
tripleOrientationAtlasRoundTrip (triple432 , oddChoice) = refl

firstThreePositionsAgreeWithChart :
  (p : Permutation5) →
  tripleCoordinates (proj₁ (toTripleOrientation p))
  ≡
  (applyPermutation5 p point0 ,
    (applyPermutation5 p point1 , applyPermutation5 p point2))
firstThreePositionsAgreeWithChart perm01234 = refl
firstThreePositionsAgreeWithChart perm01243 = refl
firstThreePositionsAgreeWithChart perm01324 = refl
firstThreePositionsAgreeWithChart perm01342 = refl
firstThreePositionsAgreeWithChart perm01423 = refl
firstThreePositionsAgreeWithChart perm01432 = refl
firstThreePositionsAgreeWithChart perm02134 = refl
firstThreePositionsAgreeWithChart perm02143 = refl
firstThreePositionsAgreeWithChart perm02314 = refl
firstThreePositionsAgreeWithChart perm02341 = refl
firstThreePositionsAgreeWithChart perm02413 = refl
firstThreePositionsAgreeWithChart perm02431 = refl
firstThreePositionsAgreeWithChart perm03124 = refl
firstThreePositionsAgreeWithChart perm03142 = refl
firstThreePositionsAgreeWithChart perm03214 = refl
firstThreePositionsAgreeWithChart perm03241 = refl
firstThreePositionsAgreeWithChart perm03412 = refl
firstThreePositionsAgreeWithChart perm03421 = refl
firstThreePositionsAgreeWithChart perm04123 = refl
firstThreePositionsAgreeWithChart perm04132 = refl
firstThreePositionsAgreeWithChart perm04213 = refl
firstThreePositionsAgreeWithChart perm04231 = refl
firstThreePositionsAgreeWithChart perm04312 = refl
firstThreePositionsAgreeWithChart perm04321 = refl
firstThreePositionsAgreeWithChart perm10234 = refl
firstThreePositionsAgreeWithChart perm10243 = refl
firstThreePositionsAgreeWithChart perm10324 = refl
firstThreePositionsAgreeWithChart perm10342 = refl
firstThreePositionsAgreeWithChart perm10423 = refl
firstThreePositionsAgreeWithChart perm10432 = refl
firstThreePositionsAgreeWithChart perm12034 = refl
firstThreePositionsAgreeWithChart perm12043 = refl
firstThreePositionsAgreeWithChart perm12304 = refl
firstThreePositionsAgreeWithChart perm12340 = refl
firstThreePositionsAgreeWithChart perm12403 = refl
firstThreePositionsAgreeWithChart perm12430 = refl
firstThreePositionsAgreeWithChart perm13024 = refl
firstThreePositionsAgreeWithChart perm13042 = refl
firstThreePositionsAgreeWithChart perm13204 = refl
firstThreePositionsAgreeWithChart perm13240 = refl
firstThreePositionsAgreeWithChart perm13402 = refl
firstThreePositionsAgreeWithChart perm13420 = refl
firstThreePositionsAgreeWithChart perm14023 = refl
firstThreePositionsAgreeWithChart perm14032 = refl
firstThreePositionsAgreeWithChart perm14203 = refl
firstThreePositionsAgreeWithChart perm14230 = refl
firstThreePositionsAgreeWithChart perm14302 = refl
firstThreePositionsAgreeWithChart perm14320 = refl
firstThreePositionsAgreeWithChart perm20134 = refl
firstThreePositionsAgreeWithChart perm20143 = refl
firstThreePositionsAgreeWithChart perm20314 = refl
firstThreePositionsAgreeWithChart perm20341 = refl
firstThreePositionsAgreeWithChart perm20413 = refl
firstThreePositionsAgreeWithChart perm20431 = refl
firstThreePositionsAgreeWithChart perm21034 = refl
firstThreePositionsAgreeWithChart perm21043 = refl
firstThreePositionsAgreeWithChart perm21304 = refl
firstThreePositionsAgreeWithChart perm21340 = refl
firstThreePositionsAgreeWithChart perm21403 = refl
firstThreePositionsAgreeWithChart perm21430 = refl
firstThreePositionsAgreeWithChart perm23014 = refl
firstThreePositionsAgreeWithChart perm23041 = refl
firstThreePositionsAgreeWithChart perm23104 = refl
firstThreePositionsAgreeWithChart perm23140 = refl
firstThreePositionsAgreeWithChart perm23401 = refl
firstThreePositionsAgreeWithChart perm23410 = refl
firstThreePositionsAgreeWithChart perm24013 = refl
firstThreePositionsAgreeWithChart perm24031 = refl
firstThreePositionsAgreeWithChart perm24103 = refl
firstThreePositionsAgreeWithChart perm24130 = refl
firstThreePositionsAgreeWithChart perm24301 = refl
firstThreePositionsAgreeWithChart perm24310 = refl
firstThreePositionsAgreeWithChart perm30124 = refl
firstThreePositionsAgreeWithChart perm30142 = refl
firstThreePositionsAgreeWithChart perm30214 = refl
firstThreePositionsAgreeWithChart perm30241 = refl
firstThreePositionsAgreeWithChart perm30412 = refl
firstThreePositionsAgreeWithChart perm30421 = refl
firstThreePositionsAgreeWithChart perm31024 = refl
firstThreePositionsAgreeWithChart perm31042 = refl
firstThreePositionsAgreeWithChart perm31204 = refl
firstThreePositionsAgreeWithChart perm31240 = refl
firstThreePositionsAgreeWithChart perm31402 = refl
firstThreePositionsAgreeWithChart perm31420 = refl
firstThreePositionsAgreeWithChart perm32014 = refl
firstThreePositionsAgreeWithChart perm32041 = refl
firstThreePositionsAgreeWithChart perm32104 = refl
firstThreePositionsAgreeWithChart perm32140 = refl
firstThreePositionsAgreeWithChart perm32401 = refl
firstThreePositionsAgreeWithChart perm32410 = refl
firstThreePositionsAgreeWithChart perm34012 = refl
firstThreePositionsAgreeWithChart perm34021 = refl
firstThreePositionsAgreeWithChart perm34102 = refl
firstThreePositionsAgreeWithChart perm34120 = refl
firstThreePositionsAgreeWithChart perm34201 = refl
firstThreePositionsAgreeWithChart perm34210 = refl
firstThreePositionsAgreeWithChart perm40123 = refl
firstThreePositionsAgreeWithChart perm40132 = refl
firstThreePositionsAgreeWithChart perm40213 = refl
firstThreePositionsAgreeWithChart perm40231 = refl
firstThreePositionsAgreeWithChart perm40312 = refl
firstThreePositionsAgreeWithChart perm40321 = refl
firstThreePositionsAgreeWithChart perm41023 = refl
firstThreePositionsAgreeWithChart perm41032 = refl
firstThreePositionsAgreeWithChart perm41203 = refl
firstThreePositionsAgreeWithChart perm41230 = refl
firstThreePositionsAgreeWithChart perm41302 = refl
firstThreePositionsAgreeWithChart perm41320 = refl
firstThreePositionsAgreeWithChart perm42013 = refl
firstThreePositionsAgreeWithChart perm42031 = refl
firstThreePositionsAgreeWithChart perm42103 = refl
firstThreePositionsAgreeWithChart perm42130 = refl
firstThreePositionsAgreeWithChart perm42301 = refl
firstThreePositionsAgreeWithChart perm42310 = refl
firstThreePositionsAgreeWithChart perm43012 = refl
firstThreePositionsAgreeWithChart perm43021 = refl
firstThreePositionsAgreeWithChart perm43102 = refl
firstThreePositionsAgreeWithChart perm43120 = refl
firstThreePositionsAgreeWithChart perm43201 = refl
firstThreePositionsAgreeWithChart perm43210 = refl

allFivePermutations : List Permutation5
allFivePermutations = perm01234 ∷ perm01243 ∷ perm01324 ∷ perm01342 ∷ perm01423 ∷ perm01432 ∷ perm02134 ∷ perm02143 ∷ perm02314 ∷ perm02341 ∷ perm02413 ∷ perm02431 ∷ perm03124 ∷ perm03142 ∷ perm03214 ∷ perm03241 ∷ perm03412 ∷ perm03421 ∷ perm04123 ∷ perm04132 ∷ perm04213 ∷ perm04231 ∷ perm04312 ∷ perm04321 ∷ perm10234 ∷ perm10243 ∷ perm10324 ∷ perm10342 ∷ perm10423 ∷ perm10432 ∷ perm12034 ∷ perm12043 ∷ perm12304 ∷ perm12340 ∷ perm12403 ∷ perm12430 ∷ perm13024 ∷ perm13042 ∷ perm13204 ∷ perm13240 ∷ perm13402 ∷ perm13420 ∷ perm14023 ∷ perm14032 ∷ perm14203 ∷ perm14230 ∷ perm14302 ∷ perm14320 ∷ perm20134 ∷ perm20143 ∷ perm20314 ∷ perm20341 ∷ perm20413 ∷ perm20431 ∷ perm21034 ∷ perm21043 ∷ perm21304 ∷ perm21340 ∷ perm21403 ∷ perm21430 ∷ perm23014 ∷ perm23041 ∷ perm23104 ∷ perm23140 ∷ perm23401 ∷ perm23410 ∷ perm24013 ∷ perm24031 ∷ perm24103 ∷ perm24130 ∷ perm24301 ∷ perm24310 ∷ perm30124 ∷ perm30142 ∷ perm30214 ∷ perm30241 ∷ perm30412 ∷ perm30421 ∷ perm31024 ∷ perm31042 ∷ perm31204 ∷ perm31240 ∷ perm31402 ∷ perm31420 ∷ perm32014 ∷ perm32041 ∷ perm32104 ∷ perm32140 ∷ perm32401 ∷ perm32410 ∷ perm34012 ∷ perm34021 ∷ perm34102 ∷ perm34120 ∷ perm34201 ∷ perm34210 ∷ perm40123 ∷ perm40132 ∷ perm40213 ∷ perm40231 ∷ perm40312 ∷ perm40321 ∷ perm41023 ∷ perm41032 ∷ perm41203 ∷ perm41230 ∷ perm41302 ∷ perm41320 ∷ perm42013 ∷ perm42031 ∷ perm42103 ∷ perm42130 ∷ perm42301 ∷ perm42310 ∷ perm43012 ∷ perm43021 ∷ perm43102 ∷ perm43120 ∷ perm43201 ∷ perm43210 ∷ []

allDistinctTriples : List DistinctTriple5
allDistinctTriples = triple012 ∷ triple013 ∷ triple014 ∷ triple021 ∷ triple023 ∷ triple024 ∷ triple031 ∷ triple032 ∷ triple034 ∷ triple041 ∷ triple042 ∷ triple043 ∷ triple102 ∷ triple103 ∷ triple104 ∷ triple120 ∷ triple123 ∷ triple124 ∷ triple130 ∷ triple132 ∷ triple134 ∷ triple140 ∷ triple142 ∷ triple143 ∷ triple201 ∷ triple203 ∷ triple204 ∷ triple210 ∷ triple213 ∷ triple214 ∷ triple230 ∷ triple231 ∷ triple234 ∷ triple240 ∷ triple241 ∷ triple243 ∷ triple301 ∷ triple302 ∷ triple304 ∷ triple310 ∷ triple312 ∷ triple314 ∷ triple320 ∷ triple321 ∷ triple324 ∷ triple340 ∷ triple341 ∷ triple342 ∷ triple401 ∷ triple402 ∷ triple403 ∷ triple410 ∷ triple412 ∷ triple413 ∷ triple420 ∷ triple421 ∷ triple423 ∷ triple430 ∷ triple431 ∷ triple432 ∷ []

allEvenPermutationCodes : List Permutation5
allEvenPermutationCodes = perm01234 ∷ perm01342 ∷ perm01423 ∷ perm02143 ∷ perm02314 ∷ perm02431 ∷ perm03124 ∷ perm03241 ∷ perm03412 ∷ perm04132 ∷ perm04213 ∷ perm04321 ∷ perm10243 ∷ perm10324 ∷ perm10432 ∷ perm12034 ∷ perm12340 ∷ perm12403 ∷ perm13042 ∷ perm13204 ∷ perm13420 ∷ perm14023 ∷ perm14230 ∷ perm14302 ∷ perm20134 ∷ perm20341 ∷ perm20413 ∷ perm21043 ∷ perm21304 ∷ perm21430 ∷ perm23014 ∷ perm23140 ∷ perm23401 ∷ perm24031 ∷ perm24103 ∷ perm24310 ∷ perm30142 ∷ perm30214 ∷ perm30421 ∷ perm31024 ∷ perm31240 ∷ perm31402 ∷ perm32041 ∷ perm32104 ∷ perm32410 ∷ perm34012 ∷ perm34120 ∷ perm34201 ∷ perm40123 ∷ perm40231 ∷ perm40312 ∷ perm41032 ∷ perm41203 ∷ perm41320 ∷ perm42013 ∷ perm42130 ∷ perm42301 ∷ perm43021 ∷ perm43102 ∷ perm43210 ∷ []

permCountIs120 : length allFivePermutations ≡ 120
permCountIs120 = refl

tripleCountIs60 : length allDistinctTriples ≡ 60
tripleCountIs60 = refl

evenPermutationCountIs60 : length allEvenPermutationCodes ≡ 60
evenPermutationCountIs60 = refl

-- Numeric equality alone is not a group representation theorem.
data TripleChartCreatesGenericQuinticGaloisGroup : Set where

noAutomaticGaloisFromTripleChart :
  TripleChartCreatesGenericQuinticGaloisGroup → ⊥
noAutomaticGaloisFromTripleChart ()
