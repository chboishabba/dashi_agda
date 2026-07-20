module DASHI.Learning.Mod97WeightDecayReceipt where

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Learning.GrokkingOperatorContract

------------------------------------------------------------------------
-- Empirical receipt surface
--
-- Task: modular multiplication modulo 97.
-- Train split: 2822 / 9409 pairs (approximately 30%).
-- Model: shared residue embedding, one ReLU hidden layer, 97-way output.
-- Optimizer: AdamW, learning rate 1/1000, full-batch, CPU.
-- Horizon: 15000 epochs, measurements every 20 epochs.
--
-- Weight decay is stored in thousandths: 200 means 0.2, 1000 means 1.0.
-- Final accuracy is stored in permille and rounded from the printed run.
-- A missing t95 is right-censoring at epoch 15000, not non-existence.
------------------------------------------------------------------------

modulus : Nat
modulus = 97

totalPairs : Nat
totalPairs = 9409

trainingPairs : Nat
trainingPairs = 2822

testPairs : Nat
testPairs = 6587

record RunReceipt : Set where
  field
    weightDecayMilli : Nat
    seed             : Nat
    observation      : GrokkingObservation

open RunReceipt public

run : Nat → Nat → FirstPassage → Nat → RunReceipt
run wd seed passage finalTest = record
  { weightDecayMilli = wd
  ; seed = seed
  ; observation = record
      { horizon = 15000
      ; fit99 = notRecorded
      ; test95 = passage
      ; finalTrainPermille = 1000
      ; finalTestPermille = finalTest
      }
  }

------------------------------------------------------------------------
-- Coarse scan receipts
------------------------------------------------------------------------

wd200-s0 = run 200 0 rightCensored 24
wd200-s1 = run 200 1 rightCensored 19
wd200-s2 = run 200 2 rightCensored 23

wd300-s0 = run 300 0 rightCensored 104
wd300-s1 = run 300 1 rightCensored 24
wd300-s2 = run 300 2 rightCensored 57

wd400-s0 = run 400 0 rightCensored 634
wd400-s1 = run 400 1 rightCensored 150
wd400-s2 = run 400 2 rightCensored 316

wd500-s0 = run 500 0 (observedAt 14440) 974
wd500-s1 = run 500 1 rightCensored 782
wd500-s2 = run 500 2 rightCensored 797

wd600-s0 = run 600 0 (observedAt 11560) 1000
wd600-s1 = run 600 1 (observedAt 13720) 995
wd600-s2 = run 600 2 (observedAt 14620) 973

wd700-s0 = run 700 0 (observedAt 10080) 1000
wd700-s1 = run 700 1 (observedAt 11760) 1000
wd700-s2 = run 700 2 (observedAt 12200) 1000

wd800-s0 = run 800 0 (observedAt 8640) 1000
wd800-s1 = run 800 1 (observedAt 10200) 1000
wd800-s2 = run 800 2 (observedAt 10620) 1000

wd900-s0 = run 900 0 (observedAt 7520) 1000
wd900-s1 = run 900 1 (observedAt 9280) 1000
wd900-s2 = run 900 2 (observedAt 9620) 1000

wd1000-s0 = run 1000 0 (observedAt 6620) 1000
wd1000-s1 = run 1000 1 (observedAt 8160) 1000
wd1000-s2 = run 1000 2 (observedAt 8400) 1000

------------------------------------------------------------------------
-- Fine boundary scan receipts
------------------------------------------------------------------------

wd450-s0 = run 450 0 rightCensored 890
wd450-s1 = run 450 1 rightCensored 421
wd450-s2 = run 450 2 rightCensored 521

wd460-s0 = run 460 0 rightCensored 935
wd460-s1 = run 460 1 rightCensored 511
wd460-s2 = run 460 2 rightCensored 570

wd470-s0 = run 470 0 rightCensored 947
wd470-s1 = run 470 1 rightCensored 477
wd470-s2 = run 470 2 rightCensored 634

wd480-s0 = run 480 0 rightCensored 934
wd480-s1 = run 480 1 rightCensored 683
wd480-s2 = run 480 2 rightCensored 644

wd490-s0 = run 490 0 (observedAt 14760) 964
wd490-s1 = run 490 1 rightCensored 712
wd490-s2 = run 490 2 rightCensored 742

wd510-s0 = run 510 0 (observedAt 14500) 974
wd510-s1 = run 510 1 rightCensored 820
wd510-s2 = run 510 2 rightCensored 791

wd520-s0 = run 520 0 (observedAt 13960) 988
wd520-s1 = run 520 1 rightCensored 891
wd520-s2 = run 520 2 rightCensored 836

wd530-s0 = run 530 0 (observedAt 13360) 998
wd530-s1 = run 530 1 rightCensored 871
wd530-s2 = run 530 2 rightCensored 865

wd540-s0 = run 540 0 (observedAt 12960) 1000
wd540-s1 = run 540 1 rightCensored 927
wd540-s2 = run 540 2 rightCensored 913

wd550-s0 = run 550 0 (observedAt 12920) 1000
wd550-s1 = run 550 1 rightCensored 948
wd550-s2 = run 550 2 rightCensored 914
