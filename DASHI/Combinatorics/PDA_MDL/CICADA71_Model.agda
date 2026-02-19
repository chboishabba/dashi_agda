module DASHI.Combinatorics.PDA_MDL.CICADA71_Model where

open import DASHI.Combinatorics.PDA_MDL.Prelude
open import DASHI.Combinatorics.PDA_MDL.CICADA71
open import DASHI.Combinatorics.PDA_MDL.ExponentVector
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)

Bucket : Set
Bucket = Fin 71

shard : EV → Bucket
shard = bucket71-ev

DatasetB : Set
DatasetB = List Bucket

shardDataset : DatasetEV → DatasetB
shardDataset []       = []
shardDataset (x ∷ xs) = shard x ∷ shardDataset xs

-- A very concrete bucket code length: constant (baseline)
lenBucket : Bucket → CodeLength
lenBucket _ = 7  -- 71 buckets need ~7 bits; use Nat as approximation

lenBuckets : DatasetB → CodeLength
lenBuckets []       = zero
lenBuckets (b ∷ bs) = lenBucket b + lenBuckets bs

-- IID bucket model with parameter cost (a table). Keep it simple now.
record IID71 : Set where
  field tableCost : CodeLength

Lmodel71 : IID71 → CodeLength
Lmodel71 M = IID71.tableCost M

Ldata|71 : IID71 → DatasetB → CodeLength
Ldata|71 M D = lenBuckets D  -- replace with -log p(b) once you encode probs

MDL71 : IID71 → DatasetEV → CodeLength
MDL71 M D = Lmodel71 M + Ldata|71 M (shardDataset D)
