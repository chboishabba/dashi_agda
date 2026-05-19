module DASHI.Arithmetic.NormalizeAddNonexpansive where

open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)

open import DASHI.Arithmetic.NormalizeAdd using
  ( normalizeAdd
  ; normalizeAdd-padicDepthPreserved
  ; normalizeAdd-primePreserved
  )
open import DASHI.Arithmetic.NormalizeAddState using (NormalizeAddState; padicAgreement)

normalizeAdd-nonexpansive :
  ∀ x y k →
  padicAgreement x y k →
  padicAgreement (normalizeAdd x) (normalizeAdd y) k
normalizeAdd-nonexpansive x y k (samePrime , (samePadicDepth , (k≤x , k≤y)))
  rewrite normalizeAdd-primePreserved x
        | normalizeAdd-primePreserved y
        | normalizeAdd-padicDepthPreserved x
        | normalizeAdd-padicDepthPreserved y
  = samePrime , (samePadicDepth , (k≤x , k≤y))

record NormalizeAddNonexpansive : Set₁ where
  field
    nonexpansive :
      ∀ x y k →
      padicAgreement x y k →
      padicAgreement (normalizeAdd x) (normalizeAdd y) k

firstNormalizeAddNonexpansive : NormalizeAddNonexpansive
firstNormalizeAddNonexpansive =
  record
    { nonexpansive = normalizeAdd-nonexpansive
    }
