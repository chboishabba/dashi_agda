module DASHI.Research.OpenAIMath.OpenAIMathCorpusRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Research.OpenAIMath.Everything

_ : upstreamCommit ≡ "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
_ = refl

_ : upstreamLeanToolchain ≡ "leanprover/lean4:v4.34.1"
_ = refl

_ : upstreamLicense ≡ "Apache-2.0"
_ = refl

_ : manuscriptClaimIsAgdaTheorem ≡ false
_ = refl

_ : upstreamLeanTheoremIsAgdaTheorem ≡ false
_ = refl

_ : relevancePromotesSameObjectTransport ≡ false
_ = refl

_ : priorityClass riemannHypothesis ≡ directFrontier
_ = refl

_ : priorityClass ellipticCM ≡ directFrontier
_ = refl

_ : priorityClass exceptionalRepresentation ≡ lemmaDonor
_ = refl
