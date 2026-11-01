module Verification.ZK where

open import Verification.Prelude

postulate Public  : Set
postulate Private : Set
postulate Output  : Set

-- The spec function (what correctness means)
postulate spec : Public -> Private -> Output

-- An implementation whose correctness you want to prove (could be a circuit)
postulate impl : Public -> Private -> Output

-- A proof object (SNARK) and a verifier predicate
postulate Proof : Set
postulate verify : Public -> Output -> Proof -> Bool

-- Soundness contract (non-ZK): if verifier accepts, output equals spec
-- (This is where you plug the cryptographic theorem/certificate.)
postulate
  zkSoundness :
    (pub : Public) -> (priv : Private) -> (out : Output) -> (pi : Proof) ->
    verify pub out pi ≡ true ->
    out ≡ spec pub priv

-- ZK verification artifact: provide pub/out/proof and a verification boolean proof.
record ZKCorrectness : Set1 where
  field
    pub  : Public
    priv : Private
    out  : Output
    pi   : Proof
    accepts : verify pub out pi ≡ true
    correct : out ≡ spec pub priv
