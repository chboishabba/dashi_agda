module DASHI.Cognition.PNF.ProducerCompleteDependencyProjectionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import DASHI.Cognition.PNF.ProducerCompleteDependencyProjectionExact

------------------------------------------------------------------------
-- Tiny exact parser fibre:
--
--   root  -> root
--   child -> root
--
-- Persistent identity is the token itself, so injectivity is immediate.  This
-- exercises the same structural fact as the runtime producer-native projection:
-- the final head edge exists before authority insertion and does not require a
-- second persistent mutation.
------------------------------------------------------------------------

data TinyToken : Set where
  root child : TinyToken

tinyHead : TinyToken → TinyToken
tinyHead root = root
tinyHead child = root

tinyFibre : ProducerCompleteDependencyFibre TinyToken TinyToken
tinyFibre = record
  { head = tinyHead
  ; persistentId = λ token → token
  ; persistentIdInjective = λ left right proof → proof
  }

childDirectHeadIsRoot :
  headTokenId (directAuthorityRow tinyFibre child) ≡ root
childDirectHeadIsRoot = refl

rootDirectHeadIsSelf :
  headTokenId (directAuthorityRow tinyFibre root) ≡ root
rootDirectHeadIsSelf = refl

childDirectEqualsRepair :
  directAuthorityRow tinyFibre child ≡ repairedAuthorityRow tinyFibre child
childDirectEqualsRepair = producerCompleteProjectionExact tinyFibre child

directTwoTokenFibreHasNoRepairUpdates :
  postInsertUpdates (directMutationReceipt (suc (suc zero))) ≡ zero
directTwoTokenFibreHasNoRepairUpdates = refl

legacyTwoTokenFibreRepairsBothRows :
  postInsertUpdates (insertThenRepairMutationReceipt (suc (suc zero)))
    ≡ suc (suc zero)
legacyTwoTokenFibreRepairsBothRows = refl
