module DASHI.Biology.QualiaSymmetryPrincipalBundleBoundaryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Source-facing scope and attribution:
-- Masafumi Oizumi, Chanseok Lim, Ryota Kanai (2026),
-- "Principal bundle geometry of qualia: Understanding the quality of
-- consciousness from symmetry", PNAS Nexus 5(9), pgag261,
-- DOI 10.1093/pnasnexus/pgag261.
-- Production correction: PNAS Nexus 5(9), pgag313,
-- DOI 10.1093/pnasnexus/pgag313 (correct supplementary file, Fig 4).
--
-- DASHI-owned finite counterexample: equivariance alone DOES NOT imply
-- a free group action (a required principal-bundle hypothesis).
-- The source explicitly discusses free action; this is an audit witness,
-- NOT an allegation that the authors asserted arbitrary actions are free.
-- Their relational theory describes qualia in systems assumed conscious;
-- it does NOT establish a phenomenal consciousness existence criterion.
------------------------------------------------------------------------

data C2 : Set where
  identityElement : C2
  nontrivialElement : C2

compose : C2 → C2 → C2
compose identityElement b = b
compose nontrivialElement identityElement = nontrivialElement
compose nontrivialElement nontrivialElement = identityElement

composeAssociates :
  ∀ a b c → compose (compose a b) c ≡ compose a (compose b c)
composeAssociates identityElement identityElement identityElement = refl
composeAssociates identityElement identityElement nontrivialElement = refl
composeAssociates identityElement nontrivialElement identityElement = refl
composeAssociates identityElement nontrivialElement nontrivialElement = refl
composeAssociates nontrivialElement identityElement identityElement = refl
composeAssociates nontrivialElement identityElement nontrivialElement = refl
composeAssociates nontrivialElement nontrivialElement identityElement = refl
composeAssociates nontrivialElement nontrivialElement nontrivialElement = refl

data NeuralRepresentation : Set where
  representationA : NeuralRepresentation
  representationB : NeuralRepresentation

-- A genuine (nonfaithful) group action, both elements act as identity.
action : C2 → NeuralRepresentation → NeuralRepresentation
action _ x = x

actionIdentity :
  ∀ x → action identityElement x ≡ x
actionIdentity x = refl

actionCompose :
  ∀ g h x → action (compose g h) x ≡ action g (action h x)
actionCompose g h x = refl

encode : NeuralRepresentation → NeuralRepresentation
encode x = x

-- This is equivariance for the stipulated trivial input/output actions.
encoderEquivariant :
  ∀ g x → encode (action g x) ≡ action g (encode x)
encoderEquivariant g x = refl

record FreeAt (x : NeuralRepresentation) : Set where
  field
    groupElementIdentifiableFromAction :
      ∀ g h → action g x ≡ action h x → g ≡ h

open FreeAt public

identityIsNotNontrivial : identityElement ≡ nontrivialElement → ⊥
identityIsNotNontrivial ()

actionNotFreeAtA : FreeAt representationA → ⊥
actionNotFreeAtA free =
  identityIsNotNontrivial
    (groupElementIdentifiableFromAction free identityElement nontrivialElement refl)

equivarianceDoesNotForceFreeAction :
  (∀ {x} → (∀ g → encode (action g x) ≡ action g (encode x)) → FreeAt x) → ⊥
equivarianceDoesNotForceFreeAction claimed =
  actionNotFreeAtA (claimed encoderEquivariant)

------------------------------------------------------------------------
-- No claim: that this finite witness determines a perceptual neural
-- geometry, disproves Oizumi/Lim/Kanai, supplies biological free/proper
-- action conditions, or constitutes phenomenal experience.
------------------------------------------------------------------------
