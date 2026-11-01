module DASHI.Law.CoerciveEncounterGenericReceiptBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as Generic
import DASHI.Law.CoerciveEncounterFixtureCompilerExact as Fixture
import DASHI.Law.CoerciveEncounterLawfulnessProductExact as Product

------------------------------------------------------------------------
-- Repo-wide receipt x-pollination.
--
-- Encounter fixture observations are exported through GenericReceipt only as
-- non-promoting receipts.  A metadata receipt cannot itself close lawfulness.
------------------------------------------------------------------------

fixtureReceipt : Fixture.EncounterFixture → Generic.GenericReceipt
fixtureReceipt f =
  Generic.mkNonPromotingReceipt
    "coercive encounter fixture"
    "DASHI.Law.CoerciveEncounterFixtureCompilerExact"
    (Fixture.encounterId f)
    "record-level encounter fields projected into fail-closed lawfulness and audit obligations"
    "lawfulness still requires every Product.LawfulnessObligationVector coordinate plus provenance closure"
    "agda -i . DASHI/Law/CoerciveEncounterFixtureCompilerExact.agda"

fixtureReceiptNeverPromotes :
  (f : Fixture.EncounterFixture) →
  Generic.promotesClaim (fixtureReceipt f) ≡ false
fixtureReceiptNeverPromotes f = refl

canonicalFixtureGenericReceipt : Generic.GenericReceipt
canonicalFixtureGenericReceipt = Fixture.canonicalMissingSafeguardFixture |> fixtureReceipt
  where
    _|>_ : ∀ {A B : Set} → A → (A → B) → B
    x |> f = f x

canonicalFixtureReceiptNonPromoting :
  Generic.promotesClaim canonicalFixtureGenericReceipt ≡ false
canonicalFixtureReceiptNonPromoting = refl

------------------------------------------------------------------------
-- The lawfulness residual remains visible after generic receipt projection.
------------------------------------------------------------------------

canonicalFixtureResidualSurvivesReceiptProjection :
  Fixture.firstLawfulnessResidual Fixture.canonicalMissingSafeguardFixture
  ≡ Product.firstOpenLawfulnessCoordinate Product.safeguardCoordinate
canonicalFixtureResidualSurvivesReceiptProjection =
  Fixture.canonicalFixtureStopsAtSafeguard
