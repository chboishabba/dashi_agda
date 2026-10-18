from agda_preflight.discovery import (
    classify_surface_role,
    normalized_signature,
    round_family,
    similarity_score,
)


def test_normalized_signature_alpha_normalizes_binders_and_space():
    left = "∀ {A : Set} → (xs : List A) → Nat"
    right = "∀ {B : Set} → (ys : List B) → Nat"
    assert normalized_signature(left) == normalized_signature(right)


def test_surface_role_demotes_round_snapshots():
    assert classify_surface_role("DASHI.Physics.Closure.TheoremInterfaceRound222Exact") == "historical_snapshot"
    assert classify_surface_role("DASHI.Core.FiniteReceiptList") == "canonical"


def test_round_family_extracts_number_without_losing_family_identity():
    family, number = round_family("DASHI.Physics.Closure.NSTriadKNClayFrontierRound222Exact")
    assert family == "DASHI.Physics.Closure.NSTriadKNClayFrontierRound#Exact"
    assert number == 222


def test_similarity_is_deterministic_and_signature_sensitive():
    same = similarity_score(
        name_a="listCount",
        signature_a="List A → Nat",
        refs_a=("Nat", "List"),
        name_b="countList",
        signature_b="List B → Nat",
        refs_b=("List", "Nat"),
    )
    different = similarity_score(
        name_a="listCount",
        signature_a="List A → Nat",
        refs_a=("Nat", "List"),
        name_b="foo",
        signature_b="Bool → Bool",
        refs_b=("Bool",),
    )
    assert 0.0 <= different < same <= 1.0
