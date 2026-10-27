from agda_preflight.discovery import similarity_score


def test_missing_signatures_do_not_create_false_high_similarity():
    score = similarity_score(
        name_a="alpha",
        signature_a="",
        refs_a=(),
        name_b="omega",
        signature_b="",
        refs_b=(),
    )
    assert score < 0.2
