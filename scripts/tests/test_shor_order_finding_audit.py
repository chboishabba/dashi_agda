from scripts.shor_order_finding_audit import (
    audit_modulus,
    multiplicative_order,
    shor_attempt,
)


def test_exact_orders_for_agda_witnesses() -> None:
    assert multiplicative_order(2, 15) == 4
    assert multiplicative_order(2, 21) == 6


def test_shor_split_for_15() -> None:
    attempt = shor_attempt(15, 2)
    assert attempt.success is True
    assert attempt.half_power == 4
    assert attempt.minus_factor == 3
    assert attempt.plus_factor == 5


def test_shor_split_for_21() -> None:
    attempt = shor_attempt(21, 2)
    assert attempt.success is True
    assert attempt.half_power == 8
    assert attempt.minus_factor == 7
    assert attempt.plus_factor == 3


def test_non_coprime_base_is_not_order_finding_input() -> None:
    attempt = shor_attempt(15, 3)
    assert attempt.coprime is False
    assert attempt.order is None
    assert attempt.success is False


def test_audit_has_successful_bases() -> None:
    report = audit_modulus(35, range(2, 13))
    assert report["attempt_count"] == 11
    assert report["success_count"] > 0
