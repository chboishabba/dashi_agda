#!/usr/bin/env python3
"""Bounded executable checks for the tax-base separation module.

DASHI source-written finite examples: research direction Johl Brown,
with OpenAI ChatGPT assistance (2026-10-27). Independent Python checks
are NOT Agda kernel verification, empirical incidence models or evidence
for any government's realized revenue.
"""

from dataclasses import dataclass

@dataclass(frozen=True)
class Income:
    units: int

@dataclass(frozen=True)
class NetWealth:
    units: int

def excess(value: int, threshold: int) -> int:
    assert value >= 0 and threshold >= 0
    return max(0, value - threshold)

def income_excess(income: Income, threshold: int) -> int:
    return excess(income.units, threshold)

def wealth_excess(stock: NetWealth, threshold: int) -> int:
    return excess(stock.units, threshold)

def wealth_after_tax(stock: NetWealth, threshold: int) -> int:
    return stock.units - wealth_excess(stock, threshold)

def test_finite_caps() -> None:
    for threshold in range(64):
        for wealth in range(64):
            asset = NetWealth(wealth)
            assert wealth_after_tax(asset, threshold) == min(wealth, threshold)
            assert wealth_excess(asset, threshold) == wealth - min(wealth, threshold)
            assert wealth_excess(asset, threshold) >= 0
        for pay in range(64):
            assert income_excess(Income(pay), threshold) == max(0, pay-threshold)

def test_same_flow_different_wealth() -> None:
    income = Income(2)
    wealth_a = NetWealth(4)
    wealth_b = NetWealth(7)
    assert income_excess(income, 2) == 0
    assert wealth_excess(wealth_a, 2) == 2
    assert wealth_excess(wealth_b, 2) == 5
    assert wealth_excess(wealth_a, 2) != wealth_excess(wealth_b, 2)

@dataclass(frozen=True)
class OwnershipSnapshot:
    net_wealth: int
    voting_rights: int

def test_identical_wealth_liability_different_control() -> None:
    a = OwnershipSnapshot(5, 1)
    b = OwnershipSnapshot(5, 7)
    assert wealth_excess(NetWealth(a.net_wealth), 3) == wealth_excess(NetWealth(b.net_wealth), 3)
    assert a.voting_rights != b.voting_rights

def test_same_amount_different_base() -> None:
    assert income_excess(Income(5), 3) == wealth_excess(NetWealth(5), 3) == 2
    assert Income(5) != NetWealth(5)


@dataclass(frozen=True)
class FiscalSocialWorld:
    assessed_wealth: int
    controlling_votes: int
    accessible_care_capacity: int

def tax_receipt(world: FiscalSocialWorld) -> int:
    return wealth_excess(NetWealth(world.assessed_wealth), 3)

def test_tax_receipt_cannot_recover_power_or_care() -> None:
    # The SAME receipt answers tax-due, but NOT voting or care.
    a = FiscalSocialWorld(5, 1, 0)
    b = FiscalSocialWorld(5, 7, 0)
    c = FiscalSocialWorld(5, 1, 9)
    assert tax_receipt(a) == tax_receipt(b) == tax_receipt(c) == 2
    assert a.controlling_votes != b.controlling_votes
    assert a.accessible_care_capacity != c.accessible_care_capacity
    # Negative control for arbitrary tax-only rechartings.
    for transform in (lambda tax: tax, lambda tax: tax * 2,
                      lambda tax: tax % 2, lambda tax: "paid"):
        assert transform(tax_receipt(a)) == transform(tax_receipt(b))
        assert transform(tax_receipt(a)) == transform(tax_receipt(c))

def test_distinct_political_outcome_queries() -> None:
    a = FiscalSocialWorld(5, 1, 0)
    b = FiscalSocialWorld(5, 7, 0)
    c = FiscalSocialWorld(5, 1, 9)
    queries = {
        "tax_due": tax_receipt,
        "voting_control": lambda w: w.controlling_votes,
        "care_provision": lambda w: w.accessible_care_capacity,
    }
    assert queries["tax_due"](a) == queries["tax_due"](b) == queries["tax_due"](c)
    assert queries["voting_control"](a) != queries["voting_control"](b)
    assert queries["care_provision"](a) != queries["care_provision"](c)

if __name__ == "__main__":
    test_finite_caps()
    test_same_flow_different_wealth()
    test_same_amount_different_base()
    test_identical_wealth_liability_different_control()
    test_tax_receipt_cannot_recover_power_or_care()
    test_distinct_political_outcome_queries()
    print("PASS: 8,192 finite cap observations + five synthetic logical checks")
