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

if __name__ == "__main__":
    test_finite_caps()
    test_same_flow_different_wealth()
    test_same_amount_different_base()
    test_identical_wealth_liability_different_control()
    print("PASS: 8,192 finite cap observations + three typed counterexamples")
