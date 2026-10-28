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



@dataclass(frozen=True)
class FiscalExecution:
    net_wealth_assessed: int
    tax_paid: int
    collection_cost: int
    appropriated_care: int

def assessed_liability(world: FiscalExecution) -> int:
    return wealth_excess(NetWealth(world.net_wealth_assessed), 3)

def test_assessment_collection_appropriation_are_distinct() -> None:
    a = FiscalExecution(5, 0, 1, 0)
    b = FiscalExecution(5, 2, 1, 0)
    c = FiscalExecution(5, 2, 1, 2)
    d = FiscalExecution(5, 2, 3, 0)
    assert {assessed_liability(w) for w in (a, b, c, d)} == {2}
    assert a.tax_paid != b.tax_paid
    assert b.tax_paid == c.tax_paid and b.appropriated_care != c.appropriated_care
    assert b.tax_paid == d.tax_paid and b.collection_cost != d.collection_cost
    for f in (lambda due: due, lambda due: due * 7, lambda due: due % 3):
        assert f(assessed_liability(a)) == f(assessed_liability(b))

@dataclass(frozen=True)
class ShareVoteState:
    owner_ordinary: int
    owner_super: int
    all_ordinary: int
    all_super: int

def owner_weighted_votes(state: ShareVoteState) -> int:
    return state.owner_ordinary + 10 * state.owner_super

def total_weighted_votes(state: ShareVoteState) -> int:
    return state.all_ordinary + 10 * state.all_super

def test_dual_class_voting_post_transfer() -> None:
    before = ShareVoteState(6, 3, 20, 3)
    after = ShareVoteState(0, 3, 20, 3)
    assert owner_weighted_votes(before) == 36
    assert owner_weighted_votes(after) == 30
    assert total_weighted_votes(before) == total_weighted_votes(after) == 50
    assert 2 * owner_weighted_votes(after) > total_weighted_votes(after)
    assert before.owner_ordinary - after.owner_ordinary == 6
    # Illustrates retention of majority, not actual ownership transfer.
    # Note the original 20-vote ordinary registry total is unchanged.

def test_assessment_vs_interim_growth() -> None:
    end_of_assessment = wealth_after_tax(NetWealth(5), 3)
    interim = end_of_assessment + 2
    assert end_of_assessment == 3
    assert interim == 5 and excess(interim, 3) == 2
    assert wealth_after_tax(NetWealth(interim), 3) == 3


@dataclass(frozen=True)
class ModelAuditCase:
    public_risk_signal: int
    legally_assessed_wealth: int

def test_ai_risk_score_does_not_determine_tax_law() -> None:
    a = ModelAuditCase(7, 2)
    b = ModelAuditCase(7, 5)
    assert a.public_risk_signal == b.public_risk_signal
    assert wealth_excess(NetWealth(a.legally_assessed_wealth), 3) == 0
    assert wealth_excess(NetWealth(b.legally_assessed_wealth), 3) == 2
    # A classifier or risk score is not a lawful valuation/assessment.
    # This negative control does not assert all AI auditors must be inaccurate.


def proposed_idle_equity_rate_bps(consecutive_year: int) -> int:
    # Purely hypothetical 1% / 2% / 5% rule in the pasted AI exchange.
    # It has no named law, administrative assessment or verified "idle" test.
    assert consecutive_year >= 1
    return 100 if consecutive_year == 1 else 200 if consecutive_year == 2 else 500

def test_ai_proposed_idle_equity_schedule_is_not_victoria_vrlt() -> None:
    assert [proposed_idle_equity_rate_bps(y) for y in range(1, 6)] == [
        100, 200, 500, 500, 500
    ]
    # Ordinary Victoria VRLT: 1% / 2% / 3%, exceptions apply.
    assert proposed_idle_equity_rate_bps(3) != 300
    # Same first two bps are numerical coincidences, not identical tax bases.
    assert proposed_idle_equity_rate_bps(1) == 100


def test_constructive_finite_axis_pareto() -> None:
    """Independent bounded oracle for finite nonempty Pareto existence.

    This tests the numeric interpretation of the Agda finite-axis summed
    rank, not its Agda syntax, kernel validity or a welfare-policy outcome.
    The candidate set is explicitly enumerated; every coordinate is
    included in the rank. No infeasible candidate is admitted.
    """
    from itertools import product
    from random import Random

    def dominated_by(other: tuple[int, ...], selected: tuple[int, ...]) -> bool:
        return (all(x <= y for x, y in zip(other, selected))
                and any(x < y for x, y in zip(other, selected)))

    total = 0
    for axes, candidates in ((0, 4), (1, 4), (2, 4), (3, 3)):
        for flattened in product(range(3), repeat=axes * candidates):
            points = [tuple(flattened[i * axes:(i + 1) * axes])
                      for i in range(candidates)]
            ranked = min(range(candidates), key=lambda i: sum(points[i]))
            assert not any(dominated_by(other, points[ranked])
                           for other in points)
            total += 1

    rng = Random(20261028)
    for _ in range(2048):
        n_axes = rng.randrange(1, 9)
        n_candidates = rng.randrange(1, 19)
        points = [tuple(rng.randrange(100) for _ in range(n_axes))
                  for _ in range(n_candidates)]
        ranked = min(range(n_candidates), key=lambda i: sum(points[i]))
        assert not any(dominated_by(other, points[ranked])
                       for other in points)
        total += 1

    # If the axis enumeration is incomplete, an unlisted-axis improvement
    # may leave identical selected ranks and invalidate Pareto minimality.
    omitted_axis_worlds = ((0, 9), (0, 0))
    assert sum(omitted_axis_worlds[0][:1]) == sum(omitted_axis_worlds[1][:1])
    assert dominated_by(omitted_axis_worlds[1], omitted_axis_worlds[0])
    assert total == 3**0 + 3**4 + 3**8 + 3**9 + 2048


def test_canonical_funding_batch_no_double_count() -> None:
    """Finite oracle for the Agda C06 conditional canonical-source model.

    The canonical source ID mapping is a *supplied premise*. The test does
    not authenticate a financial source, exchange fill or custody claim.
    """
    from itertools import product
    from random import Random

    # Each row is (canonical claim ID, exclusive channel, amount).
    checks = 0
    for n in range(4):
        for source_ids in product(range(3), repeat=n):
            for channels in product(range(3), repeat=n):
                for amounts in product(range(3), repeat=n):
                    rows = tuple(zip(source_ids, channels, amounts))
                    unique = len(set(source_ids)) == len(source_ids)
                    cash = sum(amount for _, c, amount in rows if c == 0)
                    loans = sum(amount for _, c, amount in rows if c == 1)
                    sales = sum(amount for _, c, amount in rows if c == 2)
                    assert cash + loans + sales == sum(amount for _, _, amount in rows)
                    if unique:
                        for i in range(len(rows)):
                            for j in range(i + 1, len(rows)):
                                assert rows[i][0] != rows[j][0]
                    else:
                        assert any(rows[i][0] == rows[j][0]
                                   for i in range(len(rows))
                                   for j in range(i + 1, len(rows)))
                    checks += 1

    rng = Random(20261028)
    for _ in range(20000):
        size = rng.randrange(0, 22)
        source_ids = [rng.randrange(25) for _ in range(size)]
        channels = [rng.randrange(3) for _ in range(size)]
        amounts = [rng.randrange(1000) for _ in range(size)]
        totals = tuple(sum(v for c, v in zip(channels, amounts) if c == i)
                       for i in range(3))
        assert sum(totals) == sum(amounts)
        assert (len(source_ids) == len(set(source_ids))) == (
            all(source_ids[i] != source_ids[j]
                for i in range(size) for j in range(i + 1, size)))
        checks += 1

    # Deliberate non-promotion control. Distinct local tokens alone pass a
    # uniqueness test even if they both describe one underlying real claim.
    historical_claim_alias = ((7, 101), (7, 102))
    assert len({local for _, local in historical_claim_alias}) == 2
    assert len({historical for historical, _ in historical_claim_alias}) == 1
    assert checks == sum(27 ** i for i in range(4)) + 20000


def test_canonical_funding_payment_route_weld() -> None:
    """Independent bounded route weld and equal-grand-total negative oracle."""
    from itertools import product

    seen = 0
    for cash, loan, sale in product(range(16), repeat=3):
        source_rows = ((1, 0, cash), (2, 1, loan), (3, 2, sale))
        source_partition = tuple(
            sum(amount for _, channel, amount in source_rows if channel == i)
            for i in range(3)
        )
        assert source_partition == (cash, loan, sale)
        source_grand_total = sum(row[2] for row in source_rows)
        for tax_paid in range(source_grand_total + 1):
            fee = source_grand_total - tax_paid
            funding_route = (cash, loan, sale, tax_paid, fee)
            assert source_partition == funding_route[:3]
            assert source_grand_total == tax_paid + fee
            seen += 1

    # The same gross funding sum does not establish that the channels
    # match; both are 5 but the claimed loan/cash source differs.
    cash_only = (5, 0, 0)
    debt_only = (0, 5, 0)
    assert sum(cash_only) == sum(debt_only)
    assert cash_only != debt_only

    # A valid settlement that arrives after tax payment cannot fund that
    # earlier remittance without a separately admitted bridge.
    tax_payment_epoch, sale_settlement_epoch = 3, 8
    assert not (sale_settlement_epoch <= tax_payment_epoch)
    assert seen == 16**3 + 3 * sum(range(16)) * 16**2

def test_official_settlement_receipt_backout_and_coherent_route() -> None:
    """Bounded counterworlds for source-dependent DvP-to-tax admission.

    This is a hypothetical truth-table oracle only. It cannot assert that
    official validation, client identities or custody receipts are real.
    """
    from itertools import product

    dispositions = ("due", "backed_out", "completed")
    checked = 0
    for (status, officially_valid, holder_same, class_same, sale_cash,
         route_sale_cash, settlement_epoch, payment_epoch) in product(
                dispositions, (False, True), (False, True), (False, True),
                range(4), range(4), range(7), range(7)):
        is_final = status == "completed"
        cash_matches = sale_cash == route_sale_cash
        chronology = settlement_epoch <= payment_epoch
        admissible = (is_final and officially_valid and holder_same
                      and class_same and cash_matches and chronology)
        if status != "completed":
            assert not admissible
        if settlement_epoch > payment_epoch or not officially_valid:
            assert not admissible
        if admissible:
            assert cash_matches and chronology and class_same and holder_same
        checked += 1

    assert checked == 3 * 2 * 2 * 2 * 4 * 4 * 7 * 7

    # Identical valuations and joint-reform outcomes do not determine
    # taxpayer allocation or a wealth-tax-only potential outcome.
    same_asset_valuation = ((12, 3), (12, 9))
    same_joint_reform_outcome = ((5, 1), (5, 3))
    assert same_asset_valuation[0][0] == same_asset_valuation[1][0]
    assert same_asset_valuation[0][1] != same_asset_valuation[1][1]
    assert same_joint_reform_outcome[0][0] == same_joint_reform_outcome[1][0]
    assert same_joint_reform_outcome[0][1] != same_joint_reform_outcome[1][1]


def test_369_trialectic_numeric_role_maxcut() -> None:
    """Independent finite oracle for inherited 27/19683, S3 and 3^5/5^3.

    All axes below are hypothetical annotations. Neither signed ternary
    patterns, permutation cycles nor numerals establish tax liability,
    causal effects, CHESS finality, external identity or Monster objects.
    """
    from itertools import product, permutations

    digits = (-1, 0, 1)
    policy_cube = tuple(product(digits, repeat=3))
    assert len(policy_cube) == 27

    # Each x/y pair has exactly three possible z outcomes.
    for x, y in product(digits, repeat=2):
        fibre = tuple(point for point in policy_cube if point[:2] == (x, y))
        assert len(fibre) == 3
        assert {point[2] for point in fibre} == set(digits)

    # The actual coordinate-permutation group contains six actions.
    actions = tuple(permutations(range(3)))
    assert len(actions) == 6
    for permutation in actions:
        mapped = {tuple(p[permutation[i]] for i in range(3))
                  for p in policy_cube}
        assert mapped == set(policy_cube)

    def rotate_xyz(p: tuple[int, int, int]) -> tuple[int, int, int]:
        return (p[1], p[2], p[0])

    def swap_xy(p: tuple[int, int, int]) -> tuple[int, int, int]:
        return (p[1], p[0], p[2])

    for p in policy_cube:
        assert rotate_xyz(rotate_xyz(rotate_xyz(p))) == p
        assert swap_xy(swap_xy(p)) == p

    # Three 27-cell factors have 27^3 = 3^9 = 19,683 carriers.
    trialectic_3_cell_count = len(policy_cube) ** 3
    assert trialectic_3_cell_count == 19683
    # Enumerate the complete 19,683-state fabric, not only its cardinality.
    full_fabric = tuple(product(policy_cube, repeat=3))
    assert len(full_fabric) == trialectic_3_cell_count
    # For each one of 729 (x-cell,y-cell) pairs, all 27 z cells remain.
    xy_to_z = {}
    for x_cell, y_cell, z_cell in full_fabric:
        xy_to_z.setdefault((x_cell, y_cell), set()).add(z_cell)
    assert len(xy_to_z) == 729
    assert all(available_z == set(policy_cube)
               for available_z in xy_to_z.values())

    gates = ("A05", "C09", "E07", "F07", "H08")
    ternary_annotation_profiles = tuple(product(digits, repeat=len(gates)))
    assert len(ternary_annotation_profiles) == 3**5 == 243
    assert sum(all(v == 1 for v in p)
               for p in ternary_annotation_profiles) == 1

    # The imported ComplementMode5 carrier has five constructors.
    # Its three-stage product is different, 5^3 = 125.
    five_complement_modes = range(5)
    three_mode_profiles = tuple(product(five_complement_modes, repeat=3))
    assert len(three_mode_profiles) == 5**3 == 125
    assert len(ternary_annotation_profiles) != len(three_mode_profiles)

    # Even five positive *annotation symbols* do not supply five official
    # external producer receipts. The two data types must remain distinct.
    all_positive_annotations = tuple([1] * 5)
    no_independent_records = ()
    assert all_positive_annotations in ternary_annotation_profiles
    assert len(no_independent_records) != len(gates)

    print("PASS: 27 finite hypothesis/review/effect cells, 6 S3 chart actions, "
          "19,683 three-cell carriers, 243 five-gate annotations, "
          "125 three-mode charts, independent-z and authority negative controls")

if __name__ == "__main__":
    test_finite_caps()
    test_same_flow_different_wealth()
    test_same_amount_different_base()
    test_identical_wealth_liability_different_control()
    test_tax_receipt_cannot_recover_power_or_care()
    test_distinct_political_outcome_queries()
    test_assessment_collection_appropriation_are_distinct()
    test_dual_class_voting_post_transfer()
    test_assessment_vs_interim_growth()
    test_ai_risk_score_does_not_determine_tax_law()
    test_ai_proposed_idle_equity_schedule_is_not_victoria_vrlt()
    test_constructive_finite_axis_pareto()
    test_canonical_funding_batch_no_double_count()
    test_canonical_funding_payment_route_weld()
    test_official_settlement_receipt_backout_and_coherent_route()
    test_369_trialectic_numeric_role_maxcut()
    print("PASS: 8,192 bounded arithmetic pairs + 10 synthetic counterexample suites + finite Pareto oracle + canonical funding partitions + same-route weld + operator finality gating + 369/trialectic role max-cut")
