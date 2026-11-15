#!/usr/bin/env python3
"""Contract-specific DDTL 3.0 priority experiment, NOT a legal cash forecast.

Original issuer/legal source:
CoreWeave, 2025-07-28 DDTL 3.0 agreement, Section 2.20(b)(i)-(viii):
https://www.sec.gov/Archives/edgar/data/1769628/000176962825000033/coreweave30-ex101xtermlo.htm
2025-12-31 amendment to CRR definition and 0.85 floor:
https://www.sec.gov/Archives/edgar/data/1769628/000176962826000104/ex10311.htm
Original author/finance-prior owner: separate draft PR #1101
AICoreWeaveOpenAIDDTL3CashHardwareWeld20261016Exact and
AICoreWeaveOpenAIContractRealisationCure20261016Exact.
This is an independent governance-facing ordering consumer, not a copy of
those modules or an assertion of observed customer payment / covenant result.

Amounts use synthetic USD millions (not real DDTL3 monthly balances).
The agreement imposes timing/conditions and secondary Interparty waterfalls
not reproduced here; this is a bounded ONE-PAYMENT-DATE priority projection.
"""
from dataclasses import dataclass, asdict
from decimal import Decimal
import json

D=Decimal
def usd(x):
    y=D(str(x))
    if y < 0 or not y.is_finite(): raise ValueError("invalid amount")
    return y

STAGES=(
  "first_eligible_opex",
  "second_fees",
  "third_interest_and_swap",
  "fourth_liquidity_topup",
  "fifth_principal_and_swap_termination",
  "sixth_conditional_cash_trap",
  "seventh_conditional_other_opex_capex",
  "eighth_distribution_reserve",
)

@dataclass(frozen=True)
class Receipts:
    actual_independent_customer_cash: Decimal
    parent_contributed_cash: Decimal
    account_transfers_and_other_proceeds: Decimal
    def __post_init__(self):
        for x in asdict(self).values(): usd(x)
    @property
    def cash_in_account(self):
        return sum(asdict(self).values(), D(0))

@dataclass(frozen=True)
class Claims:
    eligible_opex: Decimal
    agent_fees: Decimal
    loan_interest_and_swap: Decimal
    liquidity_topup: Decimal
    principal_and_swap_termination: Decimal
    cash_trap_request: Decimal
    other_opex_capex: Decimal
    cash_trap_event: bool = False
    opex_payment_condition: bool = False
    distribution_conditions_satisfied: bool = False
    def __post_init__(self):
        for k,v in asdict(self).items():
            if not isinstance(v, bool): usd(v)

def waterfall(rec: Receipts, c: Claims):
    left=rec.cash_in_account
    disbursed={}
    def pay(key,amount):
        nonlocal left
        amount=min(left,amount)
        disbursed[key]=amount
        left-=amount
    # DDTL3 §2.20(b)(i) has an initial $50m / calendar-month cap;
    # other eligible spending is separately conditioned at stage (vii).
    pay(STAGES[0], min(c.eligible_opex,D("50")))
    pay(STAGES[1],c.agent_fees)
    pay(STAGES[2],c.loan_interest_and_swap)
    pay(STAGES[3],c.liquidity_topup)
    pay(STAGES[4],c.principal_and_swap_termination)
    pay(STAGES[5],c.cash_trap_request if c.cash_trap_event else D(0))
    pay(STAGES[6],c.other_opex_capex if c.opex_payment_condition else D(0))
    pay(STAGES[7],left)
    # A distribution-reserve TRANSFER is not an actual company dividend.
    # §2.20(d) grants a conditional withdrawal capability, not automatic cash.
    reserve=disbursed[STAGES[7]]
    permitted_release=reserve if c.distribution_conditions_satisfied else D(0)
    assert sum(disbursed.values(),D(0))==rec.cash_in_account
    return {'deposit':rec.cash_in_account, 'stages':disbursed,
            'distribution_reserve':reserve,
            'conditional_eligible_release_ceiling':permitted_release,
            'actual_company_dividend_observed':False,
            'independent_cash':rec.actual_independent_customer_cash,
            'parent_cash':rec.parent_contributed_cash}

def crr(billed_and_received_without_double_counting, equity_cure, projected):
    """Amended contractual ratio *proxy*; billed is not synonymous with cash."""
    b=usd(billed_and_received_without_double_counting)
    e=usd(equity_cure)
    p=usd(projected)
    if p==0: return None  # original clause has its own zero denominator rule
    return (b+e)/p

def compare_synthetic_worlds():
    ratio_a=crr(85,0,100)
    ratio_b=crr(80,5,100)
    assert ratio_a==ratio_b==D(".85")
    zero=d=Receipts(D(0),D(85),D(0))
    external=Receipts(D(85),D(0),D(0))
    c=Claims(D(12),D(2),D(20),D(10),D(30),
             D(0),D(15),False,False,False)
    x=waterfall(zero,c);y=waterfall(external,c)
    assert x['deposit']==y['deposit']==D(85)
    assert x['stages']==y['stages']
    assert x['independent_cash']==0 and y['independent_cash']==85
    assert x['conditional_eligible_release_ceiling']==0
    assert sum(x['stages'].values(),D(0))==85
    # More parent deposits or a reported ratio never establish terminal demand.
    assert crr(85,0,100)==crr(80,5,100)
    # Explicit contractual cash trapping consumes residual before conditional
    # capex and reserve allocation when a trap is assumed to be triggered.
    trapped=waterfall(external,Claims(D(10),D(2),D(5),D(2),D(5),
                          D(30),D(18),True,True,False))
    untrapped=waterfall(external,Claims(D(10),D(2),D(5),D(2),D(5),
                          D(30),D(18),False,True,False))
    assert trapped['stages'][STAGES[5]]==D(30)
    assert untrapped['stages'][STAGES[5]]==D(0)
    assert trapped['distribution_reserve']<untrapped['distribution_reserve']
    assert all(trapped['stages'][STAGES[i]]>=0 for i in range(8))
    allow=waterfall(external,Claims(D(10),D(2),D(5),D(2),D(5),
                          D(0),D(18),False,True,True))
    assert allow['conditional_eligible_release_ceiling']==allow['distribution_reserve']
    assert not allow['actual_company_dividend_observed']
    return {'crr_same_value':str(ratio_a),
            'cure_world_numerator_equity':5,
            'same_account_total':str(x['deposit']),
            'same_waterfall_different_terminal_cash':True,
            'first_operating_cost_cap':"50 USDm per calendar month",
            'with_cash_trap_reserve':str(trapped['distribution_reserve']),
            'without_cash_trap_reserve':str(untrapped['distribution_reserve']),
            'automatic_distribution_proved':False}

def floating_rate_basis_stress_assuming_effective_hedge(
        assumed_drawn_usd_bn, rate_shock, hedge_notional_fraction,
        effective_hedge_fraction=1):
    """Pure conditional exposure, not actual DDTL 3.0 outstanding or hedge P&L.

    DDTL3 §5.23 requires hedging notional >=75% of reasonably projected
    outstanding FLOATING-rate loan principal at specified dates. Actual
    swaps/caps, basis, resets, drawdowns and maturities must be verified.
    """
    loan=usd(assumed_drawn_usd_bn)
    shock=usd(rate_shock)
    coverage=usd(hedge_notional_fraction)
    effective=usd(effective_hedge_fraction)
    if coverage>1 or effective>1: raise ValueError("invalid hedge fraction")
    return loan*shock*(D(1)-coverage*effective)


if __name__ == "__main__":
    print(json.dumps(compare_synthetic_worlds(),indent=2))
