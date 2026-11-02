#!/usr/bin/env python3
"""Scenario-only AI capital-cycle stress. Run: python scripts/ai_capital_cycle_network_20261102.py

Provenance: CoreWeave June 2026 SEC 10-Q: six-month operating cash +$3.663bn,
investing cash -$14.874bn, $5.524bn cash, $0.015bn marketable securities,
$10.014bn contingent unused secured-credit availability, $35.6bn debt.
All forward rates, funding caps, GPU refresh shares, delayed receipts,
2027 maturity proxy and sponsor guarantees below are hypothetical.
No across-issuer aggregation, legal debt inference or solvency forecast.
OCF contains baseline leases and existing interest; add only NEW financing
interest and an explicitly assumed refinancing-price difference.
The extra GPU refresh is strictly on top of the projected investing base.
"""
from dataclasses import dataclass, asdict
from math import isclose
import json

ANNUAL_OCF = 7.326
ANNUAL_INVEST = 29.748
CASH = 5.539
UNDRAWN = 10.014
DEBT = 35.6

@dataclass(frozen=True)
class Case:
    name: str
    ocf_growth: float = .50
    invest_growth: float = .20
    ocf_lag_one_year: bool = False
    cash_realization_fraction_after_2028: float = 1.
    incremental_refresh_after_2028: float = 0.
    new_money_interest: float = 0.
    maturity_fraction_2027: float = 0.
    refinance_extra_interest: float = 0.
    line_availability_fraction: float = 1.
    annual_new_money_ceiling: float | None = None
    reserve: float = 1.5
    ocf_advance_normalization: float = 0.

def simulate(c: Case):
    assert 0 <= c.cash_realization_fraction_after_2028 <= 1
    assert 0 <= c.line_availability_fraction <= 1
    assert 0 <= c.reserve <= CASH
    assert 0 <= c.ocf_advance_normalization < ANNUAL_OCF
    available_cash, line_left = CASH-c.reserve, UNDRAWN*c.line_availability_fraction
    line_drawn = other_debt = need_total = cumulative_gap = peak = 0.
    annual = []
    first_block = None
    for year in range(2027,2032):
        t = year-2026
        o_t = max(0,t-1) if c.ocf_lag_one_year else t
        ocf = (ANNUAL_OCF-c.ocf_advance_normalization)*(1+c.ocf_growth)**o_t
        if year >= 2029: ocf *= c.cash_realization_fraction_after_2028
        investment = ANNUAL_INVEST*(1+c.invest_growth)**t
        replacement = c.incremental_refresh_after_2028*investment if year>=2029 else 0.
        new_interest = (line_drawn+other_debt)*c.new_money_interest
        maturity = DEBT*c.maturity_fraction_2027 if year==2027 else 0.
        # Maturity assumed fully rolled: old principal refinance does not
        # become a second investment expense. Only the *incremental* coupon
        # difference is added to OCF, which already includes old interest.
        refi_spread_premium = DEBT*c.maturity_fraction_2027*c.refinance_extra_interest
        gap = investment+replacement+new_interest+refi_spread_premium-ocf
        cumulative_gap += gap
        peak = max(peak,cumulative_gap)
        cash_use = min(available_cash,max(0,gap))
        available_cash -= cash_use
        external_needed = max(0,gap-cash_use)
        draw_line = min(line_left,external_needed)
        line_left -= draw_line
        line_drawn += draw_line
        market_requested = external_needed-draw_line
        market = (min(c.annual_new_money_ceiling,market_requested)
                  if c.annual_new_money_ceiling is not None else market_requested)
        other_debt += market
        need_total += market+draw_line
        unfunded = market_requested-market
        if gap<0: available_cash += -gap
        annual.append({'year':year,'operating_cash':round(ocf,3),
                       'investing':round(investment,3),
                       'extra_gpu_refresh':round(replacement,3),
                       'new_interest':round(new_interest,3),
                       'cash_gap':round(gap,3),
                       'new_secured_draw':round(draw_line,3),
                       'new_other_debt':round(market,3),
                       'continuation_unfunded':round(unfunded,3)})
        if unfunded>1e-9:
            first_block=year
            break  # no extrapolation after financing constraint breaks build
    rollover = DEBT*c.maturity_fraction_2027 if first_block is None or first_block>=2027 else 0.
    return {'case':c.name, 'yearly':annual,'peak_cash_gap':round(peak,3),
            'total_new_money_drawn':round(need_total,3),
            'gross_issuance_with_hypothetical_2027_roll':round(need_total+rollover,3),
            'first_failed_financing_year':first_block,
            'unfunded_amount_first_failure':annual[-1]['continuation_unfunded'] if first_block else 0,
            'credit_line_drawn':round(line_drawn,3),
            'fully_financed_hypothetical_growth':first_block is None,
            'actual_insolvency_established':False}

def project_loss_allocation(debt, collateral_recovery, guarantee_cap, trigger):
    """Separate legal conditional sponsor indemnity from original lender loss."""
    residual=max(0,debt-collateral_recovery)
    paid=min(residual,guarantee_cap) if trigger else 0
    return {'gross_collateral_shortfall':round(residual,3),
            'sponsor_contingent_payment':round(paid,3),
            'lender_loss_after_sponsor':round(residual-paid,3)}

CASES=[
    Case('old_envelope', reserve=CASH,line_availability_fraction=0),
    Case('cash_and_conditional_line'),
    Case('new_12pct_coupon',new_money_interest=.12),
    Case('lag_and_extra_refresh',new_money_interest=.12,
         ocf_lag_one_year=True,incremental_refresh_after_2028=.2),
    Case('lag_refresh_payer_haircut',new_money_interest=.12,
         ocf_lag_one_year=True,incremental_refresh_after_2028=.2,
         cash_realization_fraction_after_2028=.85),
    Case('expensive_capital_and_rollover',new_money_interest=.16,
         ocf_lag_one_year=True,incremental_refresh_after_2028=.2,
         cash_realization_fraction_after_2028=.85,
         maturity_fraction_2027=.17,refinance_extra_interest=.04),
    Case('normalize_advance_cashflow',new_money_interest=.12,
         ocf_advance_normalization=2.730),
    Case('capital_limit_20bn',new_money_interest=.12,annual_new_money_ceiling=20),
    Case('capital_limit_10bn',new_money_interest=.12,annual_new_money_ceiling=10)
]

def check():
    out={c.name:simulate(c) for c in CASES}
    assert isclose(out['old_envelope']['peak_cash_gap'],120.730,abs_tol=.001)
    assert isclose(out['new_12pct_coupon']['peak_cash_gap'],152.994,abs_tol=.001)
    assert isclose(out['lag_and_extra_refresh']['peak_cash_gap'],250.725,abs_tol=.001)
    assert isclose(out['lag_refresh_payer_haircut']['peak_cash_gap'],263.543,abs_tol=.001)
    assert isclose(out['expensive_capital_and_rollover']['peak_cash_gap'],282.413,abs_tol=.001)
    assert out['normalize_advance_cashflow']['peak_cash_gap']>out['new_12pct_coupon']['peak_cash_gap']
    assert out['capital_limit_20bn']['first_failed_financing_year']==2028
    assert out['capital_limit_10bn']['first_failed_financing_year']==2027
    assert isclose(out['expensive_capital_and_rollover']['gross_issuance_with_hypothetical_2027_roll']-out['expensive_capital_and_rollover']['total_new_money_drawn'],6.052,abs_tol=.001)
    assert project_loss_allocation(15,10.5,5,True)['sponsor_contingent_payment']==4.5
    assert project_loss_allocation(15,10.5,5,False)['lender_loss_after_sponsor']==4.5
    return out

if __name__ == '__main__':
    result=check()
    print(json.dumps({'scenarios':[{'name':k,'peak_cash_gap':v['peak_cash_gap'],
       'new_money':v['total_new_money_drawn'],
       'gross_issuance_with_rollover':v['gross_issuance_with_hypothetical_2027_roll'],
       'first_unfunded_year':v['first_failed_financing_year'],
       'unfunded_at_break':v['unfunded_amount_first_failure']} for k,v in result.items()],
       'spv_waterfall':[project_loss_allocation(15,10.5,5,True),
                        project_loss_allocation(15,10.5,5,False)]},indent=2))
