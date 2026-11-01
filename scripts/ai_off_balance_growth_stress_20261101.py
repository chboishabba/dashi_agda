#!/usr/bin/env python3
"""2026-11-01 off-balance AI cash-clock sensitivity. Python 3 stdlib only.

Original issuer observations, NOT an attempt to add unlike liabilities:
* CoreWeave SEC Form 10-Q 2026-06-30, SEC accession 000176962826000366.
  H1 2026 operating +$3.663bn, investing -$14.874bn, financing +$13.985bn.
* Meta SEC Form 10-Q 2026-09-30 000162828026066773:
  not-commenced leases $355.73bn, noncancel commitments $454.52bn,
  debt notes $84bn. The first two categories MAY OVERLAP.
* SoftBank Group 2026-09-24 issued $10bn USD notes:
  $1bn @8.625%, $4.5bn @9.25%, $4.5bn @9.75%, to fund OpenAI tranche.
* SoftBank Group 2026-10-01: $30bn follow-on completed; total $64.6bn.
These calculations are scenarios, not cash-flow forecasts or legal leverage.
"""
from math import isclose

COREWEAVE_H1_OCF = 3.663   # USD bn, six months, original cash flow table
COREWEAVE_H1_INVEST = 14.874  # USD bn, six months, cash used
META_LEASES_NOT_STARTED = 355.73  # USD bn undiscounted amount
META_COMMITMENTS = 454.52       # USD bn, possible overlaps; never sum
META_DEBT_NOTES = 84.00        # USD bn recognised nominal principal
SOFTBANK_NOTES = ((1.0, 0.08625), (4.5, 0.09250), (4.5, 0.09750))


def projected_cash_clocks(operating_growth, investing_growth, years=5):
    """Annualised 2026 H1 reference; future growth starts in 2027."""
    ocf = COREWEAVE_H1_OCF * 2
    invest = COREWEAVE_H1_INVEST * 2
    cumulative_shortfall = 0.0
    peak_funding_need = 0.0
    first_cash_surplus = None
    for offset in range(1, years+1):
        ocf *= 1 + operating_growth
        invest *= 1 + investing_growth
        shortfall = invest - ocf
        cumulative_shortfall += shortfall
        peak_funding_need = max(peak_funding_need, cumulative_shortfall)
        if shortfall <= 0 and first_cash_surplus is None:
            first_cash_surplus = 2026 + offset
    return (round(cumulative_shortfall, 3), round(peak_funding_need, 3),
            first_cash_surplus)


def lease_pv_equal_payments(undiscounted, term_years, discount):
    """Toy hypothetical equal annual rent, immediate start, flat discount."""
    assert term_years >= 1 and 0 < discount < 1
    annual = undiscounted / term_years
    return annual * (1-(1+discount)**(-term_years)) / discount


def softbank_usd_note_coupon():
    """Coupon obligation for *these* ten billion USD notes, excludes EUR."""
    return sum(principal * coupon for principal, coupon in SOFTBANK_NOTES)


def scenario():
    print("META: Q2->Q3 not-started leases USD bn:",
          round(META_LEASES_NOT_STARTED-278.99, 3))
    print("META: 355.73/84 ratio is a cross-definition alert, NOT leverage:",
          round(META_LEASES_NOT_STARTED / META_DEBT_NOTES, 3))
    print("META: noncancel commitments not added to leases:", META_COMMITMENTS)
    print("COREWEAVE: H1 operating less investing, USD bn:",
          round(COREWEAVE_H1_OCF-COREWEAVE_H1_INVEST, 3))
    print("COREWEAVE: ratio cash used investing / OCF:",
          round(COREWEAVE_H1_INVEST/COREWEAVE_H1_OCF, 3))
    print("COREWEAVE: liquidity $15.553bn includes $10.014bn debt capacity")
    for og, ig in ((.30,0), (.50,0), (.50,.20), (.75,.20), (1.,.20)):
        print("GROWTH", og, ig, "cumulative/peak funding and surplus year",
              projected_cash_clocks(og,ig))
    for years in (15,20,25):
        for rate in (.05,.08,.12):
            print("HYPOTHETICAL lease PV", years, rate,
                  round(lease_pv_equal_payments(META_LEASES_NOT_STARTED,years,rate),3))
    print("SOFTBANK actual annual USD-note coupon $bn:",
          round(softbank_usd_note_coupon(), 6))
    print("SOFTBANK weighted coupon:", round(softbank_usd_note_coupon()/10, 6))
    assert isclose(COREWEAVE_H1_INVEST - COREWEAVE_H1_OCF, 11.211)
    assert isclose(softbank_usd_note_coupon(), .94125)
    assert isclose(projected_cash_clocks(.5,.2)[0],120.733, abs_tol=.001)
    assert projected_cash_clocks(.5,0)[1] > projected_cash_clocks(.5,0)[0]
    assert round(lease_pv_equal_payments(355.73,20,.08),2) == 174.63
    assert isclose(META_LEASES_NOT_STARTED-278.99,76.74)


if __name__ == "__main__":
    scenario()
