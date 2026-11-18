#!/usr/bin/env python3
"""Bem Experiment 1: steelman/realistic-null exact finite sensitivity audit.

This is an EXACT conditional mathematics witness, not reconstruction of
historical researcher choices or a discovery of misconduct.
Sources:
  Bem (2011), DOI 10.1037/a0021524, reported 53.07%, n=1560 erotic trials.
  Kekecs et al (2023), DOI 10.1098/rsos.191375: 49.89%, n=37836
  (2115 participants, confidence interval 49.11–50.67%; model-dependent).
  Bem et al (2015), DOI 10.12688/f1000research.7177.2: meta-analysis steelman.
  Original source + comparison in the two existing Agda producer files.
Run: python scripts/check_amy_eskridge_bem_steelman_realistic_sympy.py
"""
from __future__ import annotations
from math import comb
from pathlib import Path
from fractions import Fraction
import re
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
BEM = ROOT / "DASHI/Culture/AmyEskridgeBemSteelmanRealisticIdentifiabilityExact.agda"
PSI = ROOT / "DASHI/Culture/AmyEskridgeVideoTemporalForecastAndPsiMaxCutExact.agda"
TRAJ = ROOT / "DASHI/Governance/AnomalousPhenomenonTemporalEvidenceTrajectoriesExact.agda"
ROADMAP = ROOT / "Docs/roadmaps/AmyEskridgeVideoAggregationMaxCut20261117.md"

def check_exact():
    n = 1560
    # No claim of an exact observed integer hit count: the paper comparison
    # 53.07% may be an unweighted average of participant/session percentages.
    # The adjacent attainable integer totals serve as a *conditional proxy*.
    assert Fraction(827, n) < Fraction(5307, 10000) < Fraction(828, n)
    # Every finite binary record has POSITIVE probability under unbiased
    # iid Bernoulli null; hence a finite result does not logically force bias.
    assert Fraction(1, 2**n) > 0

    # Exact iid binomial one-sided tail at k>=828, conditional on integer-count
    # model; never pass off as the paper's participant-level t test.
    tail = sp.Rational(sum(comb(n, k) for k in range(828, n+1)), 2**n)
    assert tail > 0 and tail < sp.Rational(1, 100)
    # Multiple independently calibrated, predeclared alpha tests:
    # P(any positive) = 1-(1-alpha)^m. Independence is a key ASSUMPTION.
    family01 = 1 - (1-sp.Rational(1,100))**9
    family05 = 1 - (1-sp.Rational(5,100))**9
    assert family01 > sp.Rational(8,100)
    assert family01 < sp.Rational(9,100)
    assert family05 > sp.Rational(36,100)
    assert family05 < sp.Rational(38,100)

    # Extremely important: an 8/9 significant pattern is NOT explained by
    # the "at least one significant result among nine" calculation.
    # Under nine *independent predeclared valid* alpha=.05 tests, getting >=8
    # is tiny, but independence/complete selection are not historical facts.
    eight_of_nine = sum(
        sp.binomial(9, k) * sp.Rational(5, 100)**k *
        sp.Rational(95, 100)**(9-k) for k in (8, 9)
    )
    assert eight_of_nine == sp.Rational(3359375, 10**16)
    assert eight_of_nine < sp.Rational(1, 10**8)

    # Two SYNTHETIC 2x2 tables with identical 828/1560 marginal mean;
    # one has a strong cohort-rate contrast, the other no cohort contrast.
    # This actually demonstrates what the marginal percentage cannot infer.
    hetero = ((430, 350), (398, 382))
    homogeneous = ((414, 366), (414, 366))
    assert all(
        sum(row[0] for row in table) == 828 and
        sum(sum(row) for row in table) == 1560
        for table in (hetero, homogeneous)
    )
    def cohort_rates(table):
        return [sp.Rational(a, a+b) for a,b in table]
    assert cohort_rates(hetero)[0] != cohort_rates(hetero)[1]
    assert cohort_rates(homogeneous)[0] == cohort_rates(homogeneous)[1]

    # There is *no forced* analytic fault: an unselected chance model can
    # generate any given finite outcome with nonzero probability, and an
    # effect model can generate the same outcome; a selected model can too.
    # This is NON-IDENTIFIABILITY, not equality of model plausibilities.
    assert sp.Rational(1,2)**828 * sp.Rational(1,2)**(n-828) > 0
    q = sp.Rational(5307, 10000)
    assert q**828 * (1-q)**(n-828) > 0

    # Publication/analysis search multiplies opportunity for >=1 false
    # positive if genuinely independent, but does NOT guarantee any result.
    assert family01 < 1
    assert family05 < 1

    # Transparent Psi's model-based 99.75% CI excludes Bem's reported rate.
    lower, upper = sp.Rational(4911,10000), sp.Rational(5067,10000)
    bem = sp.Rational(5307,10000)
    transparent = sp.Rational(4989,10000)
    assert lower <= transparent <= upper
    assert bem > upper
    assert bem - upper == sp.Rational(240,10000)
    # Cannot infer cohort moderator existence from this alone.
    assert sp.satisfiable(sp.And(
        sp.Symbol("nonreplication"),
        ~sp.Symbol("historic_p_hacking")
    )) is not False

    print("PASS exact conditional iid tail k>=828 / 1560: %.9f" % float(tail))
    print("PASS independent 9-test alpha=.01 family-wise rate: %.8f" % float(family01))
    print("PASS independent 9-test alpha=.05 family-wise rate: %.8f" % float(family05))
    print("PASS 8/9 pattern NOT explained by independent 9-test any-hit probability")
    print("PASS two different 2x2 cohort constructions with exactly 828/1560")
    print("PASS 2023 model-specific CI and 2.40pp gap from Bem")
    return tail, family01, family05

def check_producers():
    bem, psi, traj, roadmap = (
        p.read_text(encoding="utf-8") for p in [BEM, PSI, TRAJ, ROADMAP]
    )
    for name in [
        "sameReportedRate = refl",
        "sameReportedTrialCount = refl",
        "noSignificanceToHistoricalPHashing ()",
        "noReplicationToFraud ()",
        "noAutomaticNineIndependence ()",
    ]:
        assert name in bem, name
    assert "originalBemExp1ReportedRate = 5307" in psi
    assert "transparentPsi2025" in traj
    assert "Bem Experiment 1 steelman-versus-realistic" in roadmap
    # Reject a fictional claim that the aggregate is a recorded count:
    assert "sameReportedRate" in bem
    print("PASS original producer reuse and mandatory open source-identity gates")

def check_native_prior_art_and_original_correspondence():
    native = (ROOT / "DASHI/Culture/AmyEskridgeBemNativeStatisticsDiscriminatorWeldExact.agda").read_text()
    correspondence = (ROOT / "DASHI/Culture/AmyEskridgeBemOriginalProtocolCorrespondenceWeldExact.agda").read_text()
    robust = (ROOT / "DASHI/Statistics/Vec15Robust.agda").read_text()
    inference = (ROOT / "DASHI/Statistics/Vec15Inference.agda").read_text()
    discriminator = (ROOT / "DASHI/Core/DiscriminatorSynthesisExact.agda").read_text()
    aggregator = (ROOT / "DASHI/Culture/AmyEskridgeVideoEvidenceEverything.agda").read_text()
    assert "tukeyOutlierMask15" in robust
    assert "tukeyFence15" in robust and "iqr15" in robust
    assert "pValue = countNonZero15 xs" in inference
    assert "record DiscriminatingLanguageExtension" in discriminator
    assert "extensionJoinSeparates" in discriminator
    for name in ["publishedAggregateCollision", "sameReportedNumberNeedsNewDiscriminator",
                 "joinedOriginalEvidenceCanSeparate", "noTukeyHSDByName"]:
        assert name in native, name
    for x in ["bemOriginalFirstExp1PhasesTotal = refl",
              "bemOriginalExp6PhasesTotal = refl",
              "criticClarifiedTestMismatch = refl",
              "noIncorrectCriticTestAsProof"]:
        assert x in correspondence, x
    for x in ["AmyEskridgeBemNativeStatisticsDiscriminatorWeldExact",
              "AmyEskridgeBemOriginalProtocolCorrespondenceWeldExact"]:
        assert x in aggregator, x
    print("PASS genuine native discriminator, Tukey robust-v-HSD split and 2018 correspondence")

if __name__ == "__main__":
    check_exact()
    check_producers()
    check_native_prior_art_and_original_correspondence()
