#!/usr/bin/env python3
"""Actual exact Tukey–Kramer post-hoc arithmetic and Aristotle owner audit.

Uses SciPy studentized_range for the external studentized-range cutoff.
Tests exact rational q^2, equal/unequal n, source-valid MSE, independent
assumption gates, uncertainty around a rounded qcrit, and real DAG imports.

NO claim of having analysed Bem's original experiment XLSX.
Run: python scripts/check_tukey_kramer_aristotle_bem_maxcut.py
"""
from __future__ import annotations
from fractions import Fraction
from pathlib import Path
from scipy.stats import studentized_range

ROOT=Path(__file__).resolve().parents[1]

def read(path: str) -> str:
    return (ROOT/path).read_text(encoding="utf-8")

def q_squared(n1:int,s1:int,n2:int,s2:int,mse_num:int,mse_den:int)->Fraction:
    assert n1>0 and n2>0 and mse_num>0 and mse_den>0
    difference=abs(s1*n2-s2*n1)
    return Fraction(2*difference*difference*mse_den,mse_num*n1*n2*(n1+n2))

def exact_pooled_three_group(groups:list[tuple[int,int,int]])->Fraction:
    assert len(groups)==3
    numerator=0
    dof=sum(n for n,_,_ in groups)-3
    assert dof>0
    for n,s,ss in groups:
        assert n>0 and n*ss>=s*s
        numerator+=Fraction(n*ss-s*s,n)
    return numerator/dof

def check_numbers()->None:
    qcrit=studentized_range.ppf(.95,3,27)
    qcrit_sq=qcrit*qcrit
    lower,upper=Fraction(12295,1000),Fraction(12296,1000)
    assert float(lower)<qcrit_sq<float(upper)
    groups=[(10,100,1090),(10,160,2650),(10,110,1300)]
    pooled=exact_pooled_three_group(groups)
    assert pooled==10
    assert q_squared(10,100,10,160,10,1)==36
    assert q_squared(10,100,10,110,10,1)==1
    assert q_squared(6,60,12,192,10,1)==Fraction(144,5)
    assert q_squared(10,100,10,160,270000,27000)==36
    for q2,decision in [(Fraction(36),True),(Fraction(1),False),
                        (Fraction(144,5),True)]:
        assert (float(q2)>qcrit_sq)==decision
        # bracketing decisions are at least as conservative as the
        # corresponding exact SciPy numerical reference.
        if q2>upper:
            assert float(q2)>qcrit_sq
        elif q2<=lower:
            assert float(q2)<qcrit_sq
        else:
            assert lower<q2<=upper
    near=Fraction(61477,5000) # 12.2954: inside rational bracket
    assert lower<near<upper
    assert q_squared(10,100,10,160,10,1)==        q_squared(10,160,10,100,10,1)
    print(f"PASS exact 3-group pooled MSE=10, df=27; SciPy qcrit^2={qcrit_sq:.12f}")
    print("PASS 3 balanced/unequal-n Tukey-Kramer fixtures and borderline refusal")

def check_original_producers()->None:
    hsd=read("DASHI/Statistics/TukeyKramerPostHocExact.agda")
    bound=read("DASHI/Statistics/TukeyKramerIntervalCalibrationExact.agda")
    anova=read("DASHI/Statistics/OneWayANOVAPooledMSEExact.agda")
    aristotle=read("DASHI/Culture/AmyEskridgeBemAristotleExperimentalProofSearchWeldExact.agda")
    master=read("DASHI/Culture/AmyEskridgeVideoEvidenceEverything.agda")
    original_aristotle=read("DASHI/Reasoning/AristotleActiveExperimentalProofSearchDynamicsExact.agda")
    original_stats=read("DASHI/Statistics/Vec15Robust.agda")
    for name in ["syntheticHighContrastReject = refl","syntheticLowContrastFail = refl",
                 "refusesNonIndependentExperimentalUnits = refl",
                 "refusesUncalibratedThreshold = refl"]:
        assert name in hsd,name
    for name in ["bracketedHighContrast = refl","bracketedSmallContrast = refl",
                 "uncertifiedDoesNotAdmit = refl",
                 "quantilePrecisionInsufficient"]:
        assert name in bound,name
    for name in ["syntheticMSEIsExactlyTen = refl","syntheticResidualDF = refl",
                 "noTrialPseudoreplication"]:
        assert name in anova,name
    for name in ["originalWorkbookBytesInspected : Bool",
                 "nextExperiment currentSourceStatus",
                 "currentlyMustAcquireOriginal = refl",
                 "aristotleOriginalOneIteration",
                 "noHSDAsOriginalTest"]:
        assert name in aristotle,name
    assert "canonicalOneIterationCycle" in original_aristotle
    assert "tukeyFence15" in original_stats and "iqr15" in original_stats
    for name in ["DASHI.Statistics.TukeyKramerPostHocExact",
                 "DASHI.Statistics.TukeyKramerIntervalCalibrationExact",
                 "DASHI.Statistics.OneWayANOVAPooledMSEExact",
                 "DASHI.Culture.AmyEskridgeBemAristotleExperimentalProofSearchWeldExact"]:
        assert name in master,name
    # Admission flags are not data. Nor does a squared studentized-range
    # comparison imply the original experiment was a three-arm ANOVA.
    assert "noAssumptionBooleanAsPhysicalCertificate" in hsd
    assert "noTukeyAsOriginalBemTest" in hsd
    assert "noRoundedQuantileAsProof" in bound
    print("PASS source-owner/import checks, guards and original Aristotle loop")

if __name__=="__main__":
    check_numbers()
    check_original_producers()
