#!/usr/bin/env python3
"""Sourced SQUID/cryogenic superconducting sensitivity comparison.

White component noise is NOT a measured cardiac-band system spectrum.
The sensitivity-to-range numbers below are conditional, not demonstrated
1000-SQUID system performance. See Docs/physics/DiamondMCGArrayResidualNoiseMaxCut20261118.md.
"""
import sympy as s

REFERENCES = [
 ("Room NV MCG",7000,"measured diamond-MCG sensitivity, system-specific","https://pmc.ncbi.nlm.nih.gov/articles/PMC13580569/"),
 ("ELF SQUID system",25,"0.5-100 Hz measured system; geomagnetometry","https://www.jstage.jst.go.jp/article/jcsj/59/1/59_19/_article/-char/en"),
 ("Multiloop SQUID",s.Rational(415,100),"2026 white-noise floor; 1/f corner around 10 Hz","https://www.sciencedirect.com/science/article/pii/S0921453426001036"),
 ("Transformer-coupled SQUID",s.Rational(3,2),"nominal magnetic field sensitivity; cardiac band unverified","https://pmc.ncbi.nlm.nih.gov/articles/PMC12349212/"),
 ("Low-noise SQUID system",s.Rational(1,2),"historical low system-noise benchmark; not 1 Hz certified","https://doi.org/10.1088/0953-2048/29/11/113001"),
 ("Extreme SQUID component",s.Rational(1,10),"survey white-noise component, not 1 Hz system","https://pmc.ncbi.nlm.nih.gov/articles/PMC10535156/"),
 ("Hypothetical extreme receiver",s.Rational(1,100),"NOT a validated SQUID or diamond receiver",None)
]

def years(asd_ft, r, n=1000, amplitude_pt=50, reference_m=s.Rational(1,10)):
    field=s.Rational(amplitude_pt)*(reference_m/s.Rational(r))**3
    seconds=(5*s.Rational(asd_ft)/1000/field)**2/s.Integer(n)
    return s.factor(seconds/s.Integer(31557600))

def main():
    r,a,sigma,n=s.symbols("r a sigma n",positive=True)
    time=(sigma*r**3/a)**2/n
    assert s.simplify(time.subs(r,10*r)/time-1000000)==0
    assert s.simplify(time.subs(sigma,sigma/10)/time-s.Rational(1,100))==0
    assert s.simplify(time.subs(n,10*n)/time-s.Rational(1,10))==0
    assert years(s.Rational(1,10),1000)/years(1,1000)==s.Rational(1,100)
    print("PASS exact r^6, ASD^2, N^-1 receiver substitution laws")
    print("Model: 50 pT at 0.1m, 1000 independent channels, r^-3, coherent threshold 5")
    for name,asd,scope,url in REFERENCES:
        print(name,"fT/sqrtHz",asd,"years @10,100,1000m",
              *[float(years(asd,r)) for r in [10,100,1000]],scope,url)
    print("NO measured cardiac-band 1000-channel system/no source attribution")

if __name__=="__main__":main()
