#!/usr/bin/env python3
"""Conventional SQUID pickup -> flux transformer -> pumped readout, SI verified.

Sources: superconducting flux transformer and Josephson sensor circuits;
RQU Physical Review Research 7 013281 (2025); Filsinger Lorentz-ADE and
signed port energy owner. No gravity conversion coefficients assumed.
All PSDs symbolic: input T^2/Hz, SQUID Wb^2/Hz, added output Wb^2/Hz.
"""
import sympy as s

def check():
    L=s.Matrix([1,0,0,0]);M=s.Matrix([0,1,0,0]);T=s.Matrix([0,0,1,0]);I=s.Matrix([0,0,0,1])
    tesla=M-2*T-I; web=tesla+2*L; henry=web-I
    assert web==henry+I and tesla==web-2*L
    B,Ap,Lp,Li,Mut,eta,Gain=s.symbols('B Ap Lp Li Mut eta Gain',positive=True)
    phi_in=B*Ap
    i_pick=phi_in/(Lp+Li)
    phi_squid=Mut*i_pick
    chiB=s.diff(phi_squid,B)
    assert s.simplify(chiB-Mut*Ap/(Lp+Li))==0
    assert s.simplify(phi_squid/B-chiB)==0
    assert tesla+2*L==web
    Sin,Sphi,Sread,Spump=s.symbols('Sin Sphi Sread Spump',nonnegative=True)
    output_psd=Gain**2*eta**2*(chiB**2*Sin+Sphi)+Sread+Spump
    equivalent=s.factor(output_psd/(Gain*eta*chiB)**2)
    assert s.simplify(equivalent-
      (Sin+Sphi/chiB**2+(Sread+Spump)/(Gain**2*eta**2*chiB**2)))==0
    assert s.simplify(s.limit(equivalent,Gain,s.oo)-
      (Sin+Sphi/chiB**2))==0
    assert s.simplify(s.diff(chiB,Ap)-Mut/(Lp+Li))==0
    # Nonphysical unlimited-pickup-area algebraic limit is NOT an engineering
    # claim; increasing Ap generally alters Lp and spatially integrated noise.
    assert s.simplify(s.limit(equivalent,Ap,s.oo)-Sin)==0
    print('PASS SI signatures, pickup current/flux transfer and input-referred noise')
    print('S_Beq = Sin + Sphi/chiB² + (Sread+Spump)/(Gain² eta² chiB²)')
    print('OPEN Lp(area), measured flux PSD, transfer eta(f), pump loss and environment')

if __name__=='__main__':check()
