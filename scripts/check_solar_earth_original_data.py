"""Original Lin GAMERA figure diagnostics and AusLAMP transfer audit.
Usage: python check_solar_earth_original_data.py /path/to/source/files
No raw data redistributed, no physical source-to-ground or control admission.
"""
import sys, json, hashlib, re, zipfile
from pathlib import Path
import numpy as np
import xarray as xr
root=Path(sys.argv[1]); hashes={
'PF_fig_PF.nc':'8ff495be1ebdd6609813061880b8faf08ac8365540e8ac2d2d64961c9b3b6880',
'PF_fig_JH.nc':'2213a4fbcf2f3f7354dd16b53699decbcca5d4043b3ec71f73d2ae8fb9528255',
'Lin25_PF_fig_JH.m':'cd9193d648601c69f85c31e185214555df690ef5c8ee2ae72ff1321344a8d552',
'Lin25_PF_fig_PF.m':'03c65aac070842225bf705a82f6b7a82649f9a11f409ee1769166a655bd7e1aa',
'auslamp-qld-phase-3-edi.zip':'26020ec6a1db00359a8703fad30219e6e2e9b20e8b87e968633576525b4fab49'}
for name,sha in hashes.items(): assert hashlib.sha256((root/name).read_bytes()).hexdigest()==sha
with xr.open_dataset(root/'PF_fig_JH.nc',decode_cf=False) as ds: j={k:v.values for k,v in ds.variables.items()}
with xr.open_dataset(root/'PF_fig_PF.nc',decode_cf=False) as ds: p={k:v.values for k,v in ds.variables.items()}
assert len(j)==14 and len(p)==646
# MATLAB labels and paper Table 1, not inferred NetCDF units (attributes empty).
a=j['PF_Tpd'].ravel();b=j['JH_Tpd'].ravel();c=j['PF_Ped'].ravel();d=j['JH_Ped'].ravel()
assert np.all(a>0) and np.all(b>0) and np.all(c>0) and np.all(d>0)
assert a[2]==c[1] and b[2]==d[1] and np.array_equal(b,j['TPODCs'].ravel()[:7])
assert np.argmax(a)==2 and np.argmax(a+b)==3
assert np.all(np.diff(c)<0)
period=[dict(period_s=t,alfven_GW=float(x),dc_GW=float(y),sum_GW=float(x+y),alfven_fraction=float(x/(x+y))) for t,x,y in zip([50,100,200,300,500,1000,None],a,b)]
ped=[dict(conductance_S=t,alfven_GW=float(x),dc_GW=float(y),sum_GW=float(x+y),alfven_fraction=float(x/(x+y))) for t,x,y in zip([3,5,10,20],c,d)]
peak=np.unravel_index(np.argmax(p['S_par_plt']),p['S_par_plt'].shape)
assert tuple(int(p[k].item())-1 for k in ('jmax','kmax'))==peak[::-1]
assert p['twin'].item()==200 and p['flb'].item()==4.5 and p['fub'].item()==5.5
# Paired 600-second selected field-line sample, not full 4-hour cross-spectrum.
t=p['tplt'].ravel(); E=p['emrd_plts']; B=p['bphi_plts']; s=p['dsfl'].ravel()
assert E.shape==B.shape==(61,615) and np.allclose(np.diff(t),10,atol=1e-5)
# LS fit real sine/cosine and constant; retained cross term is a component
# product, not full vector Poynting flux or field-to-ground propagation.
F=np.column_stack([np.ones(len(t)),np.cos(2*np.pi*t/200),np.sin(2*np.pi*t/200)])
ce=np.linalg.lstsq(F,E,rcond=None)[0]; cb=np.linalg.lstsq(F,B,rcond=None)[0]
ze=ce[1]-1j*ce[2]; zb=cb[1]-1j*cb[2]
co=(ze*zb.conj()).real/2; den=abs(ze)*abs(zb)/2
assert np.all(abs(co)<=den+1e-12)
# E[mV/m] B[nT] / mu0 => W/m²; orientation not assigned here.
mu=4*np.pi*1e-7; product_flux=co*1e-12/mu
# EDI stored component units verified against apparent resistivity 0.2|Z|²/f.
# Do not infer physical azimuths or fill EMPTY values. No site ranking.
rows=[];coverage=[];rho_errors=[];freq_count=0;file_count=0
with zipfile.ZipFile(root/'auslamp-qld-phase-3-edi.zip') as archive:
    assert archive.testzip() is None and 'CC-BY-4.0' in archive.read('LICENSE.txt').decode()
    for name in archive.namelist():
        if not name.lower().endswith('.edi'):continue
        file_count+=1; text=archive.read(name).decode(); blocks={}
        for block in re.split(r'(?m)^>',text)[1:]:
            head,_,body=block.partition('\n'); key=head.strip().split()[0]
            if '//' not in head or key=='!':continue
            try: blocks[key]=np.array([float(v) for v in body.split()])
            except ValueError:continue
        f=blocks['FREQ'];freq_count+=len(f);assert len(f)==int(re.search(r'NFREQ=(\d+)',text)[1])
        assert np.all(f>0) and np.all(np.diff(f)<0)
        for ab in ('XX','XY','YX','YY'):
            assert all(len(blocks[k])==len(f) for k in ('Z'+ab+'R','Z'+ab+'I','Z'+ab+'.VAR','RHO'+ab))
            z=blocks['Z'+ab+'R']+1j*blocks['Z'+ab+'I'];rr=blocks['RHO'+ab];valid=(abs(z)<1e30)&(rr>0)&(rr<1e30)
            rho_errors.extend(abs(.2*abs(z[valid])**2/f[valid]/rr[valid]-1))
        coverage.extend(f.tolist())
        for target in (.005,.05,3.915,7.83):
            i=int(np.argmin(abs(f-target)))
            if abs(f[i]/target-1)>1e-5:continue
            Z=np.array([[blocks['Z'+a+b+'R'][i]+1j*blocks['Z'+a+b+'I'][i] for b in 'XY'] for a in 'XY'])
            var=np.array([[blocks['Z'+a+b+'.VAR'][i] for b in 'XY'] for a in 'XY'])
            if np.max(abs(Z))>=1e30 or np.max(var)>=1e30 or np.min(var)<0:continue
            # E=Z_B B, Z_B=1000 Z in V/m/T; Z_H=mu0 Z_B in ohms.
            # Signed down-component form conditional on right-handed x,y,down frame.
            K=np.array([[0,-1],[1,0]])@Z; K=(K+K.conj().T)/2
            ev=np.linalg.eigvalsh(K);sv=np.linalg.svd(Z,compute_uv=False)
            rows.append(dict(f=target,gain=float(sv[0]),min_signed=float(ev[0]),max_signed=float(ev[-1]),variance_scale=float(np.sqrt(var.sum()))))
assert file_count==41 and freq_count==1467
summary=[]
for f in (.005,.05,3.915,7.83):
    rr=[r for r in rows if r['f']==f];summary.append(dict(f_Hz=f,count=len(rr),gain_mV_km_per_nT_min_median_max=np.percentile([r['gain'] for r in rr],[0,50,100]).tolist() if rr else [],positive_nominal_signed_forms=sum(r['min_signed']>0 for r in rr),median_variance_scale=float(np.median([r['variance_scale'] for r in rr])) if rr else None))
print(json.dumps(dict(status='SOURCE_DIAGNOSTIC_AND_MEASURED_TRANSFER_REPLAY',hashes=hashes,period=period,ped=ped,baseline_map_GW=float(p['TPOYN'].item()),baseline_table_minus_map_GW=float(a[2]-p['TPOYN'].item()),peak_alfven_mW_m2=float(np.max(p['S_par_plt'])),peak_dc_mW_m2=float(np.nanmax(j['avg_joun'])),dc_map_missing=int(np.sum(~np.isfinite(j['avg_joun']))),keogram_component_product_W_m2_range=[float(product_flux.min()),float(product_flux.max())],keogram_time_samples=len(t),keogram_space_samples=len(s),edi_count=file_count,edi_frequency_count=freq_count,edi_freq_range_Hz=[min(coverage),max(coverage)],rho_relative_error_percentiles=np.percentile(rho_errors,[50,95,100]).tolist(),edi_summary=summary,physical_admission=False),indent=2))
