// H19b source actor descent and coarsest invariant observation refinement.
// Re-read exact pinned fixture owned by H2, no new transcription.
import {readFileSync} from 'node:fs';
import assert from 'node:assert/strict';
const s=readFileSync(new URL('./check_shem216_r13_indexed_20261125.mjs',import.meta.url),'utf8');
const f=JSON.parse(s.slice(s.indexOf('['),s.indexOf('];')+1));
const rows=Array.from({length:3},(_,i)=>{
 const seg=f.filter(s=>s.includes(`n="${19+i}"`)).map(s=>[...s.matchAll(/<w>([\s\S]*?)<\/w>/g)].map(x=>x[1]));
 return seg[0].flatMap((w,j)=>[...(w==='.'?seg[1][j]:w)].filter(c=>/[\u05d0-\u05ea]/u.test(c)));
});
assert(rows.every(r=>r.length===72));
const C=Array.from({length:216},(_,i)=>[Math.floor(i/72),i%72]);
const masks=Array.from({length:8},(_,i)=>i);
const move=(m,[r,j])=>{if(m&1&&r===1)j=71-j;if(m&2){r=2-r;j=71-j;}if(m&4)j=(j+36)%72;return [r,j]};
const obs=([r,j])=>rows[r][j],sig=x=>masks.map(m=>obs(move(m,x))).join('');
const key=JSON.stringify;
const classes=new Map();for(const x of C){const a=sig(x);if(!classes.has(a))classes.set(a,[]);classes.get(a).push(x);}
let action=0,composition=0;
for(const x of C)for(const m of masks){
 assert.equal(sig(move(m,x)),masks.map(n=>sig(x)[n^m]).join(''));action++;
 for(const n of masks){assert.equal(key(move(n,move(m,x))),key(move(n^m,x)));composition++}
}
const conflict=m=>{const f=new Map();for(const x of C){const a=obs(x),b=obs(move(m,x));if(!f.has(a))f.set(a,new Map());if(!f.get(a).has(b))f.get(a).set(b,x);}
 const bad=[...f].filter(([,ys])=>ys.size>1);
 return {mask:m,conflicts:bad.length,maxFibre:Math.max(...[...f.values()].map(v=>v.size)),witness:bad.length?[bad[0][0],[...bad[0][1]].slice(0,2)]:null};
};
const collisions=Object.fromEntries([...classes.values()].reduce((a,v)=>a.set(v.length,(a.get(v.length)||0)+1),new Map()));
const byRow=new Set(C.map(x=>key([x[0],obs(x)]))).size;
console.log(JSON.stringify({distinctGlyphs:new Set(C.map(obs)).size,distinctRowGlyphs:byRow,signatureClasses:classes.size,collisions,action,composition,conflicts:masks.map(conflict)},null,2));
