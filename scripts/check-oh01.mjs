import fs from 'node:fs';
import vm from 'node:vm';
import assert from 'node:assert/strict';
import {inspectPublicStaticBoundary} from './check-public-static-boundary.mjs';
const base='public/readers/ontological-honesty/';
const html=fs.readFileSync(base+'index.html','utf8');
const rows=JSON.parse(html.match(/<script id="lean-data" type="application\/json">([\s\S]*?)<\/script>/)[1]);
const scripts=[...html.matchAll(/<script([^>]*)>([\s\S]*?)<\/script>/g)];
for(const [,attrs,code] of scripts)if(!attrs.includes('application/json'))new vm.Script(code);
assert.deepEqual(rows,JSON.parse(fs.readFileSync('research/ontological-honesty/export.json','utf8')));
const table=new Map(rows.map(([e,p,s])=>[e*16+p,s]));assert.equal(table.size,256);
function classify(e,p){const bits=Array.from({length:4},(_,i)=>({e:!!(e&2**i),p:!!(p&2**i)}));const a=bits.filter(x=>x.e);return !a.length?0:a.every(x=>x.p)?1:a.every(x=>!x.p)?2:3;}
function permute(m,perm){return perm.reduce((v,to,from)=>v|((m>>from&1)<<to),0)}
function permutations(a){return a.length?a.flatMap((v,i)=>permutations(a.filter((_,j)=>j!==i)).map(p=>[v,...p])):[[]]}
let refinements=0,renamings=0;
for(let e=0;e<16;e++)for(let p=0;p<16;p++){
 const s=table.get(e*16+p);assert.equal(s,classify(e,p));if(!e)assert.equal(s,0);
 for(let f=1;f<16;f++)if((f&e)===f){if(s===1||s===2)assert.equal(classify(f,p),s);refinements++;}
 if(s===3){assert.ok(Array.from({length:4},(_,i)=>1<<i).some(f=>(f&e)===f&&classify(f,p)===1));assert.ok(Array.from({length:4},(_,i)=>1<<i).some(f=>(f&e)===f&&classify(f,p)===2));}
 for(const perm of permutations([0,1,2,3])){assert.equal(classify(permute(e,perm),permute(p,perm)),s);renamings++;}
}
const boundary=inspectPublicStaticBoundary({html,hosting:JSON.parse(fs.readFileSync('.openai/hosting.json','utf8'))});
assert.ok(boundary.every?boundary.every(c=>c.pass):boundary.ok,JSON.stringify(boundary));
assert.ok(!/\b(sorry|axiom)\s+\w/.test(fs.readFileSync('research/ontological-honesty/Core.lean','utf8')));
const report={status:'PASS',rows:256,renamings,refinements,inlineJavaScript:'parsed',staticBoundary:boundary};
fs.mkdirSync('verification/oh01',{recursive:true});fs.writeFileSync('verification/oh01/model.json',JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({status:'PASS',rows:256,renamings,refinements}));
