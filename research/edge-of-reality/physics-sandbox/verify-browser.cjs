const fs=require('node:fs'),vm=require('node:vm'),zlib=require('node:zlib'),assert=require('node:assert/strict');
const site=process.argv[2];
const research=site+'/research/edge-of-reality/physics-sandbox';
const rows=JSON.parse(zlib.gunzipSync(fs.readFileSync(research+'/instrument-grid.json.gz')));
const sandbox={module:{exports:{}}};
vm.runInNewContext(fs.readFileSync(__dirname+'/browser-engine.js','utf8'),sandbox);
const api=sandbox.module.exports;
let maxError=0;
for(const row of rows){const r=api.reference(row,row.p,row.l);assert.equal(r.exactClassicalMatch,true);maxError=Math.max(maxError,r.quantumMaxError);}
const normal=rows[50*101+50],zero=rows[0],transparent=rows[50*101+100];
const run=api.experiment(normal,50,50,10000,42);
assert.equal(run.quantum.expectedSuccess,.625);assert.equal(run.quantum.expectedConditionalZero,.8);
assert.equal(JSON.stringify(run),JSON.stringify(api.experiment(normal,50,50,10000,42)));
for(const engine of ['quantum','classical']){
  assert.equal(Object.values(run[engine].counts).reduce((a,b)=>a+b,0),10000);
  assert.equal(run[engine].counts.failure0,0);
  for(const [i,k] of ['success0','success1','failure0','failure1'].entries()){
    const p=normal.masses[i]/normal.denominator;
    assert.ok(Math.abs(run[engine].counts[k]-10000*p)<8*Math.sqrt(10000*p*(1-p))+1);
  }
}
const refused=api.experiment(zero,0,0,100,0);assert.equal(refused.quantum.conditionalZero,null);assert.equal(refused.quantum.counts.failure1,100);
assert.equal(api.experiment(transparent,50,100,100,42).quantum.successRate,1);
const data={schema:'ER01-COUNTS/1',pPercent:50,lambdaPercent:50,shots:10000,samplingDesign:'iid-mixture',source:'synthetic verification',counts:{success0:5000,success1:1250,failure0:0,failure1:3750}};
assert.equal(api.compareImported(data,normal).summary.successRate,.625);
for(const bad of [{...data,shots:9999},{...data,pPercent:true},{...data,samplingDesign:'fixed-allocation'},{...data,counts:{success0:10000}}])assert.throws(()=>api.compareImported(bad,normal));
assert.throws(()=>api.experiment(normal,50,50,0,42));
const html=fs.readFileSync(site+'/public/readers/edge-of-reality/sandbox/index.html','utf8');
const embedded=html.match(/id="lean-instrument-grid">([^<]+)<\/script>/)[1];
assert.equal(zlib.gunzipSync(Buffer.from(embedded,'base64')).toString(),JSON.stringify(rows));
for(const match of html.matchAll(/<script\b([^>]*)>([\s\S]*?)<\/script>/g))if(!match[1].includes('application/octet-stream'))new vm.Script(match[2]);
assert.equal(/\bfetch\s*\(/.test(html),false);
const result={status:'PASS',parameterPairs:rows.length,maxQuantumError:maxError,seedReproducibility:true,zeroPosteriorAbsent:true,importValidation:true,embeddedGridRoundtrip:true,inlineSyntax:true,samplingEngine:'mulberry32-v1',benchmark:run};
fs.writeFileSync(research+'/verification/browser.json',JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify({...result,benchmark:undefined}));
