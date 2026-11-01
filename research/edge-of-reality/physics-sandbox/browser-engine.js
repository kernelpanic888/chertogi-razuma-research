/* Browser sampling/reference layer. Exact predictions and interface maps are
   supplied by the frozen Lean export, not calculated by this layer. */
(() => {
  const keys=['success0','success1','failure0','failure1'];
  function integer(x,lo,hi,name){if(!Number.isInteger(x)||x<lo||x>hi)throw Error(`${name}: требуется целое число ${lo}…${hi}`);return x;}
  function rng(seed){let t=seed>>>0;return()=>{t=(t+0x6D2B79F5)>>>0;let x=Math.imul(t^(t>>>15),1|t);x^=x+Math.imul(x^(x>>>7),61|x);return((x^(x>>>14))>>>0)/4294967296;};}
  function multiply(a,b){return a.map(row=>b[0].map((_,j)=>row.reduce((sum,x,k)=>sum+x*b[k][j],0)));}
  function quantumReference(p,l){
    const a=l/100,s=Math.sqrt(1-a*a),u=[[1,0,0,0],[0,1,0,0],[0,0,a,-s],[0,0,s,a]];
    const rho=Array.from({length:4},()=>[0,0,0,0]);rho[0][0]=p/100;rho[2][2]=1-p/100;
    const dagger=u[0].map((_,i)=>u.map(row=>row[i]));
    const evolved=multiply(multiply(u,rho),dagger);
    return [0,2,1,3].map(i=>evolved[i][i]);
  }
  function reference(lean,p,l){
    const probabilities=quantumReference(p,l),ideal=lean.masses.map(x=>x/lean.denominator);
    const classical=[p*10000,l*l*(100-p),0,(10000-l*l)*(100-p)];
    const exactClassicalMatch=lean.denominator===1000000&&classical.every((m,i)=>m===lean.masses[i]);
    const quantumMaxError=Math.max(...ideal.map((x,i)=>Math.abs(x-probabilities[i])));
    if(!exactClassicalMatch||quantumMaxError>1e-12)throw Error('Независимые расчёты не совпали с экспортом Lean');
    return {exactClassicalMatch,quantumMaxError,probabilities};
  }
  function wilson(k,n){if(!n)return null;const z=1.959963984540054,phat=k/n,den=1+z*z/n,mid=(phat+z*z/(2*n))/den,half=z*Math.sqrt(phat*(1-phat)/n+z*z/(4*n*n))/den;return[Math.max(0,mid-half),Math.min(1,mid+half)];}
  function summarize(counts,expected){
    const shots=keys.reduce((n,k)=>n+counts[k],0),accepted=counts.success0+counts.success1,target=expected[0]+expected[1];
    return {shots,counts,successRate:accepted/shots,successInterval95:wilson(accepted,shots),conditionalZero:accepted?counts.success0/accepted:null,conditionalInterval95:wilson(counts.success0,accepted),expectedCounts:Object.fromEntries(keys.map((k,i)=>[k,shots*expected[i]])),expectedSuccess:target,expectedConditionalZero:target?expected[0]/target:null,impossibleOutcomeCounts:keys.reduce((n,k,i)=>n+(expected[i]===0?counts[k]:0),0)};
  }
  function sampleQuantum(probabilities,shots,seed){
    const next=rng(seed),counts=Object.fromEntries(keys.map(k=>[k,0]));
    const cutoffs=[probabilities[0],probabilities[0]+probabilities[1],probabilities[0]+probabilities[1]+probabilities[2]];
    for(let i=0;i<shots;i++){const x=next();const k=x<cutoffs[0]?0:x<cutoffs[1]?1:x<cutoffs[2]?2:3;counts[keys[k]]++;}return counts;
  }
  function sampleClassical(p,l,shots,seed){const next=rng(seed),counts=Object.fromEntries(keys.map(k=>[k,0]));for(let i=0;i<shots;i++){if(next()<p/100)counts.success0++;else if(next()<(l/100)**2)counts.success1++;else counts.failure1++;}return counts;}
  function protocol(p,l){
    const theta=2*Math.acos(l/100),header='OPENQASM 2.0;\ninclude "qelib1.inc";\ngate cry(theta) c,t { ry(theta/2) t; cx c,t; ry(-theta/2) t; cx c,t; }\nqreg q[2];\ncreg c[2];\n';
    const tail=`cry(${theta.toPrecision(17)}) q[0],q[1];\nmeasure q[0] -> c[0];\nmeasure q[1] -> c[1];\n`;
    return {pPercent:p,lambdaPercent:l,theta,preparation:'Choose preparation 0 independently on each trial with probability p/100; otherwise choose preparation 1. Count all trials, including failures. Fixed shot allocations require a different statistical analysis.',preparation0:header+tail,preparation1:header+'x q[0];\n'+tail,bitstrings:{'00':'success0','01':'success1','10':'failure0','11':'failure1'},bitOrder:'c[1]c[0] = ancilla,system',status:'Circuit specification only; not submitted to hardware'};
  }
  function experiment(lean,p,l,shots,seed){
    integer(p,0,100,'p');integer(l,0,100,'lambda');integer(shots,1,100000,'shots');integer(seed,0,2147483647,'seed');
    if(lean.p!==p||lean.l!==l)throw Error('Параметры не совпали с экспортом Lean');
    const ref=reference(lean,p,l),ideal=lean.masses.map(x=>x/lean.denominator);
    return {schema:'ER01-PHYSICS/1',pPercent:p,lambdaPercent:l,shots,seed,lean,reference:ref,
      quantum:summarize(sampleQuantum(ref.probabilities,shots,seed),ideal),
      classical:summarize(sampleClassical(p,l,shots,(seed^0x5a5a5a5a)>>>0),ideal),
      protocol:protocol(p,l),provenance:'BROWSER_SIMULATION_NOT_HARDWARE',samplingEngine:'mulberry32-v1',predictionSource:'frozen Lean export; no server-side Lean'};
  }
  function compareImported(data,lean){
    if(!data||data.schema!=='ER01-COUNTS/1')throw Error('Ожидается ER01-COUNTS/1 JSON');
    const p=integer(data.pPercent,0,100,'pPercent'),l=integer(data.lambdaPercent,0,100,'lambdaPercent');
    const counts=data.counts;if(!counts||Object.keys(counts).length!==4||!keys.every(k=>Object.hasOwn(counts,k)))throw Error('Нужны все четыре счётчика исходов');
    keys.forEach(k=>integer(counts[k],0,1000000000,k));const shots=integer(data.shots,1,1000000000,'shots');
    if(keys.reduce((n,k)=>n+counts[k],0)!==shots)throw Error('Сумма счётчиков должна равняться shots, включая отказы');
    if(data.samplingDesign!=='iid-mixture')throw Error('Поддерживается дизайн iid-mixture');
    if(lean.p!==p||lean.l!==l)throw Error('Параметры не совпали с экспортом Lean');
    return {schema:'ER01-IMPORT-COMPARISON/1',pPercent:p,lambdaPercent:l,summary:summarize(counts,lean.masses.map(x=>x/lean.denominator)),provenance:'USER_SUPPLIED_COUNTS_UNVERIFIED',source:String(data.source??'unspecified').slice(0,160)};
  }
  const api={experiment,compareImported,reference,quantumReference};
  if(typeof module!=='undefined'&&module.exports)module.exports=api;else window.ER01Physics=api;
})();
