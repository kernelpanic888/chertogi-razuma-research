/* Geometry is a display of Lean-exported interfaces. No graph transition
   weights are recomputed here. Reachability highlighting is finite UI traversal. */
(() => {
  const root=document.getElementById('interfaceGraph');
  const mode=document.getElementById('graphMode');
  const detail=document.getElementById('graphDetail');
  const ns='http://www.w3.org/2000/svg';
  let current=null,selected='prepared';
  const positions={prepared:[80,335],success:[330,185],failure:[330,485],
    success0:[660,110],success1:[660,260],failure0:[660,410],failure1:[660,560]};
  const names={prepared:'Вход ρ',success:'Состояние ρs',failure:'Состояние ρf',
    success0:'След |S,0⟩',success1:'След |S,1⟩',failure0:'След |F,0⟩',failure1:'След |F,1⟩'};
  const operations={filterSuccess:'Ks',filterFailure:'Kf',readSuccess0:'Π0',
    readSuccess1:'Π1',readFailure0:'Π0',readFailure1:'Π1'};
  function el(tag,attrs={},text){const e=document.createElementNS(ns,tag);for(const[k,v]of Object.entries(attrs))e.setAttribute(k,v);if(text!==undefined)e.textContent=text;return e;}
  const percent=x=>(100*x).toFixed(1)+'%';
  function draw(r){
    current=r;
    const edges=r.lean.interfaces;
    if(!edges){detail.textContent='Обновляется Lean-ядро. Перезапустите сервер и расчёт.';return;}
    const D=r.lean.denominator,S=r.lean.successMass,F=r.lean.failureMass;
    const A=r.lean.masses[0],B=r.lean.masses[1];
    const masses={prepared:D,success:S,failure:F,success0:A,success1:B,failure0:0,failure1:F};
    const reached=new Set([selected]);
    for(let i=0;i<3;i++)for(const e of edges)if(e.admissible&&reached.has(e.source))reached.add(e.target);
    const svg=el('svg',{viewBox:'0 0 760 690',role:'group','aria-label':'Сеть состояний и направленных интерфейсов. Сплошные стрелки — переходы с положительным весом; пунктир — нулевой вес.'});
    const defs=el('defs');
    for(const [id,color] of [['active','#85ffd5'],['inactive','#54796a'],['selected','#ffd257']]){
      const m=el('marker',{id:'arrow-'+id,viewBox:'0 0 10 10',refX:9,refY:5,markerWidth:7,markerHeight:7,orient:'auto-start-reverse'});
      m.append(el('path',{d:'M 0 0 L 10 5 L 0 10 z',fill:color}));defs.append(m);
    }
    svg.append(defs);
    svg.append(el('text',{x:15,y:25,class:'graphColumn'},'ВХОД'));
    svg.append(el('text',{x:235,y:25,class:'graphColumn'},'УСЛОВНЫЕ СОСТОЯНИЯ'));
    svg.append(el('text',{x:580,y:25,class:'graphColumn'},'СОСТОЯНИЯ ЗАПИСИ'));
    for(const e of edges){
      const [sx,sy]=positions[e.source],[tx,ty]=positions[e.target];
      const mid=(sx+tx)/2;
      const path=el('path',{d:`M ${sx+70} ${sy} C ${mid} ${sy}, ${mid} ${ty}, ${tx-78} ${ty}`,
        fill:'none',stroke:e.admissible?'#85ffd5':'#54796a','stroke-width':e.admissible?3:2,
        'stroke-dasharray':e.admissible?'none':'5 7','marker-end':'url(#arrow-'+(e.admissible?'active':'inactive')+')'});
      svg.append(path);
      const sourceMass=masses[e.source];
      const prob=sourceMass?percent(e.mass/sourceMass):'не задано';
      const lx=(sx+tx)/2,ly=(sy+ty)/2-15;
      const g=el('g',{role:'button',tabindex:0,'aria-label':`${operations[e.id]}, условная вероятность ${prob}`,class:'graphEdge'});
      g.append(el('rect',{x:lx-80,y:ly-17,width:160,height:29,rx:3,fill:'#00140f',stroke:'#216654'}));
      g.append(el('text',{x:lx,y:ly+3,'text-anchor':'middle',fill:e.admissible?'#ffd257':'#91ad9f'},`${operations[e.id]} · ${prob}`));
      const pick=()=>{detail.textContent=`Интерфейс ${operations[e.id]}: ${names[e.source]} → ${names[e.target]}. ${e.admissible?'Допустим для текущего входа.':'Нулевой вес для текущего входа.'} Совместный вес пути ${e.mass}/${D}; вероятность перехода при заданном исходном состоянии: ${prob}.`;};
      g.addEventListener('click',pick);g.addEventListener('keydown',ev=>{if(ev.key==='Enter'||ev.key===' '){ev.preventDefault();pick();}});svg.append(g);
    }
    for(const [id,[x,y]] of Object.entries(positions)){
      const active=masses[id]>0,highlight=reached.has(id)&&active;
      const group=el('g',{role:'button',tabindex:0,'aria-label':names[id],class:'graphNode'});
      group.append(el('circle',{cx:x,cy:y,r:60,fill:'#03281f',stroke:id===selected?'#ffd257':highlight?'#85ffd5':'#54796a','stroke-width':id===selected?4:2,'stroke-dasharray':active?'none':'4 6'}));
      group.append(el('text',{x,y:y-8,'text-anchor':'middle',fill:active?'#d8ffef':'#91ad9f'},names[id]));
      let sub=id==='prepared'?'diag(p, 1−p)':id==='success'?(S?`p₀ = ${percent(A/S)}`:'не определено'):id==='failure'?(F?'|1⟩⟨1|':'не определено'):'';
      if(id!=='prepared'&&id!=='success'&&id!=='failure'){
        const e=edges.find(e=>e.target===id);
        const rec=e[mode.value==='coarse'?'coarseRecord':'resolvedRecord'];
        sub=rec?`чтение: ${rec[0]?'S':'F'}${mode.value==='coarse'?'':rec[1]}`:'нет чтения';
      }
      group.append(el('text',{x,y:y+15,'text-anchor':'middle',fill:'#91ad9f',class:'graphSmall'},sub));
      group.append(el('text',{x,y:y+80,'text-anchor':'middle',fill:active?'#85ffd5':'#91ad9f',class:'graphSmall'},`вес: ${percent(masses[id]/D)}`));
      const pick=()=>{selected=id;draw(current);};
      group.addEventListener('click',pick);group.addEventListener('keydown',ev=>{if(ev.key==='Enter'||ev.key===' '){ev.preventDefault();pick();}});svg.append(group);
    }
    svg.append(el('text',{x:300,y:670,'text-anchor':'middle',fill:'#ffd257',class:'graphSmall'},'Σ = {Ks, Kf} — семейство интерфейсов'));
    root.replaceChildren(svg);
    const reachable=[...reached].filter(id=>id!==selected&&masses[id]>0).map(id=>names[id]);
    detail.textContent=`Выбрано: ${names[selected]}. ${masses[selected]?'Достижимые состояния: '+(reachable.join(', ')||'дальнейших переходов нет')+'.':'Нулевой вес: это условное состояние в данном запуске не реализуется.'} ${mode.value==='coarse'?'Грубое чтение скрывает метку 0/1; различные вершины сохраняются.':'Подробное чтение различает флаг и метку системы.'}`;
  }
  mode.addEventListener('change',()=>current&&draw(current));
  window.drawInterfaceGraph=draw;
})();
