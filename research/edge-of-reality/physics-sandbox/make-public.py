"""Package the local sandbox as a self-contained browser page.

Usage: python3 make-public.py /absolute/site/checkout
Requires the checked native instrument executable to have been built.
"""
from pathlib import Path
import base64
import gzip
import hashlib
import json
import re
import shutil
import subprocess
import sys

ROOT=Path(__file__).resolve().parent
SITE=Path(sys.argv[1]).resolve()
PUBLIC=SITE/'public/readers/edge-of-reality/sandbox'
RESEARCH=SITE/'research/edge-of-reality/physics-sandbox'
PUBLIC.mkdir(parents=True,exist_ok=True)
RESEARCH.mkdir(parents=True,exist_ok=True)

out=subprocess.run([str(ROOT/'.lake/build/bin/instrument'),'--grid'],capture_output=True,
                   text=True,check=True,timeout=30)
grid=[json.loads(line) for line in out.stdout.splitlines()]
assert len(grid)==10201
assert [(r['p'],r['l']) for r in grid]==[(p,l) for p in range(101) for l in range(101)]
raw=json.dumps(grid,separators=(',',':')).encode()
packed=gzip.compress(raw,mtime=0)
assert gzip.decompress(packed)==raw
(RESEARCH/'instrument-grid.json.gz').write_bytes(packed)
encoded=base64.b64encode(packed).decode()

html=(ROOT/'index.html').read_text()
html=html.replace('<title>ER-01 · Песочница измерения</title>', '<title>ER-01 · Песочница измерения и сеть интерфейсов</title><meta name="description" content="Проверенные в Lean веса измерения, сеть состояний и интерфейсов, квантовый расчёт и классический контроль."><link rel="canonical" href="https://chertogi-razuma-research.kernelpanic888.chatgpt.site/readers/edge-of-reality/sandbox/">')
html=html.replace('<body><main>', '<body><main><nav class="actions"><a href="../#s4">← К ридеру ER-01</a><a href="../../../index.html">На главную</a></nav>')
html=html.replace('ЛОКАЛЬНАЯ ПЕСОЧНИЦА','ПЕСОЧНИЦА ИЗМЕРЕНИЯ')
html=html.replace('Это локальная симуляция измерения.', 'Это симуляция измерения в браузере.')
html=html.replace('Сравниваем точное предсказание Lean с независимым квантовым расчётом и классическим отбором.', 'Сравниваем точные предсказания из заранее проверенного экспорта Lean с независимым квантовым расчётом и классическим отбором в браузере. Сервер Lean не запускается.')
html=html.replace('Классические рациональные вероятности совпали с Lean точно.', 'Классические веса совпали с экспортом Lean точно.')
html=html.replace('Два симулятора используют разные потоки случайных чисел.', 'Два симулятора используют разные потоки псевдослучайных чисел Mulberry32. Seed воспроизводит результат этой браузерной версии; локальная Python-версия использует другой генератор.')
html=html.replace('Полнота комплексных матриц', 'Полнота комплексных матриц')
html=html.replace('</details>\n</main>', '</details>\n<p class="small">Все расчёты и импорт счётчиков выполняются в браузере. Файл счётчиков не отправляется на сервер. <a href="source-map.json">Происхождение и границы проверки</a>.</p>\n</main>')
html=html.replace('<section class="panel" aria-label="Сеть состояний и интерфейсов">', '<section id="network" class="panel" aria-label="Сеть состояний и интерфейсов">')
graph=(ROOT/'graph.js').read_text().replace('Обновляется Lean-ядро. Перезапустите сервер и расчёт.', 'Экспорт интерфейсов недоступен. Обновите страницу.')
engine=(ROOT/'browser-engine.js').read_text()
loader='''
let gridPromise;
function loadLeanGrid(){
 if(!gridPromise)gridPromise=(async()=>{
  if(typeof DecompressionStream==='undefined')throw Error('Браузер не поддерживает распаковку данных. Откройте страницу в актуальном браузере.');
  const text=document.getElementById('lean-instrument-grid').textContent.trim();
  const bytes=Uint8Array.from(atob(text),c=>c.charCodeAt(0));
  const stream=new Blob([bytes]).stream().pipeThrough(new DecompressionStream('gzip'));
  const rows=JSON.parse(await new Response(stream).text());
  if(rows.length!==10201)throw Error('Неполный экспорт Lean');
  return rows;
 })();
 return gridPromise;
}
async function prediction(p,l){
 if(!Number.isInteger(p)||!Number.isInteger(l)||p<0||p>100||l<0||l>100)throw Error('p и lambda: целые проценты 0…100');
 const rows=await loadLeanGrid(),r=rows[p*101+l];
 if(!r||r.p!==p||r.l!==l)throw Error('Параметры не совпали с экспортом Lean');
 return r;
}
'''
html=html.replace('<script src="/graph.js"></script>', '<script type="application/octet-stream" id="lean-instrument-grid">'+encoded+'</script><script>'+engine+'</script><script>'+graph+'</script><script>'+loader+'</script>')
old="const q=new URLSearchParams({p:$('p').value,lambda:$('lambda').value,shots:$('shots').value,seed:$('seed').value});const response=await fetch('/api/experiment?'+q);const r=await response.json();if(!response.ok)throw Error(r.error);"
new="const p=Number($('p').value),l=Number($('lambda').value);const lean=await prediction(p,l);const r=ER01Physics.experiment(lean,p,l,Number($('shots').value),Number($('seed').value));"
assert html.count(old)==1
html=html.replace(old,new)
old="const response=await fetch('/api/compare',{method:'POST',headers:{'Content-Type':'application/json'},body:await f.text()});const r=await response.json();if(!response.ok)throw Error(r.error);"
new="const data=JSON.parse(await f.text());const lean=await prediction(data.pPercent,data.lambdaPercent);const r=ER01Physics.compareImported(data,lean);"
assert html.count(old)==1
html=html.replace(old,new)
assert not re.search(r'\bfetch\s*\(',html)
assert '<script src=' not in html
(PUBLIC/'index.html').write_text(html)

for file in ['ER01/Core.lean','ER01/Instrument.lean','ER01/InterfaceGraph.lean',
             'InstrumentMain.lean','Audit.lean','lakefile.toml','lean-toolchain',
             'physics.py','server.py','verify.py','README_RU.md','graph.js',
             'browser-engine.js','make-public.py','verify-browser.cjs','index.html',
             'verification/report.json','verification/axioms.log',
             'verification/benchmark.json','verification/device-protocol.json',
             'verification/graph-ui.json']:
    dest=RESEARCH/file;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/file,dest)

source={'id':'ER-01-SANDBOX','version':'0.2','date':'2026-11-01',
        'pageSha256':hashlib.sha256(html.encode()).hexdigest(),
        'gridSha256':hashlib.sha256(raw).hexdigest(),
        'gridGzipSha256':hashlib.sha256(packed).hexdigest(),
        'parameterPairs':10201,'instrumentTheorems':7,'graphTheorems':10,
        'coreTheoremsPreviouslyChecked':24,
        'formalSource':'research/edge-of-reality/physics-sandbox/',
        'predictionRuntime':'Replay exact native Lean-exported masses and interface maps',
        'samplingRuntime':'Browser JavaScript, Mulberry32; not Lean-verified sampling',
        'quantumReference':'Numerical 4x4 density-matrix evolution in browser; checked against native Lean grid',
        'hardwareExecuted':False,'physicalHorizonDefined':False,
        'claimBoundary':'Diagonal input has a classical statistical realization. DAG rank is not physical time. No spacetime metric or quantum time machine is established.',
        'uploadPolicy':'Counts file parsed locally in browser; no API upload'}
(PUBLIC/'source-map.json').write_text(json.dumps(source,ensure_ascii=False,indent=2)+'\n')

reader=SITE/'public/readers/edge-of-reality/index.html'
reader_html=reader.read_text()
if 'id="physics-sandbox-entry"' not in reader_html:
    link='''<div class="question" id="physics-sandbox-entry"><h3><span class="ru">Песочница измерения и сеть интерфейсов</span><span class="en">Measurement sandbox and interface graph</span></h3><p><span class="ru">Состояния — вершины, интерфейсы — рёбра. Сравните точные веса из Lean с квантовым расчётом и классическим отбором, переключите чтение наблюдателя и загрузите счётчики. Все расчёты выполняются в браузере; данных устройства пока нет.</span><span class="en">States are vertices; interfaces are edges. Compare exact Lean-exported weights with a quantum calculation and classical selection, switch observer readout, and import counts. Calculations run in your browser; no device data have been collected.</span></p><a href="sandbox/#network"><span class="ru">ОТКРЫТЬ ПЕСОЧНИЦУ ↗</span><span class="en">OPEN SANDBOX (RU) ↗</span></a></div>'''
    assert reader_html.count('<div id="lean-simulator"')==1
    reader_html=reader_html.replace('<div id="lean-simulator"',link+'<div id="lean-simulator"')
    reader.write_text(reader_html)
reader_map=SITE/'public/readers/edge-of-reality/source-map.json'
data=json.loads(reader_map.read_text())
data['version']='0.3'
data['readerSha256']=hashlib.sha256(reader.read_bytes()).hexdigest()
data['physicsSandbox']={'path':'sandbox/','sourceMap':'sandbox/source-map.json',
 'formalSourcePath':'research/edge-of-reality/physics-sandbox/',
 'instrumentTheorems':7,'graphTheorems':10,'hardwareExecuted':False}
reader_map.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
journal=SITE/'journal/2026-11-01-er-01-edge-of-reality.md'
if '## Measurement sandbox and state-interface network' not in journal.read_text():
    with journal.open('a') as f:
        f.write('\n\n## Measurement sandbox and state-interface network\n\nAdded a self-contained browser sandbox linked from section 04. Native Lean-exported exact instrument weights, six interfaces and two record maps cover all 10201 integer-percent parameter pairs. Seven instrument and ten graph theorems are audited. Browser JavaScript performs independent density-matrix calculations and finite-shot sampling; it does not execute Lean. All outcomes remain in the accounting; counts import stays in browser. Original local sources, independent verification and a reproducible export are retained in research/edge-of-reality/physics-sandbox. No hardware measurements, spacetime metric or physical event horizon are claimed. The sandbox UI is Russian and the English reader link identifies it as RU. Homepage reader order is preserved.\n')
print(json.dumps({'pageBytes':len(html.encode()),'gridBytes':len(raw),'gzipBytes':len(packed),'pairs':len(grid),'page':str(PUBLIC/'index.html')}))
