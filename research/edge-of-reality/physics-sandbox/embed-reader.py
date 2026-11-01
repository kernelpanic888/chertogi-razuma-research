"""Embed the complete standalone sandbox in ER-01, without a frame or network.

Run after make-public.py:
  python3 research/edge-of-reality/physics-sandbox/embed-reader.py
The host and template are part of the reader HTML. An open shadow root scopes
the existing styles and controls; inline code uses that root for lookup.
"""
from pathlib import Path
import hashlib
import json
import re

SITE=Path(__file__).resolve().parents[3]
READER=SITE/'public/readers/edge-of-reality/index.html'
SANDBOX=SITE/'public/readers/edge-of-reality/sandbox/index.html'
source=SANDBOX.read_text()
style=re.search(r'<style>([\s\S]*?)</style>',source)[1]
style=style.replace('body{',':host{display:block;')
style+='\nmain{width:100%;max-width:none;margin:0}h3{font:600 28px/1.2 Georgia,serif;color:#85ffd5;margin:20px 0}.panel{margin:20px 0}nav{margin-bottom:16px}\n'
body=re.search(r'<main>([\s\S]*?)</main>',source)[1]
body=re.sub(r'<nav\b[^>]*>[\s\S]*?</nav>','',body,count=1)
body=body.replace('<h1>','<h3>').replace('</h1>','</h3>')
body=body.replace('href="source-map.json"','href="sandbox/source-map.json"')
scripts=[]
data=[]
for match in re.finditer(r'<script\b([^>]*)>([\s\S]*?)</script>',source):
    attrs,code=match[1],match[2]
    if 'application/octet-stream' in attrs:
        data.append(match[0])
        continue
    code=code.replace('document.getElementById(', 'sandboxDocument.getElementById(')
    code=code.replace('document.querySelectorAll(', 'sandboxDocument.querySelectorAll(')
    code=code.replace('window.ER01Physics=api', 'sandboxHost.physics=api')
    code=code.replace('window.drawInterfaceGraph', 'sandboxHost.drawInterfaceGraph')
    code=code.replace('ER01Physics.experiment(', 'sandboxHost.physics.experiment(')
    code=code.replace('ER01Physics.compareImported(', 'sandboxHost.physics.compareImported(')
    scripts.append(code)
assert len(data)==1 and len(scripts)==4
assert not any(re.search(r'\bfetch\s*\(',script) for script in scripts)
intro='''<section id="s4b"><div id="physics-sandbox-entry"><div class="eyebrow">04B / ER-01 · STATES → INTERFACES → RECORDS</div>
<h2><span class="ru">Состояния и интерфейсы: проверяемая сеть</span><span class="en">States and interfaces: a checkable network</span></h2>
<p><span class="ru">Здесь модель получает явную сеть переходов: вершины задают состояния системы и регистров записи, а рёбра — интерфейсы с операциями измерения. Песочница встроена в эту страницу вместе с точными данными Lean; переходить на другой сайт или запускать локальный сервер не требуется.</span><span class="en">The model now has an explicit transition network: vertices represent system and record-register states; edges are interfaces carrying measurement operations. The complete sandbox and exact Lean data are embedded in this page. No separate page or local server is required.</span></p>
<div class="formula">Kₛ = diag(1, λ), &nbsp; K𝒻 = diag(0, √(1−λ²))<br>Kₛ†Kₛ + K𝒻†K𝒻 = I<br>P(S) = p + λ²(1−p), &nbsp; P(0 | S) = p / P(S), &nbsp; P(S) &gt; 0</div>
<p><span class="ru">Σ обозначает семейство интерфейсов {Kₛ, K𝒻}. После выбора исхода возникают условные состояния, затем интерфейсы чтения записывают метку. Подробное чтение различает S0 и S1; грубое читает только S, сохраняя разные вершины модели. Нулевой вес означает отсутствие условного результата в этом запуске.</span><span class="en">Σ denotes the interface family {Kₛ, K𝒻}. Outcome selection produces conditional states, followed by readout interfaces that record a label. Resolved readout distinguishes S0 and S1; coarse readout reports only S while retaining distinct model vertices. Zero weight leaves the corresponding conditional result undefined.</span></p>
<p><span class="ru">Семь теорем инструмента проверяют веса успеха и отказа; десять теорем сети — сохранение веса, свойства путей и различие чтений. Точные веса и карты интерфейсов заранее экспортированы из Lean для всех 10 201 пары целых процентов. Независимый матричный расчёт и выборки выполняются в браузере. Подписи интерактивной панели ниже — на русском.</span><span class="en">Seven instrument theorems check success and failure weights; ten network theorems check mass preservation, path structure and readout distinctions. Exact weights and interface maps were exported from Lean for all 10,201 integer-percent pairs. The independent matrix calculation and finite-shot samples run in the browser. The interactive panel below has Russian labels.</span></p>
<div class="red"><span class="ru">Это конечная модель измерения с классически воспроизводимой диагональной статистикой. Расположение вершин не задаёт метрику пространства-времени. Отсутствие обратного пути следует из выбранной сети и не доказывает физический запрет обратных процессов. Данных квантового устройства пока нет.</span><span class="en">This is a finite measurement model whose diagonal statistics admit a classical realization. Vertex positions do not define a spacetime metric. The absence of a reverse path follows from the chosen network, not a physical prohibition of reverse processes. No quantum-device data have been collected.</span></div>
</div>
'''
fragment=intro+'<div id="er01-physics-sandbox" lang="ru"></div><template id="er01-physics-template"><style>'+style+'</style><main>'+body+'</main>'+''.join(data)+'</template>'
fragment+='''<script>(() => {
const sandboxHost=document.getElementById('er01-physics-sandbox');
const sandboxDocument=sandboxHost.attachShadow({mode:'open'});
sandboxDocument.append(document.getElementById('er01-physics-template').content.cloneNode(true));
'''+ '\n;\n'.join(scripts)+'\n})();</script>'
fragment+='''<p class="links"><a href="sandbox/#network"><span class="ru">Открыть на весь экран ↗</span><span class="en">Open full-screen (RU) ↗</span></a><a href="sandbox/source-map.json"><span class="ru">Паспорт песочницы ↗</span><span class="en">Sandbox provenance ↗</span></a></p></section>'''
start='<!-- ER01-INTEGRATED-SANDBOX:START -->'
end='<!-- ER01-INTEGRATED-SANDBOX:END -->'
reader=READER.read_text()
reader=re.sub(r'<div class="question" id="physics-sandbox-entry">[\s\S]*?</div>(?=<div id="lean-simulator")','',reader,count=1)
if start in reader:
    reader=re.sub(re.escape(start)+r'[\s\S]*?'+re.escape(end),lambda _:start+fragment+end,reader,count=1)
else:
    assert reader.count('<section id="s5">')==1
    reader=reader.replace('<section id="s5">',start+fragment+end+'<section id="s5">')
reader=reader.replace('ER-01 · v0.2','ER-01 · v0.4')
READER.write_text(reader)
source_map=SITE/'public/readers/edge-of-reality/source-map.json'
record=json.loads(source_map.read_text())
record['version']='0.4'
record['readerSha256']=hashlib.sha256(READER.read_bytes()).hexdigest()
record['physicsSandbox']['integration']={'section':'s4b','host':'er01-physics-sandbox','mode':'inline template and open shadow root; exact data embedded; no iframe, network or local server'}
record['physicsSandbox']['standalonePage']='sandbox/'
source_map.write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n')
journal=SITE/'journal/2026-11-01-er-01-edge-of-reality.md'
if '## Complete sandbox embedded in the reader' not in journal.read_text():
    with journal.open('a') as f:
        f.write('\n\n## Complete sandbox embedded in the reader\n\nSection 04B now contains the complete measurement sandbox and state-interface graph, with its own inline exact Lean export. An open shadow root scopes its existing styles and controls; no iframe, API call, local server or external runtime is required. Bilingual explanatory text gives the instrument, state/edge semantics, checked properties and physical limits. Panel controls retain their Russian labels, explicitly stated in both introductions. The standalone page remains a full-screen option. The original 24-theorem trace reader remains functional and isolated. Reader version 0.4.\n')
print(json.dumps({'readerBytes':len(READER.read_bytes()),'sandboxScripts':len(scripts),'dataBlocks':len(data),'section':'s4b'}))
