const fs = require('fs');
const path = require('path');
const vm = require('vm');
const crypto = require('crypto');

const root = __dirname;
const htmlPath = path.join(root, 'calculator_single copy.html');
const html = fs.readFileSync(htmlPath, 'utf8');

// Reuse the exporter in calculator_single copy.html so the SB3 and the download
// page always contain the exact same extension implementation.
const scripts = [...html.matchAll(/<script>([\s\S]*?)<\/script>/g)].map(match => match[1]);
const elements = new Map();
const element = id => {
  if (!elements.has(id)) elements.set(id, {
    id, style: {}, classList: {toggle() {}},
    addEventListener(type, callback) { this[type] = callback; },
    click() {}
  });
  return elements.get(id);
};
let extensionSource = '';
class CaptureBlob {
  constructor(parts) { extensionSource = String(parts[0]); }
}
const context = {
  window: {CAS_WORKER_BASE64: '', open() {}},
  document: {
    getElementById: element,
    querySelector(selector) { return element(selector); },
    createElement() { return element('generated-link'); }
  },
  Blob: CaptureBlob,
  URL: {createObjectURL() { return 'blob:captured'; }, revokeObjectURL() {}},
  setTimeout() {}
};
vm.createContext(context);
vm.runInContext(scripts[0], context);
vm.runInContext(scripts[1], context);
element('downloadExtension').click();
if (!extensionSource.includes('Scratch.extensions.register')) throw new Error('Could not capture extension source');

extensionSource = extensionSource.replace(
  'Scratch.extensions.register(new PrecCAS());',
  'const precCASEngine = new PrecCAS();\n  Scratch.extensions.register(precCASEngine);'
);
const uiCode = String.raw`
  if (!Scratch.extensions.unsandboxed) {
    throw new Error('Prec CAS UI must be loaded with “Run extension without sandbox” enabled');
  }
  class PrecCASUI {
    constructor(engine) {
      this.engine = engine;
      this.host = null;
      this.entries = [];
      this.running = false;
      this.installTimer = setInterval(() => this.install(), 250);
      this.install();
    }
    getInfo() {
      return {
        id: 'preccasui', name: 'Prec CAS UI', color1: '#174ea6',
        blocks: [
          {opcode: 'show', blockType: Scratch.BlockType.COMMAND, text: '显示 CAS 界面'},
          {opcode: 'hide', blockType: Scratch.BlockType.COMMAND, text: '隐藏 CAS 界面'},
          {opcode: 'focus', blockType: Scratch.BlockType.COMMAND, text: '聚焦输入框'}
        ]
      };
    }
    show() { if (this.host) this.host.style.display = 'flex'; }
    hide() { if (this.host) this.host.style.display = 'none'; }
    focus() { if (this.input) this.input.focus(); }
    install() {
      const renderer = Scratch.vm.renderer;
      const canvas = renderer && (renderer.canvas || (renderer._gl && renderer._gl.canvas)) ||
        document.querySelector('[class*="stage_stage"] canvas') ||
        document.querySelector('[class*="stage-wrapper"] canvas');
      if (!canvas || this.host) return;
      clearInterval(this.installTimer);
      const host = document.createElement('section');
      this.host = host;
      host.dataset.precCasUi = 'true';
      host.style.cssText = 'position:fixed;z-index:20;display:flex;flex-direction:column;background:#f4f5f7;color:#17191d;font-family:Inter,Segoe UI,Arial,sans-serif;overflow:hidden;box-sizing:border-box;';
      host.innerHTML =
        '<style>[data-prec-cas-ui] *{box-sizing:border-box}[data-prec-cas-ui] button,[data-prec-cas-ui] textarea,[data-prec-cas-ui] input{font:inherit}.pc-top{height:56px;display:flex;align-items:center;justify-content:space-between;padding:8px 16px;background:#fff;border-bottom:2px solid #2f6feb}.pc-brand{font-size:20px;font-weight:750;color:#174ea6}.pc-tools{display:flex;align-items:center;gap:7px;font-size:11px;color:#667085}.pc-tools input{width:62px;height:29px;border:1px solid #c7ced8;border-radius:4px;padding:0 5px}.pc-tools button{height:29px;border:1px solid #c7ced8;border-radius:4px;background:#fff;color:#344054;cursor:pointer}.pc-history{flex:1;min-height:0;overflow:auto;padding:12px 18px}.pc-empty{height:100%;display:flex;flex-direction:column;align-items:center;justify-content:center;color:#777d86}.pc-empty strong{font-size:19px;color:#32363c}.pc-entry{padding:9px 0;border-bottom:1px solid #d9dce1;font-family:Cascadia Mono,Consolas,monospace;font-size:12px}.pc-expr{color:#565c65}.pc-expr:before{content:\"> \";color:#2f6feb;font-weight:bold}.pc-result{margin-top:5px;padding-left:14px;white-space:pre-wrap;overflow-wrap:anywhere;color:#111318}.pc-time{padding-left:14px;margin-top:3px;color:#8a9099;font:10px Segoe UI,Arial,sans-serif}.pc-input{display:grid;grid-template-columns:auto minmax(0,1fr) auto;align-items:end;gap:9px;padding:9px 16px;background:#fff;border-top:1px solid #cfd3d9}.pc-prompt{height:34px;display:flex;align-items:center;color:#2f6feb;font-family:monospace;font-weight:bold}.pc-input textarea{height:34px;max-height:90px;resize:none;border:0;outline:0;padding:7px 0;font-family:Cascadia Mono,Consolas,monospace;background:transparent}.pc-run{height:34px;border:0;border-radius:4px;background:#216e4e;color:#fff;padding:0 14px;cursor:pointer}.pc-status:before{content:\"\";display:inline-block;width:7px;height:7px;border-radius:50%;margin-right:5px;background:#39a66d}.pc-status.busy:before{background:#2f6feb}.pc-status.error:before{background:#e05b52}</style>' +
        '<header class="pc-top"><div class="pc-brand">Prec CAS</div><div class="pc-tools"><span class="pc-status busy">正在加载</span><span class="pc-nodes">0 nodes</span><label>精度 <input class="pc-precision" type="number" min="1" max="1048576" value="256"> bits</label><button class="pc-help">?</button><button class="pc-gc">GC</button><button class="pc-clear">×</button></div></header>' +
        '<div class="pc-history"><div class="pc-empty"><strong>精确计算，从这里开始。</strong><span>Prec CAS · TurboWarp · WebAssembly</span></div></div>' +
        '<div class="pc-input"><span class="pc-prompt">&gt;</span><textarea rows="1" spellcheck="false" placeholder="输入表达式，Enter 计算，Shift+Enter 换行"></textarea><button class="pc-run">计算</button></div>';
      document.body.appendChild(host);
      const q = selector => host.querySelector(selector);
      this.input = q('textarea'); this.history = q('.pc-history'); this.empty = q('.pc-empty');
      this.status = q('.pc-status'); this.nodes = q('.pc-nodes'); this.precision = q('.pc-precision');
      const sync = () => {
        const rect = canvas.getBoundingClientRect();
        host.style.left = rect.left + 'px'; host.style.top = rect.top + 'px';
        host.style.width = rect.width + 'px'; host.style.height = rect.height + 'px';
        host.style.fontSize = Math.max(8, rect.width / 480 * 12) + 'px';
      };
      sync(); this.syncTimer = setInterval(sync, 150);
      const stopKeys = event => event.stopPropagation();
      this.input.addEventListener('keydown', event => {
        stopKeys(event);
        if (event.key === 'Enter' && !event.shiftKey) { event.preventDefault(); this.evaluate(); }
      });
      this.input.addEventListener('keyup', stopKeys);
      this.input.addEventListener('keypress', stopKeys);
      q('.pc-run').addEventListener('click', () => this.evaluate());
      q('.pc-help').addEventListener('click', () => { this.input.value = '!help'; this.evaluate(); });
      q('.pc-gc').addEventListener('click', async () => { await this.engine.collect(); await this.updateNodes(); });
      q('.pc-clear').addEventListener('click', async () => {
        this.entries.length = 0; this.history.querySelectorAll('.pc-entry').forEach(node => node.remove());
        this.empty.hidden = false; await this.engine.reset(); await this.engine.setPrecision({BITS: this.precision.value}); await this.updateNodes();
      });
      this.precision.addEventListener('change', () => this.engine.setPrecision({BITS: this.precision.value}));
      this.engine.ready.then(() => { this.setStatus('Wasm 就绪'); this.input.focus(); }, error => this.setStatus(String(error), 'error'));
      Scratch.vm.runtime.on('PROJECT_STOP_ALL', () => this.show());
    }
    setStatus(text, kind = '') { this.status.textContent = text; this.status.className = 'pc-status' + (kind ? ' ' + kind : ''); }
    async updateNodes() { this.nodes.textContent = (await this.engine.nodeCount()) + ' nodes'; }
    append(expression, result, elapsed) {
      this.empty.hidden = true;
      const item = document.createElement('article'); item.className = 'pc-entry';
      const expressionNode = document.createElement('div'); expressionNode.className = 'pc-expr'; expressionNode.textContent = expression;
      const resultNode = document.createElement('div'); resultNode.className = 'pc-result'; resultNode.textContent = result;
      const timeNode = document.createElement('div'); timeNode.className = 'pc-time'; timeNode.textContent = elapsed.toFixed(3) + ' ms';
      item.append(expressionNode, resultNode, timeNode); this.history.appendChild(item); this.history.scrollTop = this.history.scrollHeight;
    }
    async evaluate() {
      if (this.running) return;
      const expression = this.input.value.trim(); if (!expression) return;
      this.input.value = ''; this.running = true; this.setStatus('计算中', 'busy');
      const start = performance.now();
      try { const result = await this.engine.evaluate({EXPRESSION: expression}); this.append(expression, result, performance.now() - start); await this.updateNodes(); this.setStatus('Wasm 就绪'); }
      catch (error) { this.append(expression, 'error: ' + error.message, performance.now() - start); this.setStatus('计算失败', 'error'); }
      finally { this.running = false; this.input.focus(); }
    }
  }
  const precCASUI = new PrecCASUI(precCASEngine);
  Scratch.extensions.register(precCASUI);
`;
extensionSource = extensionSource.replace(/\n\}\)\(Scratch\);\s*$/, `${uiCode}\n})(Scratch);\n`);
fs.writeFileSync(path.join(root, 'prec-cas-ui-extension.js'), extensionSource);
const userscriptSource = `/* TurboWarp Desktop startup loader for Prec CAS */
(() => {
  'use strict';
  const extensionURL = ${JSON.stringify(`data:text/javascript;base64,${Buffer.from(extensionSource).toString('base64')}`)};
  const load = async () => {
    if (!window.vm || !window.vm.extensionManager || !window.vm.runtime) {
      setTimeout(load, 100);
      return;
    }
    const manager = window.vm.extensionManager;
    if (manager.isExtensionLoaded('preccas')) return;
    const security = manager.securityManager;
    const originalGetSandboxMode = security.getSandboxMode;
    try {
      security.getSandboxMode = async () => 'unsandboxed';
      await manager.loadExtensionURL(extensionURL);
    } catch (error) {
      console.error('Prec CAS startup extension failed:', error);
    } finally {
      security.getSandboxMode = originalGetSandboxMode;
    }
  };
  load();
})();
`;
fs.writeFileSync(path.join(root, 'userscript.js'), userscriptSource);
let serial = 0;
const id = prefix => `${prefix}_${++serial}`;
const blocks = {};
const variable = (variableId, name) => [12, name, variableId];
const text = value => [10, String(value)];
const number = value => [4, String(value)];
const input = shadow => [1, shadow];
const reporterInput = (blockId, shadow = text('')) => [3, blockId, shadow];

function block(opcode, {next = null, parent = null, inputs = {}, fields = {}, topLevel = false, x = 0, y = 0, shadow = false} = {}) {
  const blockId = id('b');
  blocks[blockId] = {opcode, next, parent, inputs, fields, shadow, topLevel};
  if (topLevel) Object.assign(blocks[blockId], {x, y});
  return blockId;
}
function chain(ids) {
  ids.forEach((blockId, index) => {
    blocks[blockId].parent = index ? ids[index - 1] : blocks[blockId].parent;
    blocks[blockId].next = ids[index + 1] || null;
  });
}

const vars = {
  expression: 'var_expression', result: 'var_result', precision: 'var_precision',
  status: 'var_status', nodes: 'var_nodes'
};
const listId = 'list_history';
const vfield = (name, variableId) => ({VARIABLE: [name, variableId]});

// Green flag initialization.
const flag = block('event_whenflagclicked', {topLevel: true, x: 30, y: 30});
const statusLoading = block('data_setvariableto', {fields: vfield('状态', vars.status), inputs: {VALUE: input(text('正在加载'))}});
const reset = block('preccas_reset');
const setPrecision = block('preccas_setPrecision', {inputs: {BITS: input(variable(vars.precision, '精度'))}});
const nodeReporter = block('preccas_nodeCount');
const setNodes = block('data_setvariableto', {fields: vfield('节点', vars.nodes), inputs: {VALUE: reporterInput(nodeReporter, number(0))}});
blocks[nodeReporter].parent = setNodes;
const statusReady = block('data_setvariableto', {fields: vfield('状态', vars.status), inputs: {VALUE: input(text('Wasm 就绪'))}});
chain([flag, statusLoading, reset, setPrecision, setNodes, statusReady]);

function clickScript(x, body) {
  const hat = block('event_whenthisspriteclicked', {topLevel: true, x, y: 30});
  chain([hat, ...body]);
  return hat;
}

// Calculator sprite script.
const ask = block('sensing_askandwait', {inputs: {QUESTION: input(text('输入 CAS 表达式'))}});
const answerReporter = block('sensing_answer');
const saveExpression = block('data_setvariableto', {fields: vfield('表达式', vars.expression), inputs: {VALUE: reporterInput(answerReporter)}});
blocks[answerReporter].parent = saveExpression;
const calculating = block('data_setvariableto', {fields: vfield('状态', vars.status), inputs: {VALUE: input(text('计算中'))}});
const evalReporter = block('preccas_evaluate', {inputs: {EXPRESSION: input(variable(vars.expression, '表达式'))}});
const saveResult = block('data_setvariableto', {fields: vfield('结果', vars.result), inputs: {VALUE: reporterInput(evalReporter)}});
blocks[evalReporter].parent = saveResult;
const addExpr = block('data_addtolist', {fields: {LIST: ['历史', listId]}, inputs: {ITEM: input(variable(vars.expression, '表达式'))}});
const addResult = block('data_addtolist', {fields: {LIST: ['历史', listId]}, inputs: {ITEM: input(variable(vars.result, '结果'))}});
const nodesAfter = block('preccas_nodeCount');
const refreshNodes = block('data_setvariableto', {fields: vfield('节点', vars.nodes), inputs: {VALUE: reporterInput(nodesAfter, number(0))}});
blocks[nodesAfter].parent = refreshNodes;
const readyAfter = block('data_setvariableto', {fields: vfield('状态', vars.status), inputs: {VALUE: input(text('Wasm 就绪'))}});
clickScript(30, [ask, saveExpression, calculating, saveResult, addExpr, addResult, refreshNodes, readyAfter]);

// Help sprite.
const helpEval = block('preccas_evaluate', {inputs: {EXPRESSION: input(text('!help'))}});
const helpResult = block('data_setvariableto', {fields: vfield('结果', vars.result), inputs: {VALUE: reporterInput(helpEval)}});
blocks[helpEval].parent = helpResult;
clickScript(250, [helpResult]);

// Precision sprite.
const askPrecision = block('sensing_askandwait', {inputs: {QUESTION: input(text('输入精度（bits）'))}});
const precisionAnswer = block('sensing_answer');
const savePrecision = block('data_setvariableto', {fields: vfield('精度', vars.precision), inputs: {VALUE: reporterInput(precisionAnswer, number(256))}});
blocks[precisionAnswer].parent = savePrecision;
const applyPrecision = block('preccas_setPrecision', {inputs: {BITS: input(variable(vars.precision, '精度'))}});
clickScript(450, [askPrecision, savePrecision, applyPrecision]);

// GC sprite.
const collect = block('preccas_collect');
const gcNodesReporter = block('preccas_nodeCount');
const gcNodes = block('data_setvariableto', {fields: vfield('节点', vars.nodes), inputs: {VALUE: reporterInput(gcNodesReporter, number(0))}});
blocks[gcNodesReporter].parent = gcNodes;
clickScript(650, [collect, gcNodes]);

// Clear sprite.
const clearList = block('data_deletealloflist', {fields: {LIST: ['历史', listId]}});
const clearResult = block('data_setvariableto', {fields: vfield('结果', vars.result), inputs: {VALUE: input(text(''))}});
const clearExpression = block('data_setvariableto', {fields: vfield('表达式', vars.expression), inputs: {VALUE: input(text(''))}});
const casReset = block('preccas_reset');
const restorePrecision = block('preccas_setPrecision', {inputs: {BITS: input(variable(vars.precision, '精度'))}});
const zeroNodes = block('data_setvariableto', {fields: vfield('节点', vars.nodes), inputs: {VALUE: input(number(0))}});
clickScript(850, [clearList, clearResult, clearExpression, casReset, restorePrecision, zeroNodes]);

function svgAsset(name, svg) {
  const data = Buffer.from(svg);
  const md5 = crypto.createHash('md5').update(data).digest('hex');
  fs.writeFileSync(path.join(buildDir, `${md5}.svg`), data);
  return {assetId: md5, name, md5ext: `${md5}.svg`, dataFormat: 'svg', rotationCenterX: 60, rotationCenterY: 22};
}
function buttonSVG(label, fill, width = 120) {
  return `<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="44" viewBox="0 0 ${width} 44"><rect width="${width}" height="44" rx="7" fill="${fill}"/><text x="${width / 2}" y="28" text-anchor="middle" font-family="Arial,sans-serif" font-size="16" font-weight="700" fill="white">${label}</text></svg>`;
}

const buildDir = path.join(root, '.turbowarp-cas-build');
fs.mkdirSync(buildDir, {recursive: true});
const backdropSvg = `<svg xmlns="http://www.w3.org/2000/svg" width="480" height="360"><rect width="480" height="360" fill="#f4f5f7"/><rect width="480" height="56" fill="white"/><rect y="54" width="480" height="2" fill="#2f6feb"/><text x="18" y="35" font-family="Arial,sans-serif" font-size="22" font-weight="700" fill="#174ea6">Prec CAS</text><text x="18" y="88" font-family="Arial,sans-serif" font-size="13" fill="#667085">点击下方按钮输入表达式或管理引擎</text><rect x="16" y="102" width="448" height="180" rx="7" fill="white" stroke="#d9dce1"/><text x="30" y="130" font-family="monospace" font-size="14" fill="#2f6feb">&gt; 表达式 / 结果</text><text x="18" y="344" font-family="Arial,sans-serif" font-size="11" fill="#8a9099">Prec CAS · TurboWarp · WebAssembly</text></svg>`;
const backdropData = Buffer.from(backdropSvg);
const backdropMd5 = crypto.createHash('md5').update(backdropData).digest('hex');
fs.writeFileSync(path.join(buildDir, `${backdropMd5}.svg`), backdropData);

const sprite = (name, x, costume, spriteBlocks = {}) => ({
  isStage: false, name, variables: {}, lists: {}, broadcasts: {}, blocks: spriteBlocks,
  comments: {}, currentCostume: 0, costumes: [costume], sounds: [], volume: 100,
  layerOrder: 1, visible: true, x, y: -140, size: 70, direction: 90,
  draggable: false, rotationStyle: "don't rotate"
});

// Move each top-level click script from the shared map to its corresponding sprite.
const clickHats = Object.entries(blocks).filter(([, value]) => value.opcode === 'event_whenthisspriteclicked').map(([key]) => key);
function takeScript(hatId) {
  const selected = {};
  let current = hatId;
  while (current) {
    selected[current] = blocks[current];
    const children = Object.entries(blocks).filter(([, value]) => value.parent === current).map(([key]) => key);
    for (const child of children) if (!selected[child]) selected[child] = blocks[child];
    current = blocks[current].next;
  }
  // Reporter children can themselves own argument blocks.
  let changed = true;
  while (changed) {
    changed = false;
    for (const [key, value] of Object.entries(blocks)) {
      if (value.parent && selected[value.parent] && !selected[key]) { selected[key] = value; changed = true; }
    }
  }
  for (const key of Object.keys(selected)) delete blocks[key];
  return selected;
}

const costumes = [
  svgAsset('计算', buttonSVG('计算', '#216e4e', 130)),
  svgAsset('帮助', buttonSVG('帮助', '#2f6feb')),
  svgAsset('精度', buttonSVG('设置精度', '#7a5af8')),
  svgAsset('GC', buttonSVG('GC', '#667085')),
  svgAsset('清空', buttonSVG('清空', '#b42318'))
];
const sprites = [
  sprite('计算', -172, costumes[0], takeScript(clickHats[0])),
  sprite('帮助', -86, costumes[1], takeScript(clickHats[1])),
  sprite('精度', 0, costumes[2], takeScript(clickHats[2])),
  sprite('GC', 86, costumes[3], takeScript(clickHats[3])),
  sprite('清空', 172, costumes[4], takeScript(clickHats[4]))
];

const project = {
  targets: [{
    isStage: true, name: 'Stage',
    variables: {
      [vars.expression]: ['表达式', ''], [vars.result]: ['结果', ''],
      [vars.precision]: ['精度', 256], [vars.status]: ['状态', '未加载'], [vars.nodes]: ['节点', 0]
    },
    lists: {[listId]: ['历史', []]}, broadcasts: {}, blocks, comments: {}, currentCostume: 0,
    costumes: [{assetId: backdropMd5, name: 'Prec CAS', md5ext: `${backdropMd5}.svg`, dataFormat: 'svg', rotationCenterX: 240, rotationCenterY: 180}],
    sounds: [], volume: 100, layerOrder: 0, tempo: 60, videoTransparency: 50,
    videoState: 'on', textToSpeechLanguage: null
  }, ...sprites],
  monitors: [],
  extensions: ['preccas', 'preccasui'],
  // The extension is intentionally loaded from a local file before this SB3.
  // Omitting URLs avoids requiring a localhost HTTP server.
  extensionURLs: {},
  meta: {semver: '3.0.0', vm: '11.1.0', agent: 'Prec CAS TurboWarp builder'}
};
// In the serverless workflow userscript.js registers the unsandboxed extension
// when TurboWarp Desktop starts, before the SB3 is opened. This lets the SB3
// retain the extension IDs without losing custom blocks during deserialization.
// The extension owns the UI and CAS lifecycle, so the project only needs a stage.
project.targets = [project.targets[0]];
project.targets[0].blocks = {};
project.targets[0].variables = {};
project.targets[0].lists = {};
project.extensions = ['preccas', 'preccasui'];
project.extensionURLs = {};
fs.writeFileSync(path.join(buildDir, 'project.json'), JSON.stringify(project));
console.log(buildDir);
