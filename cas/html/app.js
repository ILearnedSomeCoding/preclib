(() => {
  const history = document.getElementById("history");
  const emptyState = document.getElementById("emptyState");
  const form = document.getElementById("calculatorForm");
  const input = document.getElementById("expressionInput");
  const runButton = document.getElementById("runButton");
  const helpButton = document.getElementById("helpButton");
  const clearButton = document.getElementById("clearButton");
  const collectButton = document.getElementById("collectButton");
  const precisionInput = document.getElementById("precisionInput");
  const engineStatus = document.getElementById("engineStatus");
  const nodeStatus = document.getElementById("nodeStatus");

  let worker = null;
  let ready = false;
  let running = false;
  let requestId = 0;
  let pending = new Map();
  let commandHistory = [];
  let historyIndex = 0;

  const resizeInput = () => {
    input.style.height = "0";
    input.style.height = `${Math.min(input.scrollHeight, 160)}px`;
  };

  const setStatus = (text, kind = "") => {
    engineStatus.textContent = text;
    engineStatus.className = `status${kind ? ` ${kind}` : ""}`;
  };

  const updateRunButton = () => {
    runButton.disabled = !ready;
    runButton.textContent = running ? "停止" : "计算";
    runButton.classList.toggle("stop", running);
  };

  const appendEntry = (expression, result, elapsed) => {
    emptyState.hidden = true;
    const entry = document.createElement("article");
    entry.className = "entry";
    const expressionNode = document.createElement("div");
    expressionNode.className = "entry-expression";
    expressionNode.textContent = expression;
    const resultNode = document.createElement("div");
    resultNode.className = `entry-result${result.startsWith("error:") ? " error" : ""}`;
    resultNode.textContent = result;
    const timeNode = document.createElement("div");
    timeNode.className = "entry-time";
    timeNode.textContent = `${elapsed.toFixed(3)} ms`;
    entry.append(expressionNode, resultNode, timeNode);
    history.appendChild(entry);
    history.scrollTop = history.scrollHeight;
  };

  const callWorker = (method, ...args) => new Promise((resolve, reject) => {
    const id = ++requestId;
    pending.set(id, {resolve, reject});
    worker.postMessage({id, method, args});
  });

  const startWorker = () => {
    ready = false;
    setStatus("正在加载", "loading");
    updateRunButton();
    let workerUrl = "worker.js?v=20260815-8";
    let blobWorkerUrl = false;
    if(window.CAS_WORKER_BASE64 || window.CAS_WORKER_SOURCE){
      let workerPayload = window.CAS_WORKER_SOURCE;
      if(window.CAS_WORKER_BASE64){
        const binary = atob(window.CAS_WORKER_BASE64);
        workerPayload = new Uint8Array(binary.length);
        for(let i = 0; i < binary.length; ++i)
          workerPayload[i] = binary.charCodeAt(i);
      }
      if(!workerPayload){
        setStatus("引擎文件缺失", "error");
        return;
      }
      workerUrl = URL.createObjectURL(new Blob(
        [workerPayload], {type: "text/javascript"}));
      blobWorkerUrl = true;
    }else if(location.protocol === "file:"){
      setStatus("引擎文件缺失", "error");
      return;
    }
    const loadingWorker = new Worker(workerUrl);
    worker = loadingWorker;
    const loadTimeout = setTimeout(() => {
      if(worker === loadingWorker && !ready){
        setStatus("加载超时", "error");
        updateRunButton();
      }
    }, 15000);
    worker.onmessage = event => {
      const message = event.data;
      if(message.type === "ready"){
        clearTimeout(loadTimeout);
        if(blobWorkerUrl) URL.revokeObjectURL(workerUrl);
        const bits = Math.max(1, Math.min(1048576,
          Number(precisionInput.value) || message.precision));
        callWorker("setPrecision", bits).then(() => {
          ready = true;
          precisionInput.value = String(bits);
          nodeStatus.textContent = `${message.nodes} nodes`;
          setStatus("Wasm 就绪");
          updateRunButton();
          input.focus();
        });
        return;
      }
      if(message.type === "fatal"){
        clearTimeout(loadTimeout);
        setStatus("加载失败", "error");
        appendEntry("engine", `error: ${message.error}`, 0);
        return;
      }
      const request = pending.get(message.id);
      if(!request) return;
      pending.delete(message.id);
      if(message.error) request.reject(new Error(message.error));
      else request.resolve(message.result);
    };
    worker.onerror = event => {
      clearTimeout(loadTimeout);
      if(blobWorkerUrl) URL.revokeObjectURL(workerUrl);
      setStatus(`Worker 错误${event.message ? `: ${event.message}` : ""}`, "error");
      for(const request of pending.values()) request.reject(new Error(event.message));
      pending.clear();
    };
  };

  const stopCalculation = () => {
    if(!running) return;
    worker.terminate();
    for(const request of pending.values()) request.reject(new Error("calculation stopped"));
    pending.clear();
    running = false;
    ready = false;
    setStatus("正在重启", "loading");
    updateRunButton();
    startWorker();
  };

  const evaluate = async () => {
    if(!ready || running) return;
    const expression = input.value.trim();
    if(!expression) return;
    commandHistory.push(expression);
    historyIndex = commandHistory.length;
    input.value = "";
    resizeInput();
    running = true;
    setStatus("计算中", "loading");
    updateRunButton();
    const start = performance.now();
    try{
      const result = await callWorker("evaluate", expression);
      appendEntry(expression, result, performance.now() - start);
      nodeStatus.textContent = `${await callWorker("nodeCount")} nodes`;
    }catch(error){
      if(error.message !== "calculation stopped")
        appendEntry(expression, `error: ${error.message}`, performance.now() - start);
    }finally{
      if(running){
        running = false;
        setStatus("Wasm 就绪");
        updateRunButton();
        input.focus();
      }
    }
  };

  input.addEventListener("input", resizeInput);
  input.addEventListener("keydown", event => {
    if(event.key === "Enter" && !event.shiftKey){
      event.preventDefault();
      evaluate();
    }else if(event.key === "ArrowUp" && !input.value.includes("\n")){
      if(historyIndex > 0){
        input.value = commandHistory[--historyIndex];
        resizeInput();
        event.preventDefault();
      }
    }else if(event.key === "ArrowDown" && !input.value.includes("\n")){
      if(historyIndex < commandHistory.length){
        historyIndex += 1;
        input.value = historyIndex === commandHistory.length ? "" : commandHistory[historyIndex];
        resizeInput();
        event.preventDefault();
      }
    }
  });
  form.addEventListener("submit", event => {
    event.preventDefault();
    if(running) stopCalculation(); else evaluate();
  });
  helpButton.addEventListener("click", () => {
    if(!ready || running) return;
    input.value = "!help";
    resizeInput();
    evaluate();
  });
  precisionInput.addEventListener("change", async () => {
    if(!ready || running) return;
    const bits = Math.max(1, Math.min(1048576, Number(precisionInput.value) || 256));
    precisionInput.value = String(bits);
    await callWorker("setPrecision", bits);
  });
  collectButton.addEventListener("click", async () => {
    if(!ready || running) return;
    await callWorker("collect");
    nodeStatus.textContent = `${await callWorker("nodeCount")} nodes`;
  });
  clearButton.addEventListener("click", async () => {
    history.querySelectorAll(".entry").forEach(node => node.remove());
    emptyState.hidden = false;
    commandHistory = [];
    historyIndex = 0;
    if(ready && !running){
      await callWorker("reset");
      await callWorker("setPrecision", Number(precisionInput.value));
      nodeStatus.textContent = "0 nodes";
    }
    input.focus();
  });

  startWorker();
})();
