importScripts("cas_engine.js?v=20260815-8");

let api = null;

const reply = (id, result, error) => postMessage({id, result, error});

createCasModule().then(module => {
  api = {
    evaluate: module.cwrap("cas_eval", "string", ["string"]),
    setPrecision: module.cwrap("cas_set_precision", null, ["number"]),
    getPrecision: module.cwrap("cas_get_precision", "number", []),
    nodeCount: module.cwrap("cas_node_count", "number", []),
    collect: module.cwrap("cas_collect", null, []),
    reset: module.cwrap("cas_reset", null, [])
  };
  postMessage({type: "ready", precision: api.getPrecision(), nodes: api.nodeCount()});
}).catch(error => postMessage({type: "fatal", error: String(error)}));

onmessage = event => {
  const {id, method, args = []} = event.data;
  if(!api){
    reply(id, null, "engine is not ready");
    return;
  }
  try{
    const result = api[method](...args);
    reply(id, result, null);
  }catch(error){
    reply(id, null, String(error));
  }
};
