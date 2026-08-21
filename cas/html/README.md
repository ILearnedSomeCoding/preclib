# Prec CAS Web

## 构建

如果当前终端已经运行过 `emsdk_env.bat`：

```powershell
.\cas\html\build.ps1
```

否则直接传入 emsdk 安装目录：

```powershell
.\cas\html\build.ps1 -Emsdk C:\path\to\emsdk
```

构建会在本目录生成内嵌 Wasm 的 `cas_engine.js`。

## 运行

构建后可以直接双击 `index.html`。页面会从 `worker_bundle.js` 创建
Blob Worker，不需要服务器，也不会把长计算放到 UI 主线程。

也可以从项目根目录启动本地服务器：

```powershell
python -m http.server 8000
```

然后访问：

```text
http://localhost:8000/cas/html/
```
