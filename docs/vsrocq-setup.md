# VsRocq/VsCoq Setup

Use QIDE for annotated C files. Use VsCoq, coq-lsp, or another Rocq/Coq editor
integration for generated `.v` proof files.

## Install Extension

It is recommended to install the `vscoq-2.2.3.vsix` extension from this
repository root instead of the marketplace. The extension is compatible with
Coq 8.20 and has been tested.

If you have other Coq extensions installed, disable them for this workspace
while testing VsCoq 2.2.3. The `ejgallego.coq-lsp` and `rocq-prover.vsrocq`
extensions are known to conflict with VsCoq 2.2.3.

## Configure `vscoq.path`

VS Code may find `vscoqtop` executable automatically if it is in your `PATH`.
If not, configure the absolute path to `vscoqtop` in VS Code settings:

Windows Coq Platform example:

```json
{
  "vscoq.path": "D:/Coq8.20/bin/vscoqtop.exe"
}
```

Linux/macOS opam switch example:

```json
{
  "vscoq.path": "/absolute/path/to/opam-switch/bin/vscoqtop"
}
```

Windows verification example:

```powershell
Test-Path "D:\Coq8.20\bin\vscoqtop.exe"
& "D:\Coq8.20\bin\vscoqtop.exe" --version
```

## Optional Preferences

Use the following VS Code settings block to keep proof interaction behavior
stable across different VsCoq extension versions:

```json
{
  "vscoq.path": ...,
  "vscoq.args": [],
  "vscoq.proof.mode": 0,
  "vscoq.proof.pointInterpretationMode": 1,
  "vscoq.proof.delegation": "None"
}
```
