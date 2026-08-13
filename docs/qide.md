# QIDE Setup

QIDE is the VS Code extension for annotated C files. It starts the
platform-specific QCP language server and lets you execute QCP incrementally
while inspecting assertion states.

Editor setup is optional for command-line builds.

## Install

Install `qide.vsix` from the repository root with `Extensions: Install from
VSIX...`, then configure `qide.lspBinPath` in `.vscode/settings.json`.

Windows:

```json
{
  "qide.lspBinPath": "D:/absolute/path/to/qcp-binary-democases/win-binary/lsp.exe",
  "qide.lspArg": ""
}
```

Linux:

```json
{
  "qide.lspBinPath": "/absolute/path/to/qcp-binary-democases/linux-binary/lsp",
  "qide.lspArg": ""
}
```

macOS Apple Silicon:

```json
{
  "qide.lspBinPath": "/absolute/path/to/qcp-binary-democases/mac-arm64-binary/lsp",
  "qide.lspArg": ""
}
```

macOS Intel:

```json
{
  "qide.lspBinPath": "/absolute/path/to/qcp-binary-democases/mac-x86-64-binary/lsp",
  "qide.lspArg": ""
}
```

Replace the example prefix with the absolute path of your checkout.
`qide.lspArg` is a string, not a JSON array; leave it empty unless you need
additional QCP options. Forward slashes are valid in VS Code JSON on Windows
and avoid JSON backslash escaping.

## Usage

1. Open an annotated C program.
2. Move the cursor to the point you want QCP to execute to.
3. Press `Alt+RightArrow`.

You can change the keyboard shortcut in VS Code settings. You can also run the
`qide.interpretToPoint` command from the command palette.
