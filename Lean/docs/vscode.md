# VS Code 使用说明

## 第一次打开

1. 用 VS Code 打开仓库根目录 `annotated_simplec_lean`，不要只打开某个子包目录。
2. VS Code 右下角或 Extensions 面板会提示推荐扩展，安装 `Lean 4` 和 `PowerShell`。
3. 如果 Lean 扩展没有立刻识别工具链，重启 VS Code 或执行 `Developer: Reload Window`。

## 构建整个仓库

按 `Ctrl+Shift+B`，选择或直接运行默认任务：

```powershell
Lean: Build workspace
```

该任务会调用：

```powershell
.\scripts\build.ps1 -Task build
```

## 常用任务

在 Command Palette 中执行 `Tasks: Run Task` 后可以选择：

- `Lean: Build workspace`
- `Lean: Clean workspace`
- `Lean: Setup Windows`
- `Lean: Setup Windows fallback`

## Lean 文件查看

打开任意 `.lean` 文件后，Lean 4 扩展会显示当前文件的 Infoview。由于这是多 Lake 包仓库，
如果某个子包文件暂时没有正确加载，先在 VS Code 终端中运行一次根目录构建任务。

Windows PowerShell 用户应优先使用仓库根目录的 `scripts/build.ps1`，不需要安装 `make`
或切换到 WSL。
