# Container Setup

Docker/devcontainer is an optional Rocq-only environment. Use it if you already
work with containers or want an isolated Linux-based setup.

## What This Supports

- Rocq/Coq 8.20.1
- The Rocq core libraries by default
- VS Code devcontainer workflow

It does not install Lean and does not replace the native Windows/Linux/macOS
setup guides.

## Prerequisites

- Docker
- Visual Studio Code
- VS Code Dev Containers extension

## Build the Docker Image

From the repository root:

```sh
docker build --build-arg MAKE_JOBS=5 -t qcp .
```

`MAKE_JOBS=5` is a bounded parallel job count. Lower it on a memory-constrained
machine.

## Use the VS Code Devcontainer

1. Open the repository root in VS Code.
2. Run `Dev Containers: Reopen in Container` from the command palette.
3. Let VS Code build and enter the container.

The container builds the Rocq core libraries. If you also need every generated
example, run the full Rocq build inside the container after it starts.
