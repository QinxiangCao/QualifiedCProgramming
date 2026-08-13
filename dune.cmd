@echo off
setlocal

set "ROOT=%~dp0"
set "FAKE_ROOT=%ROOT%tools\windows\fake-ocaml"
set "FAKE_BIN=%FAKE_ROOT%\bin"
set "FAKE_STDLIB=%FAKE_ROOT%\lib\ocaml"

if not exist "%FAKE_BIN%\ocamlc.exe" (
  echo Missing fake ocamlc.exe under "%FAKE_BIN%" 1>&2
  exit /b 1
)

if not exist "%FAKE_STDLIB%\Makefile.config" (
  echo Missing fake OCaml Makefile.config under "%FAKE_STDLIB%" 1>&2
  exit /b 1
)

if defined DUNE_REAL (
  set "REAL_DUNE=%DUNE_REAL%"
) else (
  set "REAL_DUNE="
  for /f "delims=" %%I in ('where dune.exe 2^>nul') do (
    if not defined REAL_DUNE set "REAL_DUNE=%%I"
  )
)

if not defined REAL_DUNE (
  echo Cannot find dune.exe in PATH. Install Coq Platform or set DUNE_REAL. 1>&2
  exit /b 1
)

set "PATH=%FAKE_BIN%;%PATH%"
set "OCAMLLIB=%FAKE_STDLIB%"
set "CAMLLIB=%FAKE_STDLIB%"

"%REAL_DUNE%" %*
