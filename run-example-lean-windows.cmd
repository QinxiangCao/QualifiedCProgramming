@echo off
setlocal EnableExtensions
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0scripts\generate-lean.ps1" %*
exit /b %errorlevel%
