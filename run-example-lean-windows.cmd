@echo off
setlocal EnableExtensions
pushd "%~dp0"

if not exist "win-binary\symexec.exe" (
  echo [ERROR] win-binary\symexec.exe was not found.
  goto :missing_binary
)
if not exist "win-binary\StrategyCheck.exe" (
  echo [ERROR] win-binary\StrategyCheck.exe was not found.
  goto :missing_binary
)

set "LEAN_OUT=Lean\examples\SimpleC\EE\QCP_demos_LLM\generated"
set "LEAN_LOGIC=SimpleC.EE.QCP_demos_LLM.generated"
set "QCP_DEMOS_LLM_COMMON=-IQCP_examples/QCP_demos_LLM/ -slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM"

if not exist "%LEAN_OUT%" mkdir "%LEAN_OUT%"

for %%C in (
  poly_sll
  sll
  sll_insert_sort
  functional_queue
  dll_queue
  sll_queue
  simple_arith/abs
  simple_arith/add
  simple_arith/max3
  simple_arith/gcd
  simple_arith/Always_pos
  simple_arith/div_test
  simple_arith/exgcd
  simple_arith/delta
  simple_arith/test_prime
  sum
  bst_insert
  bst_insert_rec
  bst_fp_insert
  bst_fp_delete
  swap
  bst_delete_rec
  bst_delete_rec2
  avl_insert
  sll_auto
  dll_auto
  array_auto
  chars
  bubble_sort
  array_cases
) do win-binary\symexec.exe --no-coq-gen --lean-output-dir="%LEAN_OUT%" --lean-logic-path=%LEAN_LOGIC% %QCP_DEMOS_LLM_COMMON% --input-file=QCP_examples/QCP_demos_LLM/%%C.c --no-exec-info || goto :error

for %%S in (
  common
  dll_queue
  bst
) do win-binary\StrategyCheck.exe --no-coq-gen --lean-output-dir="%LEAN_OUT%" --lean-logic-path=%LEAN_LOGIC% %QCP_DEMOS_LLM_COMMON% --input-file=QCP_examples/QCP_demos_LLM/%%S.strategies --no-exec-info || goto :error

echo QCP_demos_LLM Lean files generated in %LEAN_OUT%.
popd
exit /b 0

:missing_binary
set "exit_code=2"
goto :report_error

:error
set "exit_code=%errorlevel%"
if "%exit_code%"=="0" set "exit_code=1"

:report_error
echo [ERROR] QCP_demos_LLM Lean generation stopped with exit code %exit_code%.
popd
exit /b %exit_code%
