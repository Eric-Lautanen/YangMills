@echo off
REM Coq verifier wrapper for verify_proof tool
REM Reads Coq proof from stdin and verifies it
REM Usage: coq.bat < proof.v

set TMPFILE=%TEMP%\verify_coq_%RANDOM%.v

more > "%TMPFILE%" 2>nul

if not exist "%TMPFILE%" (
  if exist "%~1" copy "%~1" "%TMPFILE%" >nul
)

where coqc >nul 2>nul
if %ERRORLEVEL% NEQ 0 (
  echo Coq (coqc) is not installed. Please install Coq to use this verifier.
  del "%TMPFILE%" 2>nul
  exit /b 1
)

coqc "%TMPFILE%" 2>&1
set EXITCODE=%ERRORLEVEL%

del "%TMPFILE%" 2>nul
del "%~n1.glob" "%~n1.vo" 2>nul
exit /b %EXITCODE%
