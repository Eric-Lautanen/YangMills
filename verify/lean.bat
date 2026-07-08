@echo off
REM Lean verifier wrapper for verify_proof tool
REM Reads Lean proof from stdin and verifies it
REM Usage: lean.bat < proof.lean

setlocal
set TMPFILE=%TEMP%\verify_%RANDOM%.lean

REM Read stdin to temp file
more > "%TMPFILE%" 2>nul

REM If no stdin (empty), check if first arg is a file
if exist "%TMPFILE%" (
  if exist "%~1" (
    copy "%~1" "%TMPFILE%" >nul
  )
)

set PATH=%USERPROFILE%\.elan\bin;%PATH%

lean "%TMPFILE%" 2>&1
set EXITCODE=%ERRORLEVEL%

del "%TMPFILE%" 2>nul
exit /b %EXITCODE%
