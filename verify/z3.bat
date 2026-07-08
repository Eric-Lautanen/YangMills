@echo off
REM Z3 verifier wrapper for verify_proof tool
REM Reads SMT-LIB2 proof from stdin and checks satisfiability
REM Returns exit 0 if UNSAT (proof valid), non-zero otherwise

C:\Python314\python.exe "%~dp0z3_verify.py" %1 2>&1
exit /b %ERRORLEVEL%
