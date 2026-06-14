@echo off
setlocal

cd /d "%~dp0"

python "%~dp0macro_recorder_app.py"
if errorlevel 1 (
  echo.
  echo 起動に失敗しました、E  pause
  exit /b 1
)

endlocal
