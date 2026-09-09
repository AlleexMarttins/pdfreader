$ErrorActionPreference = 'Stop'

$packageRoot = Join-Path $PSScriptRoot 'dist\RelatorioClientesAgendado\RelatorioClientesAgendado'
$executablePath = Join-Path $packageRoot 'RelatorioClientesAgendado.exe'
$processNames = @('RelatorioClientesAgendado', 'Relatorio de Clientes')

if (-not (Test-Path -LiteralPath $executablePath)) {
    throw "Executável agendado não encontrado: $executablePath"
}

if (-not (Get-Process -ErrorAction SilentlyContinue | Where-Object { $processNames -contains $_.ProcessName })) {
    Start-Process -FilePath $executablePath -WorkingDirectory $packageRoot
}
