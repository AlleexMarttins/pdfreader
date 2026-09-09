[CmdletBinding()]
param()

$ErrorActionPreference = "Stop"
$expectedDomain = "MVA"
$expectedUser = "relatorios.wol"
$codexAppId = "OpenAI.Codex_2p2nqsd0c76g0!App"
$runKey = "HKCU:\Software\Microsoft\Windows\CurrentVersion\Run"
$runValueName = "CodexRelatoriosWOL"
$runCommand = "explorer.exe shell:AppsFolder\$codexAppId"

if ($env:USERDOMAIN -ne $expectedDomain -or $env:USERNAME -ne $expectedUser) {
    throw "Execute este inicializador somente como $expectedDomain\$expectedUser."
}

if (-not (Get-StartApps | Where-Object AppID -eq $codexAppId)) {
    throw "O aplicativo Codex não foi encontrado nesta sessão. Instale ou abra o Codex antes de registrar a inicialização."
}

New-Item -Path $runKey -Force | Out-Null
New-ItemProperty -Path $runKey -Name $runValueName -PropertyType String -Value $runCommand -Force | Out-Null

Start-Process -FilePath "explorer.exe" -ArgumentList "shell:AppsFolder\$codexAppId"
Write-Host "Inicialização do Codex registrada para $expectedDomain\$expectedUser."
