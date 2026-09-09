[CmdletBinding()]
param(
    [string]$UserName = "RelatoriosWOL"
)

$ErrorActionPreference = "Stop"
$reportsDirectory = "C:\Users\TI\Desktop\Relatorios"

if (Get-LocalUser -Name $UserName -ErrorAction SilentlyContinue) {
    throw "A conta local '$UserName' já existe. Nenhuma alteração foi feita."
}

$accountPassword = Read-Host "Defina a senha exclusiva da conta $UserName" -AsSecureString
if ($accountPassword.Length -eq 0) {
    throw "A criação foi cancelada: a senha não pode ficar em branco."
}

New-LocalUser -Name $UserName `
    -Password $accountPassword `
    -FullName "Execução de relatórios por Wake-on-LAN" `
    -Description "Conta local padrão destinada exclusivamente ao agente de relatórios." `
    -PasswordNeverExpires | Out-Null

if (-not (Test-Path -LiteralPath $reportsDirectory)) {
    New-Item -ItemType Directory -Path $reportsDirectory -Force | Out-Null
}

$principal = "$env:COMPUTERNAME\$UserName"
& icacls $reportsDirectory /grant "${principal}:(OI)(CI)(M)" | Out-Null
if ($LASTEXITCODE -ne 0) {
    throw "Não foi possível conceder acesso de gravação à pasta dos relatórios."
}

$administratorsGroup = Get-LocalGroup -SID "S-1-5-32-544"
$administrators = Get-LocalGroupMember -Group $administratorsGroup | ForEach-Object Name
if ($administrators -contains $principal) {
    throw "A conta foi criada, mas foi encontrada no grupo de administradores. A configuração precisa ser revisada antes do uso."
}

Write-Host "Conta '$principal' criada como usuário padrão."
Write-Host "Acesso concedido: modificar '$reportsDirectory'."
Write-Host "Feche esta janela após ler a confirmação."
