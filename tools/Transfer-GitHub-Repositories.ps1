[CmdletBinding(SupportsShouldProcess, ConfirmImpact = 'High')]
param(
    [string]$SourceOwner,

    [string]$TargetOwner,

    [string]$GitHubHost = 'github.com',

    [switch]$Execute,

    [string]$AuditPath
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

function Invoke-GitHubCli {
    param(
        [Parameter(Mandatory = $true)]
        [string[]]$Arguments,

        [string]$GitHubCli = 'gh'
    )

    $global:LASTEXITCODE = 0
    $commandOutput = & $GitHubCli @Arguments 2>&1

    if ($LASTEXITCODE -ne 0) {
        $details = ($commandOutput | Out-String).Trim()
        throw "GitHub CLI falhou (codigo $LASTEXITCODE): $details"
    }

    return ($commandOutput | Out-String).Trim()
}

function Get-GitHubOwnedRepositoryNames {
    param(
        [Parameter(Mandatory = $true)]
        [string]$SourceOwner,

        [string]$GitHubHost = 'github.com'
    )

    # gh api --paginate/--slurp busca todas as paginas sem depender do limite padrao da API.
    # Fonte: https://cli.github.com/manual/gh_api
    $rawPages = Invoke-GitHubCli -Arguments @(
        'api', '--hostname', $GitHubHost, '--paginate', '--slurp',
        "users/$SourceOwner/repos?type=owner&per_page=100"
    )

    try {
        $pages = $rawPages | ConvertFrom-Json
    }
    catch {
        throw "A lista de repositorios recebida do GitHub nao e JSON valido: $($_.Exception.Message)"
    }

    $repositoryNames = foreach ($page in @($pages)) {
        foreach ($repository in @($page)) {
            if ($null -ne $repository.name -and -not [string]::IsNullOrWhiteSpace([string]$repository.name)) {
                [string]$repository.name
            }
        }
    }

    return @($repositoryNames | Sort-Object -Unique)
}

function Invoke-GitHubRepositoryTransfer {
    param(
        [Parameter(Mandatory = $true)]
        [string]$SourceOwner,

        [Parameter(Mandatory = $true)]
        [string]$RepositoryName,

        [Parameter(Mandatory = $true)]
        [string]$TargetOwner,

        [string]$GitHubHost = 'github.com'
    )

    # POST /repos/{owner}/{repo}/transfer exige new_owner e responde 202 quando aceito.
    # Fonte: https://docs.github.com/en/rest/repos/repos#transfer-a-repository
    Invoke-GitHubCli -Arguments @(
        'api', '--hostname', $GitHubHost, '--method', 'POST',
        "repos/$SourceOwner/$RepositoryName/transfer",
        "new_owner=$TargetOwner"
    ) | Out-Null
}

function Test-GitHubOwnerName {
    param([string]$OwnerName)

    return $OwnerName -match '^[A-Za-z0-9](?:[A-Za-z0-9-]{0,37}[A-Za-z0-9])?$'
}

function Assert-MigrationArguments {
    param(
        [string]$SourceOwner,
        [string]$TargetOwner
    )

    if (-not (Test-GitHubOwnerName -OwnerName $SourceOwner)) {
        throw "Conta de origem invalida: '$SourceOwner'. Informe somente o login do GitHub."
    }

    if (-not (Test-GitHubOwnerName -OwnerName $TargetOwner)) {
        throw "Conta de destino invalida: '$TargetOwner'. Informe somente o login do GitHub."
    }

    if ($SourceOwner -ieq $TargetOwner) {
        throw 'A conta de origem e a conta de destino devem ser diferentes.'
    }
}

function Write-MigrationAudit {
    param(
        [Parameter(Mandatory = $true)]
        [object[]]$Entries,

        [Parameter(Mandatory = $true)]
        [string]$AuditPath
    )

    $parentDirectory = Split-Path -Parent $AuditPath
    if (-not [string]::IsNullOrWhiteSpace($parentDirectory) -and -not (Test-Path -LiteralPath $parentDirectory -PathType Container)) {
        New-Item -ItemType Directory -Path $parentDirectory -Force | Out-Null
    }

    $Entries | ConvertTo-Json -Depth 4 | Set-Content -LiteralPath $AuditPath -Encoding utf8
}

function Start-GitHubRepositoryMigration {
    param(
        [string]$SourceOwner,
        [string]$TargetOwner,
        [string]$GitHubHost,
        [bool]$Execute,
        [string]$AuditPath,
        [System.Management.Automation.PSCmdlet]$CommandContext
    )

    Assert-MigrationArguments -SourceOwner $SourceOwner -TargetOwner $TargetOwner

    if ($null -eq (Get-Command gh -ErrorAction SilentlyContinue)) {
        throw 'GitHub CLI (gh) nao foi encontrado no PATH. Instale-o e autentique a conta de origem antes de continuar.'
    }

    Invoke-GitHubCli -Arguments @('auth', 'status', '--hostname', $GitHubHost) | Out-Null
    Invoke-GitHubCli -Arguments @('api', '--hostname', $GitHubHost, "users/$TargetOwner") | Out-Null

    $repositoryNames = Get-GitHubOwnedRepositoryNames -SourceOwner $SourceOwner -GitHubHost $GitHubHost
    $auditEntries = foreach ($repositoryName in $repositoryNames) {
        $entry = [ordered]@{
            repository = "$SourceOwner/$repositoryName"
            destination = "$TargetOwner/$repositoryName"
            timestampUtc = [DateTime]::UtcNow.ToString('o')
        }

        if (-not $Execute) {
            $entry.status = 'simulado'
        }
        elseif ($CommandContext.ShouldProcess("$SourceOwner/$repositoryName", "transferir para $TargetOwner")) {
            try {
                Invoke-GitHubRepositoryTransfer -SourceOwner $SourceOwner -RepositoryName $repositoryName -TargetOwner $TargetOwner -GitHubHost $GitHubHost
                $entry.status = 'solicitado'
            }
            catch {
                $entry.status = 'falhou'
                $entry.error = $_.Exception.Message
            }
        }
        else {
            $entry.status = 'ignorado'
        }

        [pscustomobject]$entry
    }

    if (-not [string]::IsNullOrWhiteSpace($AuditPath)) {
        Write-MigrationAudit -Entries @($auditEntries) -AuditPath $AuditPath
    }

    return @($auditEntries)
}

if ($MyInvocation.InvocationName -ne '.') {
    Start-GitHubRepositoryMigration `
        -SourceOwner $SourceOwner `
        -TargetOwner $TargetOwner `
        -GitHubHost $GitHubHost `
        -Execute $Execute.IsPresent `
        -AuditPath $AuditPath `
        -CommandContext $PSCmdlet
}
