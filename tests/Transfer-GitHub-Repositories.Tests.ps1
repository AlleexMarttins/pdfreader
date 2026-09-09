. "$PSScriptRoot\..\tools\Transfer-GitHub-Repositories.ps1"

Describe 'Get-GitHubOwnedRepositoryNames' {
    It 'combina todas as paginas retornadas pela API em uma lista de nomes' {
        Mock Invoke-GitHubCli {
            '[[{"name":"api"}],[{"name":"site"}]]'
        }

        $repositoryNames = Get-GitHubOwnedRepositoryNames -SourceOwner 'conta-antiga'

        $repositoryNames | Should Be @('api', 'site')
        Assert-MockCalled Invoke-GitHubCli -Times 1 -Exactly -ParameterFilter {
            $Arguments -contains '--paginate' -and
            $Arguments -contains '--slurp' -and
            $Arguments[-1] -eq 'users/conta-antiga/repos?type=owner&per_page=100'
        }
    }

    It 'interrompe quando a API nao retorna JSON valido' {
        Mock Invoke-GitHubCli { 'pagina indisponivel' }

        $caughtException = $null
        try {
            Get-GitHubOwnedRepositoryNames -SourceOwner 'conta-antiga'
        }
        catch {
            $caughtException = $_
        }

        ($null -ne $caughtException) | Should Be $true
        $caughtException.Exception.Message | Should Match 'JSON'
    }
}

Describe 'Invoke-GitHubRepositoryTransfer' {
    It 'envia a transferencia ao endpoint documentado com o novo proprietario' {
        Mock Invoke-GitHubCli {
            $script:transferArguments = $Arguments
            '{"full_name":"conta-nova/api"}'
        }

        Invoke-GitHubRepositoryTransfer -SourceOwner 'conta-antiga' -RepositoryName 'api' -TargetOwner 'conta-nova'

        $script:transferArguments[0] | Should Be 'api'
        $script:transferArguments[1] | Should Be '--hostname'
        $script:transferArguments[3] | Should Be '--method'
        $script:transferArguments[4] | Should Be 'POST'
        ($script:transferArguments -join ' ') | Should Match 'repos/conta-antiga/api/transfer'
        ($script:transferArguments -join ' ') | Should Match 'new_owner=conta-nova'
    }
}
