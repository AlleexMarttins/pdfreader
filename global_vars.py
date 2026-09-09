from library import re

APP_VERSION = "3.0.18"
GITHUB_REPO = "AlleexMarttins/pdfreader"
MINHAS_NOTAS_LOGIN = "mvacomercio@gmail.com"
MINHAS_NOTAS_PASSWORD = "Mva@0134"
ZWEB_USERNAME = "horizonteeletronica@gmail.com"
ZWEB_PASSWORD = "Mva@2026"
ZWEB_BASE_URL = "https://zweb.com.br"
GMAIL_OAUTH_CLIENT_ID = ""
GMAIL_OAUTH_CLIENT_SECRET = ""
LAST_MVA = None
LAST_EH = None
LAST_HASH_MERGE = None
SALES_PERIOD = None 

# Armazena resultados separados por origem (MVA/EH)
results_by_source = {
    "MVA": [],
    "EH": []
}

regex_data = re.compile(r"^\s*\d{2}/\d{2}/\d{4}")
regex_negative = re.compile(r"[-−–]\s*\d")

list_results = []  # Lista para armazenar resultados de múltiplos PDFs
listFiles = []
