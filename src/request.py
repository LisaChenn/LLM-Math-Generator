import os
from datasets import load_dataset
import gspread
from oauth2client.service_account import ServiceAccountCredentials

# ─── Load GSM8K ────────────────────────────────────────────────────────────────
# This pulls the 'train' split and selects the first 100 entries.
dataset = load_dataset("openai/gsm8k", "main", split="train")
subset = dataset.select(range(100))

# ─── Authenticate to Google Sheets ─────────────────────────────────────────────
# Define the OAuth scopes and load your service‑account key.
SCOPES = ["https://www.googleapis.com/auth/spreadsheets"]
CREDS_FILE = "path/to/credentials.json"   # ← replace with your JSON key path

creds = ServiceAccountCredentials.from_json_keyfile_name(CREDS_FILE, SCOPES)
gc = gspread.authorize(creds)

# Open your sheet by URL or name
SPREADSHEET_NAME = "GSM8K Problems"       # ← the name of your sheet
sh = gc.open(SPREADSHEET_NAME)
worksheet = sh.sheet1                     # first worksheet

# ─── Prepare & Push Data ───────────────────────────────────────────────────────
# We'll write a header row, then each problem & answer.
rows = [["id", "question", "answer"]]
for idx, example in enumerate(subset):
    rows.append([
        str(idx + 1),
        example["question"].strip().replace("\n", " "),
        example["answer"].strip().replace("\n", " "),
    ])

# Clear any existing content, then update in one batch
worksheet.clear()
worksheet.update(rows)
print("Successfully wrote 100 problems to your sheet!")
