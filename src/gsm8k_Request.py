from datasets import load_dataset
import pandas as pd

# Load the GSM8K dataset (main split)
dataset = load_dataset("openai/gsm8k", "main", split="train")

# Select the first 1000 problems
subset = dataset.select(range(7473))

# Convert to pandas DataFrame
df = pd.DataFrame(subset)

# Save to CSV file
df.to_csv("/Users/Lisa/Documents/gsm8k_first_4282.csv", index=False)

# Optionally, save as JSON
# df.to_json("gsm8k_first_1000.json", orient="records", indent=2)
