import json
import requests
from tqdm import tqdm
from datasets import load_dataset

# Load the GSM8K dataset (train split)
dataset = load_dataset("openai/gsm8k", "main", split="train")

# Select a subset (e.g. first 10 for testing)
subset = dataset.select(range(7473))

OLLAMA_URL = "http://localhost:11434/api/generate"
MODEL_NAME = "llama3.2"  # Your Ollama model name

# Category counters
category_counts = {
    "decimal": 0,
    "percentage": 0,
    "ratios": 0,
    "unit conversion": 0,
    "probability": 0,
    "geometry": 0,
    "algebra": 0,
    "fractions": 0,
    "proportions": 0,
    "other": 0  
}

# Prompt template
def create_prompt(problem_text):
    return f"""Classify the following math problem into one of the categories: decimal, percentage, ratios, unit conversion, algebra, probability, geometry, fractions, proportions or other. Do not include any other comments or words except for the category.

Problem:
{problem_text}

Category:"""

# Send problem to Ollama
def classify_problem(problem_text):
    prompt = create_prompt(problem_text)
    try:
        response = requests.post(OLLAMA_URL, json={
            "model": MODEL_NAME,
            "prompt": prompt,
            "stream": False
        })
        response.raise_for_status()
        return response.json()["response"].strip().strip(".").lower()
    except Exception as e:
        print("Error:", e)
        return "error"

# Loop through and classify
output_file = "gsm8k_UPDATED_classified.jsonl"
with open(output_file, "w") as f_out:
    for item in tqdm(subset, desc="Classifying GSM8K problems"):
        question = item["question"]
        category = classify_problem(question)

        # Count category
        if category in category_counts:
            category_counts[category] += 1
        else:
            category_counts["other"] += 1  # For "Error" or bad output

        item["predicted_category"] = category
        f_out.write(json.dumps(item) + "\n")

# Print summary
print("\n📊 Classification Counts:")
for k, v in category_counts.items():
    print(f"{k.capitalize():<12}: {v}")

print(f"\n✅ Done! Output saved to {output_file}")
