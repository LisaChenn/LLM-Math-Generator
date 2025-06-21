import json
import requests
from tqdm import tqdm
from collections import defaultdict
from datasets import load_dataset

# Load the GSM8K dataset (train split)
dataset = load_dataset("openai/gsm8k", "main", split="train")
subset = dataset.select(range(7473))  # Use full dataset

OLLAMA_URL = "http://localhost:11434/api/generate"
MODEL_NAME = "llama3.2"

# Dynamic category counter
category_counts = defaultdict(int)

# Prompt template
def create_prompt(problem_text):
    return f"""Classify the following math problem into a math category you think would best fit. Do not include any other comments or words except for the category.

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
output_file = "gsm8k_classified4.jsonl"
with open(output_file, "w") as f_out:
    for item in tqdm(subset, desc="Classifying GSM8K problems"):
        question = item["question"]
        category = classify_problem(question)

        # Track frequency of returned category
        category_counts[category] += 1

        item["predicted_category"] = category
        f_out.write(json.dumps(item) + "\n")

# Print summary
print("\n📊 Classification Counts:")
sorted_counts = sorted(category_counts.items(), key=lambda x: x[1], reverse=True)
for category, count in sorted_counts:
    print(f"{category.capitalize():<20}: {count}")

print(f"\n✅ Done! Output saved to {output_file}")
