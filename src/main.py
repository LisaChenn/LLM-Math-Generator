import json
import requests
from tqdm import tqdm
from datasets import load_dataset

# Load the GSM8K dataset (train split)
dataset = load_dataset("openai/gsm8k", "main", split="train")

# Select a subset (for testing)
subset = dataset.select(range(7473))  # change this as needed

OLLAMA_URL = "http://localhost:11434/api/generate"
MODEL_NAME = "llama3.2"  # your Ollama model name

# Prompt template
def create_prompt(problem_text):
    return f"""Convert the following math word problem into Lean 4 code. 
Use proper variable names, integer operations, and output the total as a variable or result. 
Do not include natural language explanations or any other commentary.

Problem:
{problem_text}

Lean 4 Code:
"""

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
        return response.json()["response"].strip()
    except Exception as e:
        print("Error:", e)
        return "error"

# Output only the Lean 4 code
output_file = "gms8k_To_lean4.jsonl"
with open(output_file, "w") as fout:
    for item in tqdm(subset, desc="Generating Lean 4 code"):
        question = item["question"]
        lean_code = classify_problem(question)
        
        lean_only = {
            "lean4_code": lean_code
        }

        fout.write(json.dumps(lean_only) + "\n")

print(f"✅ Done! Lean 4 code saved to {output_file}")
