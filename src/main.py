import json
import requests
from tqdm import tqdm
from datasets import load_dataset

# Load the GSM8K dataset (train split)
dataset = load_dataset("openai/gsm8k", "main", split="train")

# Select a subset (for testing)
# subset = dataset.select(range(7473))  # change this as needed
# subset = dataset.select(range(3))
subset = dataset.shuffle(seed=42).select(range(3))

OLLAMA_URL = "http://localhost:11434/api/generate"
MODEL_NAME = "llama3.2"  # your Ollama model name

# Prompt template
def create_prompt(problem_text):
    return f"""
You are a math genius and a great programmer

You going to convert math questions into formal lean code
For example:
This is the GMS8K problem: 

Julie is reading a 120-page book. Yesterday, she was able to read 12 pages and today, she read twice as many pages as yesterday. If she wants to read half of the remaining pages tomorrow, how many pages should she read?
This is the correct outputted Lean 4 Code

def total_pages : Nat := 120
def pages_yday : Nat := 12
def pages_today : Nat := 2 * pages_yday
def remaining_pages : Nat := 120 - (pages_yday + pages_today)

#eval remaining_pages / 2

Below is another example. 

This is the GMS8K problem: 

Betty is saving money for a new wallet which costs $100. Betty has only half of the money she needs. Her parents decided to give her $15 for that purpose, and her grandparents twice as much as her parents. How much more money does Betty need to buy the wallet?

This is the correct outputted Lean 4 Code
def wallet_cost : Nat := 100def curr_money : Nat := wallet_cost / 2def parent_money : Nat := 15def grandparent_money : Nat := 2 * parent_money

#eval wallet_cost - (curr_money + parent_money + grandparent_money)


Convert the following math word problem into Lean 4 code. 
Use proper variable names, arithmetic operations, and output the total as a variable or result.
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
output_file = "gms8k_To_lean4TEST2.jsonl"
with open(output_file, "w") as fout:
    for item in tqdm(subset, desc="Generating Lean 4 code"):
        question = item["question"]
        lean_code = classify_problem(question)
        
        lean_only = {
            "question": question,
            "lean4_code": lean_code
        }

        fout.write(json.dumps(lean_only) + "\n")

print(f"✅ Done! Lean 4 code saved to {output_file}")
