import subprocess
from openai import OpenAI
from dotenv import load_dotenv
import random
import os
from lean_runner import check_with_lean
import random
from datasets import load_dataset

gsm8k = load_dataset("openai/gsm8k", "main")
example = gsm8k['train'][0]['question']

load_dotenv()
client = OpenAI()

print("Loading Client...\n")


def getExamples(num_examples=3):
    print("Getting Examples...\n")
    dataset = load_dataset("openai/gsm8k", "main")["train"]
    samples = random.sample(list(dataset), num_examples)
    examples_text = "\n\n".join(f"Example {i+1}:\n{ex['question']}" for i, ex in enumerate(samples))
    return examples_text

def generateProblem(client, numExamplesToPull=3):
    examplesGen = getExamples(numExamplesToPull)
    print("Generating Problem...\n")

    system_prompt = (
        "You are a math word problem generator. Your goal is to create math problems "
        "that resemble the style of the GSM8K dataset. Each problem must have a unique numeric solution.\n\n"
        "Here are a few examples:\n\n"
        f"{examplesGen}\n\n"
        "Now generate a new, original problem that follows this same format. Do not include the answer or explanation."
    )

    response = client.chat.completions.create(
        model="gpt-4",
        messages=[
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": "Generate a new math problem."}
        ]
    )
    print(response.choices[0].message.content.strip())
    return response.choices[0].message.content.strip()


def convert_to_lean(client, problem_text):
    print("Converting to Lean...\n")
    response = client.chat.completions.create(
        model="gpt-4",
        messages=[
            {"role": "system", "content": (
                "You are a Lean 4 proof assistant. "
                "Translate math word problems into Lean 4 code that proves there is a unique numeric answer. "
                "Use `∃!` for uniqueness. Wrap the result in ```lean ``` code fences."
                "Do not include any explanation-- just the Lean 4 code"
            )},
            {"role": "user", "content": f"Convert this word problem to a Lean proof:\n\n{problem_text}"}
        ]
    )

    text = response.choices[0].message.content
    if "```lean" in text:
        print(response.choices[0].message.content)
        return text.split("```lean")[1].split("```")[0].strip()
    return ""

convert_to_lean(client, generateProblem(client))